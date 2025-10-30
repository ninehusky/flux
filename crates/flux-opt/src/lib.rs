#![feature(rustc_private)]
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use std::collections::HashMap;

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    mir::{
        AssertKind, BasicBlockData, BinOp, Body, Local, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind, UnOp, VarDebugInfoContents,
    },
    ty::TyCtxt,
};

use crate::hint::{FluxHint, FluxPanicType};

pub mod hint;

pub type HintsPerModule = HashMap<String, Vec<FluxHint>>;

pub const ROOT_ID: &str = "<root>";

/// Gathers and prints to stderr all panic hints found in the crate.
/// See [`FluxHint`] for details on the hints collected.
pub fn gather_crate_panics(tcx: TyCtxt<'_>) -> Result<HintsPerModule, String> {
    let crate_items = tcx.hir_crate_items(());
    let mut result: HashMap<String, Vec<FluxHint>> = HashMap::new();

    // 1. Iterate through all items in the crate
    for def_id in crate_items.definitions() {
        let def_path = tcx.def_path_str(def_id);
        // 2. If the item is a function, analyze it for panics
        match tcx.def_kind(def_id) {
            DefKind::Fn | DefKind::AssocFn => {
                let module_path = def_path
                    .rsplit_once("::")
                    .map(|(module, _)| module)
                    .unwrap_or(ROOT_ID)
                    .to_string();

                let hints = get_hints_for_func(tcx, def_id);
                result.entry(module_path).or_default().extend(hints);
            }
            _ => {
                // Skip non-function items (structs, enums, etc.)
            }
        }
    }

    for module in result.keys() {
        let hints = &result[module];
        eprintln!("=== FLUX-OPT: Panics found in module '{}': {} ===", module, hints.len());
        for hint in hints {
            eprintln!(
                "- Function: {}, Panic Type: {:?}, Assertion: {}, Span: {:?}",
                hint.function, hint.panic_type, hint.assertion, hint.span
            );
        }
    }

    Ok(result)
}

fn prettify_operand_one_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    op: &Operand<'tcx>,
    block: &'tcx BasicBlockData<'tcx>,
    body: &Body<'tcx>,
) -> Result<String, String> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            let obj = prettify_local_one_block(tcx, place.local, block, body)?;

            return Ok(prettify_projections(tcx, obj, place, body)?);
        }
        Operand::Constant(c) => {
            if let Some(scalar_int) = c.const_.try_to_scalar_int() {
                return Ok(format!("{}", scalar_int));
            }
            return Err(format!("I don't know how to prettify this constant: {:?}", c));
        }
    }
}

// TODO(@ninehusky): add this as unit test
fn prettify_projections<'tcx>(
    tcx: TyCtxt<'tcx>,
    base: String,
    place: &Place<'tcx>,
    body: &Body<'tcx>,
) -> Result<String, String> {
    let mut result = base;

    for (base, proj) in place.iter_projections() {
        match proj {
            ProjectionElem::Deref => {
                // We're not doing anything if they dereference.
                // result = format!("*{}", result);
            }
            ProjectionElem::Field(field_idx, _) => {
                let base_ty = base.ty(&body.local_decls, tcx);
                match base_ty.ty.ty_adt_def() {
                    Some(adt_def) => {
                        if let Some(field_def) = adt_def.all_fields().nth(field_idx.as_usize()) {
                            let field_name = field_def.name.as_str();
                            result = format!("{}.{}", result, field_name);
                            continue;
                        }
                    }
                    None => return Err(format!("Base type is not an ADT: {:?}", base_ty)),
                };
            }
            _ => {
                return Err(format!("Unsupported projection element: {:?}", proj));
            }
        }
    }

    Ok(result)
}

/// Pretty-print the value of a local within a single basic block.
/// Stops at debug locals or function arguments.
fn prettify_local_one_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    local: Local,
    block: &'tcx BasicBlockData<'tcx>,
    body: &Body<'tcx>,
) -> Result<String, String> {
    // Check if the local is a debug variable
    if let Some(name) = debug_name_for_local(body, local) {
        return Ok(name);
    }

    let og_assignment: Option<(&'tcx Place<'tcx>, &'tcx Rvalue<'tcx>)> =
        find_assignment(block, local);
    match og_assignment {
        Some((_, rvalue)) => {
            match rvalue {
                Rvalue::BinaryOp(op, args) => {
                    let op_str = match op {
                        BinOp::Eq => "==",
                        BinOp::Lt => "<",
                        BinOp::Le => "<=",
                        _ => {
                            return Err(format!("Unsupported binary operation: {:?}", op));
                        }
                    };
                    let left = prettify_operand_one_block(tcx, &args.0, block, body)?;
                    let right = prettify_operand_one_block(tcx, &args.1, block, body)?;
                    Ok(format!("{} {} {}", left, op_str, right))
                }
                // NOTE(@ninehusky): This is suspicious.
                // I chatted with Vivien/Evan about this and this seems right?
                // Basically, there is a difference between a Rvalue::Len and a
                // UnOp::PtrMetdata called with a slice/array, even though
                // it seems that both of them do the same thing.
                // In our current implementation, we _only_ support
                // UnOp::PtrMetadata for getting lengths of slices/arrays.
                Rvalue::UnaryOp(op, arg) => {
                    let op_str = {
                        match op {
                            UnOp::PtrMetadata => {
                                // verify that the argument is a slice
                                let local_decls = &body.local_decls;
                                let arg_type = arg.ty(local_decls, tcx);
                                if arg_type.is_array_slice() || arg_type.is_slice() {
                                    "len"
                                } else {
                                    return Err("PtrMetadata applied to non-slice type".to_string());
                                }
                            }
                            _ => return Err(format!("Unsupported unary operation: {:?}", op)),
                        }
                    };
                    // The expectation is that if we are here, the op_str is "len".
                    assert_eq!(op_str, "len");
                    let inner = prettify_operand_one_block(tcx, &arg, block, body)?;
                    Ok(format!("{}.{}()", inner, op_str))
                }
                Rvalue::CopyForDeref(arg) => {
                    // We're not doing anything if they copy for deref.
                    // This would otherwise be something like `&obj`.
                    prettify_operand_one_block(tcx, &Operand::Copy(arg.clone()), block, body)
                }
                Rvalue::Ref(_, _, arg) => {
                    let base =
                        prettify_operand_one_block(tcx, &Operand::Copy(arg.clone()), block, body)?;
                    prettify_projections(tcx, base, arg, body)
                }
                Rvalue::RawPtr(_, arg) => {
                    // We're not doing anything with raw pointers.
                    prettify_operand_one_block(tcx, &Operand::Copy(arg.clone()), block, body)
                }
                Rvalue::Use(arg) => {
                    // ignore this.
                    prettify_operand_one_block(tcx, arg, block, body)
                }
                _ => return Err(format!("I don't know what to do with a {:?}!", rvalue)),
            }
        }
        None => Err(format!("No assignment found for local _{} in the given block", local.index())),
    }
}

fn find_assignment<'tcx>(
    block_data: &'tcx BasicBlockData<'tcx>,
    target: Local,
) -> Option<(&'tcx Place<'tcx>, &'tcx Rvalue<'tcx>)> {
    for statement in block_data.statements.iter().rev() {
        if let StatementKind::Assign(vals) = &statement.kind {
            let place = &vals.0;
            let rvalue = &vals.1;
            if place.local == target {
                return Some((place, rvalue));
            }
        }
    }
    None
}

fn parse_fn_name(fn_name: &str) -> &str {
    // Find the last occurrence of "::" and return the substring after it
    if let Some(pos) = fn_name.rfind("::") { &fn_name[pos + 2..] } else { fn_name }
}

fn debug_name_for_local<'tcx>(body: &Body<'tcx>, local: Local) -> Option<String> {
    for var in &body.var_debug_info {
        if let VarDebugInfoContents::Place(place) = &var.value {
            if place.local == local {
                return Some(var.name.to_string());
            }
        }
    }
    None
}

pub fn get_hints_for_func(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Vec<FluxHint> {
    let fn_name = tcx.def_path_str(def_id.to_def_id());
    println!("🔎 Starting analysis of {}", fn_name);

    if !tcx.is_mir_available(def_id.to_def_id()) {
        println!("⚠️  Skipping {}: No MIR available (likely a trait method declaration)", fn_name);
        return vec![];
    }

    let mut panics = vec![];

    for basic_block in tcx.optimized_mir(def_id.to_def_id()).basic_blocks.iter() {
        let terminator = &basic_block.terminator;
        if terminator.is_none() {
            continue;
        }
        let terminator = terminator.as_ref().unwrap();
        match &terminator.kind {
            TerminatorKind::Call { func, .. } => {
                if let Some((def_id, _)) = func.const_fn_def() {
                    let called_path = tcx.def_path_str(def_id);
                    // We handle aborts by path because they're not in lang items.
                    if is_panic_or_abort_fn(tcx, def_id)
                        || called_path == "core::intrinsics::abort"
                        || called_path == "std::process::abort"
                    {
                        let panic_type = FluxPanicType::ExplicitPanic;
                        panics.push(FluxHint {
                            function: fn_name.clone(),
                            span: terminator.source_info.span,
                            assertion: "Explicit Panic".into(),
                            panic_type,
                        });
                    }
                }
            }
            TerminatorKind::Assert { cond, msg, .. } => {
                match &**msg {
                    AssertKind::BoundsCheck { .. }
                    | AssertKind::DivisionByZero(_)
                    | AssertKind::RemainderByZero(_) => {
                        if let Operand::Copy(place) | Operand::Move(place) = cond {
                            let local = place.local;
                            let debug_msg = prettify_local_one_block(
                                tcx,
                                local,
                                basic_block,
                                &tcx.optimized_mir(def_id.to_def_id()),
                            );

                            let panic_type = match &**msg {
                                AssertKind::BoundsCheck { .. } => hint::FluxPanicType::BoundsCheck,
                                AssertKind::DivisionByZero(_) => {
                                    hint::FluxPanicType::DivisionByZero
                                }
                                AssertKind::RemainderByZero(_) => {
                                    hint::FluxPanicType::RemainderByZero
                                }
                                _ => unreachable!(),
                            };

                            if let Ok(assertion_str) = debug_msg.clone() {
                                let hint = FluxHint {
                                    span: terminator.source_info.span,
                                    assertion: assertion_str,
                                    panic_type,
                                    function: parse_fn_name(&fn_name).to_string(),
                                };
                                panics.push(hint);
                            } else {
                                eprintln!(
                                    "Couldn't resolve debug message {:?} for bounds check in function {}",
                                    debug_msg, fn_name
                                );
                            }
                        }
                    }
                    _ => (),
                };
            }
            _ => {}
        }
    }
    panics
}
