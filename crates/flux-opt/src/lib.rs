#![feature(rustc_private)]
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use std::collections::HashMap;

use flux_middle::global_env::GlobalEnv;
use rustc_hir::{def::DefKind, def_id::LocalDefId};
use rustc_middle::{
    mir::{
        AssertKind, BasicBlockData, BinOp, Body, Local, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind, UnOp, VarDebugInfoContents,
    },
    ty::TyCtxt,
};

use crate::hint::FluxHint;

mod hint;

pub fn run_mir_analysis_on_all_functions(genv: GlobalEnv) {
    let tcx = genv.tcx();
    let crate_items = tcx.hir_crate_items(());

    let mut panics_per_module: HashMap<String, Vec<FluxHint>> = HashMap::new();

    // Iterate through all items in the crate
    for def_id in crate_items.definitions() {
        let def_path = tcx.def_path_str(def_id);
        match tcx.def_kind(def_id) {
            DefKind::Fn | DefKind::AssocFn => {
                let module_path = def_path
                    .rsplit_once("::") // split into (before, after)
                    .map(|(module, _)| module)
                    .unwrap_or("<root>")
                    .to_string();

                let hints = entry_point(tcx, def_id);
                panics_per_module
                    .entry(module_path)
                    .or_default()
                    .extend(hints);
            }
            _ => {
                // Skip non-function items (structs, enums, etc.)
            }
        }
    }

    for module in panics_per_module.keys() {
        let hints = &panics_per_module[module];
        eprintln!("=== FLUX-OPT: Panics found in module '{}': {} ===", module, hints.len());
        for hint in hints {
            eprintln!(
                "- Function: {}, Panic Type: {:?}, Assertion: {}, Span: {:?}",
                hint.function, hint.panic_type, hint.assertion, hint.span
            );
        }
    }
}

fn prettify_operand_one_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    op: &Operand<'tcx>,
    block: &BasicBlockData<'tcx>,
    body: &Body<'tcx>,
) -> String {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            let obj = prettify_local_one_block(tcx, place.local, block, body)
                .unwrap_or(format!("_{}", place.local.index()));
            // try to get fields
            let arg = place;
            eprintln!("Projection chain: {:?}", arg.projection);

            if arg.projection.is_empty() || arg.projection.len() < 2 {
                return obj;
            }

            // match on one dereference and one field access
            // For field access like `self._0`, you want the type of `self` (the base)
            if let ProjectionElem::Field(field_idx, _) = &arg.projection[1] {
                // Get the type of the place BEFORE the field projection
                let base_place = Place {
                    local: place.local,
                    projection: tcx.mk_place_elems(&place.projection[..place.projection.len() - 1]),
                };

                // This gives you the type of `self` (the parent/base type)
                let base_ty = base_place.ty(&body.local_decls, tcx).ty;

                // Now you can get the ADT definition to look up field names
                if let Some(adt_def) = base_ty.ty_adt_def() {
                    // Fixed syntax
                    if let Some(field_def) = adt_def.all_fields().nth(field_idx.as_usize()) {
                        let field_name = field_def.name.as_str();
                        return format!("{}.{}", obj, field_name);
                    }
                }

                // Fallback if we can't get the field name
                return format!("{}._{}", obj, field_idx.index());
            }

            obj
        }
        Operand::Constant(c) => {
            if let Some(scalar_int) = c.const_.try_to_scalar_int() {
                return format!("{}", scalar_int);
            }
            format!("{:?}", c)
        }
    }
}

/// Pretty-print the value of a local within a single basic block.
/// Stops at debug locals or function arguments.
fn prettify_local_one_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    local: Local,
    block: &BasicBlockData<'tcx>,
    body: &Body<'tcx>,
) -> Option<String> {
    // Check if the local is a debug variable
    if let Some(name) = debug_name_for_local(body, local) {
        return Some(name);
    }

    let og_assignment = find_assignment(block, local);
    match og_assignment {
        Some((_, rvalue)) => {
            match rvalue {
                Rvalue::BinaryOp(op, args) => {
                    let op_str = match op {
                        BinOp::Eq => "==",
                        BinOp::Lt => "<",
                        BinOp::Le => "<=",
                        _ => todo!("I have no idea how to format a {:?}", op),
                    };
                    let left = prettify_operand_one_block(tcx, &args.0, block, body);
                    let right = prettify_operand_one_block(tcx, &args.1, block, body);
                    Some(format!("({:?} {} {})", op_str, left, right))
                }
                // suspicious.
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
                                    "ptr_metadata"
                                }
                            }
                            _ => todo!(),
                        }
                    };
                    let inner = prettify_operand_one_block(tcx, &arg, block, body);
                    // Some(format!("({} {})", op_str, inner))
                    Some(inner)
                }
                Rvalue::CopyForDeref(arg) | Rvalue::Ref(_, _, arg) => {
                    let obj =
                        prettify_operand_one_block(tcx, &Operand::Copy(arg.clone()), block, body);
                    if arg
                        .projection
                        .iter()
                        .any(|elem| matches!(elem, ProjectionElem::Field(idx, val)))
                    {
                        let field = arg.projection.iter().find_map(|elem| {
                            if let ProjectionElem::Field(field_idx, _) = elem {
                                Some(field_idx)
                            } else {
                                None
                            }
                        });
                        if let Some(field_idx) = field {
                            Some(format!("{}.{:?}", obj, field_idx))
                        } else {
                            Some(obj)
                        }
                    } else {
                        Some(obj)
                    }
                }
                Rvalue::RawPtr(_, arg) => {
                    let obj =
                        prettify_operand_one_block(tcx, &Operand::Copy(arg.clone()), block, body);
                    if arg
                        .projection
                        .iter()
                        .any(|elem| matches!(elem, ProjectionElem::Field(idx, val)))
                    {
                        let field = arg.projection.iter().find_map(|elem| {
                            if let ProjectionElem::Field(field_idx, _) = elem {
                                Some(field_idx)
                            } else {
                                None
                            }
                        });
                        if let Some(field_idx) = field {
                            let format_str = match field_idx.index() {
                                0 => "ring",
                                1 => "head",
                                2 => "tail",
                                _ => "unknown_field",
                            };
                            Some(format!("{}.{}", obj, format_str))
                        } else {
                            Some(obj)
                        }
                    } else {
                        Some(obj)
                    }
                }
                Rvalue::Use(arg) => Some(prettify_operand_one_block(tcx, &arg, block, body)),
                _ => {
                    eprintln!("I don't know what to do with a {:?}!", rvalue);
                    eprintln!("Its enum type is: rvalue::{:?}", std::mem::discriminant(&rvalue));
                    None
                }
            }
        }
        None => None,
    }
}

fn find_assignment<'tcx>(
    block_data: &BasicBlockData<'tcx>,
    target: Local,
) -> Option<(Place<'tcx>, Rvalue<'tcx>)> {
    for statement in block_data.statements.iter().rev() {
        if let StatementKind::Assign(vals) = &statement.kind {
            let place = &vals.0;
            let rvalue = &vals.1;
            if place.local == target {
                return Some((place.clone(), rvalue.clone()));
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

pub fn entry_point(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Vec<FluxHint> {
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
        let source_map = tcx.sess.source_map();
        match &terminator.kind {
            TerminatorKind::Assert { cond, expected, msg, target, .. } => {
                match &**msg {
                    AssertKind::BoundsCheck { len, index } => {
                        if let Operand::Copy(place) | Operand::Move(place) = cond {
                            let local = place.local;
                            let debug_msg = prettify_local_one_block(
                                tcx,
                                local,
                                basic_block,
                                &tcx.optimized_mir(def_id.to_def_id()),
                            );

                            if let Some(assertion_str) = debug_msg.clone() {
                                let hint = FluxHint {
                                    span: terminator.source_info.span,
                                    assertion: assertion_str,
                                    panic_type: hint::FluxPanicType::BoundsCheck,
                                    function: parse_fn_name(&fn_name).to_string(),
                                };
                                panics.push(hint);
                            }
                        }
                    }
                    AssertKind::RemainderByZero(_) | AssertKind::DivisionByZero(_) => {
                        if let Operand::Copy(place) | Operand::Move(place) = cond {
                            let local = place.local;
                            let debug_msg = prettify_local_one_block(
                                tcx,
                                local,
                                basic_block,
                                &tcx.optimized_mir(def_id.to_def_id()),
                            );
                            if let Some(assertion_str) = debug_msg.clone() {
                                let hint = FluxHint {
                                    span: terminator.source_info.span,
                                    assertion: assertion_str,
                                    panic_type: if matches!(**msg, AssertKind::DivisionByZero(_)) {
                                        hint::FluxPanicType::DivisionByZero
                                    } else {
                                        hint::FluxPanicType::RemainderByZero
                                    },
                                    function: parse_fn_name(&fn_name).to_string(),
                                };
                                panics.push(hint);
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
