#![feature(rustc_private)]
extern crate rustc_hir;
extern crate rustc_middle;

use flux_middle::global_env::GlobalEnv;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LOCAL_CRATE, LocalDefId},
};
use rustc_middle::{
    mir::{
        AssertKind, BasicBlock, BasicBlockData, BinOp, Body, Const, Local, Operand, Place,
        ProjectionElem, Rvalue, Statement, StatementKind, TerminatorKind, UnOp,
        VarDebugInfoContents, pretty::write_mir_pretty,
    },
    ty::TyCtxt,
};

/// These are the ring buffer functions that we actually
/// care about.
const EXPECTED_FUNCTIONS: &[&str] = &[
    "available_len",
    "as_slices",
    "has_elements",
    "is_full",
    "len",
    "enqueue",
    "push",
    "dequeue",
    "remove_first_matching",
    "empty",
    "retain",
];

// 🎯 NEW: Helper function to run MIR analysis on all functions
pub fn run_mir_analysis_on_all_functions(genv: GlobalEnv) {
    let tcx = genv.tcx();
    let crate_items = tcx.hir_crate_items(());

    let mut total_panics = 0;

    // Iterate through all items in the crate
    for def_id in crate_items.definitions() {
        // Check if this item is a function
        match tcx.def_kind(def_id) {
            DefKind::Fn | DefKind::AssocFn => {
                let def_path = tcx.def_path_str(def_id);
                let fn_name = parse_fn_name(&def_path);
                if EXPECTED_FUNCTIONS.contains(&fn_name) {
                    // Call your entry_point for this specific function
                    total_panics += entry_point(tcx, def_id);
                }
            }
            _ => {
                // Skip non-function items (structs, enums, etc.)
            }
        }
    }

    if total_panics > 0 {
        eprintln!("=== FLUX-OPT: Total panics found across all functions: {} ===", total_panics);
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
                    format!("{}.{}", obj, field_idx.index())
                } else {
                    obj
                }
            } else {
                obj
            }
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

pub fn entry_point(tcx: TyCtxt<'_>, def_id: LocalDefId) -> usize {
    let fn_name = tcx.def_path_str(def_id.to_def_id());
    println!("🔎 Starting analysis of {}", fn_name);

    // 🎯 FIX: Check if this definition has a body before accessing MIR
    if !tcx.is_mir_available(def_id.to_def_id()) {
        println!("⚠️  Skipping {}: No MIR available (likely a trait method declaration)", fn_name);
        return 0;
    }

    // print the MIR
    // eprintln!("MIR for function {}:\n", fn_name);
    // eprintln!("{:#?}", tcx.optimized_mir(def_id.to_def_id()));

    let mut panics = 0;

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
                            eprintln!("Found an assertion checking for: Bounds Check");
                            eprintln!("It lives at {:?}", terminator.source_info.span);
                            if let Ok(snippet) = source_map.span_to_snippet(terminator.source_info.span) {
                                eprintln!("Source snippet: {}", snippet);
                            } else {
                                eprintln!("(could not retrieve source snippet)");
                            }
                            eprintln!(
                                "The assert expression:\n{}\n",
                                debug_msg.unwrap_or("Could not prettify expression".to_string())
                            );
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
                            eprintln!(
                                "Found an assertion checking for: {}",
                                match &**msg {
                                    AssertKind::RemainderByZero(_) => "Remainder By Zero",
                                    AssertKind::DivisionByZero(_) => "Division By Zero",
                                    _ => "Unknown",
                                }
                            );
                            eprintln!("It lives at {:?}", terminator.source_info.span);
                            if let Ok(snippet) = source_map.span_to_snippet(terminator.source_info.span) {
                                eprintln!("Source snippet: {}", snippet);
                            } else {
                                eprintln!("(could not retrieve source snippet)");
                            }
                            eprintln!(
                                "The assert expression:\n{}\n",
                                debug_msg.unwrap_or("Could not prettify expression".to_string())
                            );
                        }
                    }
                    _ => (),
                };
                // Print to stderr
                panics += 1;
            }
            _ => {}
        }
    }
    panics
}
