#![feature(rustc_private)]
extern crate rustc_middle;
extern crate rustc_hir;

use flux_middle::global_env::GlobalEnv;
use rustc_middle::{mir::{Statement, TerminatorKind}, ty::TyCtxt};
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LOCAL_CRATE, LocalDefId},
};
use rustc_middle::mir::pretty::write_mir_pretty;

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

fn parse_fn_name(fn_name: &str) -> &str {
    // Find the last occurrence of "::" and return the substring after it
    if let Some(pos) = fn_name.rfind("::") {
        &fn_name[pos + 2..]
    } else {
        fn_name
    }
}

pub fn entry_point(tcx: TyCtxt<'_>, def_id: LocalDefId) -> usize {
    let fn_name = tcx.def_path_str(def_id.to_def_id());
    println!("🔎 Starting analysis of {}", fn_name);

    // 🎯 FIX: Check if this definition has a body before accessing MIR
    if !tcx.is_mir_available(def_id.to_def_id()) {
        println!("⚠️  Skipping {}: No MIR available (likely a trait method declaration)", fn_name);
        return 0;
    }

    let mut panics = 0;

    for basic_block in tcx.optimized_mir(def_id.to_def_id()).basic_blocks.iter() {
        let terminator = &basic_block.terminator;
        if terminator.is_none() {
            continue;
        }
        let terminator = terminator.as_ref().unwrap();
        match &terminator.kind {
            TerminatorKind::Assert { cond, expected, msg, target, .. } => {
                // Print to stderr
                panics += 1;
                eprintln!("Inside function: {}, Found an assert saying {:?}", fn_name, msg);
            }
            _ => {}
        }
    }
    panics
}