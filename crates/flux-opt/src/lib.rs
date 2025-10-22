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

// 🎯 NEW: Helper function to run MIR analysis on all functions
pub fn run_mir_analysis_on_all_functions(genv: GlobalEnv) {
    let tcx = genv.tcx();
    let crate_items = tcx.hir_crate_items(());
    
    // Iterate through all items in the crate
    for def_id in crate_items.definitions() {
        
        // Check if this item is a function
        match tcx.def_kind(def_id) {
            DefKind::Fn | DefKind::AssocFn => {
                println!("🔍 Analyzing function: {}", tcx.def_path_str(def_id));
                
                // Call your entry_point for this specific function
                entry_point(tcx, def_id);
            }
            _ => {
                // Skip non-function items (structs, enums, etc.)
            }
        }
    }
}

pub fn entry_point(tcx: TyCtxt<'_>, def_id: LocalDefId) {
    println!("=== FLUX-OPT: Starting MIR analysis ===");

    let fn_name = tcx.def_path_str(def_id.to_def_id());

       // 🎯 FIX: Check if this definition has a body before accessing MIR
    if !tcx.is_mir_available(def_id.to_def_id()) {
        println!("⚠️  Skipping {}: No MIR available (likely a trait method declaration)", fn_name);
        return;
    }

    for basic_block in tcx.optimized_mir(def_id.to_def_id()).basic_blocks.iter() {
        println!("Function: {}, Basic Block: {:?}", fn_name, basic_block);
        let terminator = &basic_block.terminator;
        if terminator.is_none() {
            continue;
        }
        let terminator = terminator.as_ref().unwrap();
        match &terminator.kind {
            TerminatorKind::Assert { cond, expected, msg, target, .. } => {
                // Print to stderr
                eprintln!("Inside function: {}, Found an assert saying {:?}", fn_name, msg);
            }
            _ => {}
        }
    }

    println!("=== FLUX-OPT: Finished MIR analysis ===");
}