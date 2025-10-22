#![feature(rustc_private)]
extern crate rustc_middle;
extern crate rustc_hir;

use flux_middle::global_env::GlobalEnv;
use rustc_middle::{ty::TyCtxt};
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

    // get optimized MIR (this triggers pipeline if needed)
    let mir = tcx.optimized_mir(def_id.to_def_id());
    // write pretty MIR to stdout (or a file)
    if let Err(e) = write_mir_pretty(tcx, Some(def_id.to_def_id()), &mut std::io::stdout()) {
        // fallback to debug
        eprintln!("write_mir_pretty failed: {:?}\nDumping Debug:", e);
        println!("{:#?}", &*mir);
    } else {
        let err_file = format!("mir_{}.txt", fn_name.replace("::", "_"));
        let mut file = std::fs::File::create(&err_file).expect("Could not create MIR output file");
        let absolute_path = std::fs::canonicalize(&err_file).expect("Could not get absolute path");
        write_mir_pretty(tcx, Some(def_id.to_def_id()), &mut file).unwrap();
        panic!("MIR for function '{}' written to {}", fn_name, absolute_path.display());


    }
    
    println!("=== FLUX-OPT: Finished MIR analysis ===");
}