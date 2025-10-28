#![feature(rustc_private)]

extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

// We need this to run tests for some reason.
extern crate rustc_driver;

use core::panic;
use std::sync::atomic::AtomicBool;

use flux_middle::{fhir, global_env::GlobalEnv, queries::Providers, timings, Specs};
use flux_opt::{gather_crate_panics, hint::FluxHint};
use rustc_driver::Callbacks;
use rustc_interface::Config;
use rustc_session::config::Options;

pub struct DummyCallback {
    pub expected: Vec<FluxHint>,
}

impl Callbacks for DummyCallback {
    fn config(&mut self, _config: &mut rustc_interface::interface::Config) {
        // we're not gonna do anything.
    }

    fn after_analysis<'tcx>(
            &mut self,
            compiler: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            if compiler.sess.dcx().has_errors().is_some() {
                panic!("Compilation error!");
            }
            let res = gather_crate_panics(tcx);
            match res {
                Ok(hints) => {
                    assert_eq!(hints, self.expected);
                }
                Err(e) => {
                    panic!("Error gathering panics: {:?}", e);
                }
            }
            rustc_driver::Compilation::Stop
    }

}

// A helper function to run our Flux-Opt algorithm on a source string.
fn run_mii(src: &'static str) -> GlobalEnv {
    // 1. Create an Input from the source string.
    let input = rustc_session::config::Input::Str {
        name: rustc_span::FileName::anon_source_code(src),
        input: src.to_string(),
    };

    // 2. Define a config. I kind of just set everything to
    // "None" or the equivalent default value.
    let config = Config {
        opts: Options::default(),
        crate_cfg: Default::default(),
        crate_check_cfg: Default::default(),
        input,
        output_dir: None,
        output_file: None,
        file_loader: None,
        lint_caps: Default::default(),
        register_lints: None,
        override_queries: None,
        make_codegen_backend: None,
        registry: rustc_driver::diagnostics_registry(),
        ice_file: None,
        locale_resources: vec![],
        psess_created: None,
        hash_untracked_state: None,
        extra_symbols: vec![],
        using_internal_features: &AtomicBool::new(false),
        expanded_args: vec![], 
    };

    // 3. Run the compiler with the config.

    let mut result: Vec<FluxHint> = vec![];
    rustc_driver::run_compiler(config, |compiler| {
        if compiler.sess.dcx().has_errors().is_some() {
            panic!("Compilation error!");
        }

        compiler.enter(|tcx| {
            // 4. Create a GlobalEnv from the TyCtxt.
            let genv = GlobalEnv::new(tcx);

            // 5. Run Flux-Opt on the GlobalEnv to get hints.
            result = flux_opt::hint_generation::generate_hints(&genv);
        });
    });
}

pub mod hint_tests {
    use flux_opt::hint::{FluxHint, FluxPanicType};

    #[test]
    fn test_flux_hint_creation() {
        let hint = FluxHint {
            function: "test_function".to_string(),
            span: rustc_span::DUMMY_SP,
            assertion: "i < len".to_string(),
            panic_type: FluxPanicType::BoundsCheck,
        };
        assert_eq!(hint.function, "test_function");
        assert_eq!(hint.assertion, "i < len");
        assert_eq!(hint.panic_type, FluxPanicType::BoundsCheck);
    }

    #[test]
    fn get_mir() {
        let rust_src = r#"
        fn divide(a: i32, b: i32) -> i32 {
            a / b
        }
        "#;

        let mir = flux_opt::tests::get_mir_from_source(rust_src, "divide");
    }
}
