#![feature(rustc_private)]

extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

// We need this to run tests for some reason.
extern crate rustc_driver;

use core::panic;
use std::io;

use flux_opt::{HintsPerModule, gather_crate_panics};
use rustc_driver::Callbacks;
use rustc_span::source_map::FileLoader;

const DUMMY_FILE_NAME: &str = "in_memory.rs";

pub struct DummyCallback {
    pub source: String,
    pub expected: HintsPerModule,
    pub care_about_spans: bool,
}

impl Callbacks for DummyCallback {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.file_loader = Some(Box::new(InMemoryFileLoader {
            name: DUMMY_FILE_NAME.to_string(),
            contents: self.source.clone(),
        }));
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
                if self.care_about_spans {
                    assert_eq!(hints, self.expected);
                } else {
                    assert_eq!(
                        hints.keys().collect::<Vec<_>>(),
                        self.expected.keys().collect::<Vec<_>>()
                    );
                    // This is kind of a "special equals" -- I don't care about spans here.
                    for (k, v) in hints.iter() {
                        assert_eq!(v.len(), self.expected.get(k).unwrap().len());
                        for (hint1, hint2) in v.iter().zip(self.expected.get(k).unwrap().iter()) {
                            assert_eq!(hint1.assertion, hint2.assertion);
                            assert_eq!(hint1.function, hint2.function);
                            assert_eq!(hint1.panic_type, hint2.panic_type);
                        }
                    }
                }
            }
            Err(e) => {
                panic!("There was a terrible error gathering panics: {:?}", e);
            }
        }
        rustc_driver::Compilation::Stop
    }
}

struct InMemoryFileLoader {
    name: String,
    contents: String,
}

impl FileLoader for InMemoryFileLoader {
    fn file_exists(&self, path: &std::path::Path) -> bool {
        path.to_string_lossy() == self.name
    }

    fn read_file(&self, path: &std::path::Path) -> io::Result<String> {
        if path.to_string_lossy() == self.name {
            Ok(self.contents.clone())
        } else {
            Err(io::Error::new(io::ErrorKind::NotFound, "no such file"))
        }
    }

    fn read_binary_file(&self, _path: &std::path::Path) -> io::Result<std::sync::Arc<[u8]>> {
        unimplemented!("I'm not doing this!");
    }
}

// A helper function to run our Flux-Opt algorithm on a source string.
fn run_mii(src: &str, expected: &HintsPerModule) {
    // 1. Create an Input from the source string.
    let mut callback = DummyCallback {
        expected: expected.clone(),
        source: src.to_string(),
        care_about_spans: false,
    };

    // Pretend the compiler is invoked with a single file argument
    let args =
        vec!["rustc".to_string(), DUMMY_FILE_NAME.to_string(), "--crate-type=bin".to_string()];

    rustc_driver::run_compiler(&args, &mut callback);
}

pub mod hint_tests {
    use flux_opt::{
        HintsPerModule, ROOT_ID,
        hint::{FluxHint, FluxPanicType},
    };

    use crate::run_mii;

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
    fn div_by_zero() {
        let rust_src = r#"
        #[inline(never)]
        fn divide(a: i32, b: i32) -> i32 {
            a / b
        }

        pub fn main() {
            let x = 10;
            let y = 2;
            let _result = divide(x, y);
        }
        "#;

        let mut expected_hints: HintsPerModule = std::collections::HashMap::new();
        expected_hints.insert(
            ROOT_ID.to_string(),
            vec![FluxHint {
                function: "divide".to_string(),
                span: rustc_span::DUMMY_SP,
                assertion: "b == 0".to_string(),
                panic_type: FluxPanicType::DivisionByZero,
            }],
        );

        run_mii(rust_src, &expected_hints);
    }

    #[test]
    fn rem_by_zero() {
        let rust_src = r#"
        #[inline(never)]
        fn modulo(a: i32, b: i32) -> i32 {
            a % b
        }

        pub fn main() {
            let x = 10;
            let y = 2;
            let _result = modulo(x, y);
        }
        "#;

        let mut expected_hints: HintsPerModule = std::collections::HashMap::new();
        expected_hints.insert(
            ROOT_ID.to_string(),
            vec![FluxHint {
                function: "modulo".to_string(),
                span: rustc_span::DUMMY_SP,
                assertion: "b == 0".to_string(),
                panic_type: FluxPanicType::RemainderByZero,
            }],
        );
        run_mii(rust_src, &expected_hints);
    }

    #[test]
    fn bounds_check() {
        let rust_src = r#"
        #[inline(never)]
        fn do_something_cool(i: usize, arr: &[i32]) -> i32 {
            arr[i]
        }

        pub fn main() {
            let a: [i32; 3] = [1, 2, 3];
            let _result = do_something_cool(1, &a);
        }
        "#;

        let mut expected_hints: HintsPerModule = std::collections::HashMap::new();
        expected_hints.insert(
            ROOT_ID.to_string(),
            vec![FluxHint {
                function: "do_something_cool".to_string(),
                span: rustc_span::DUMMY_SP,
                assertion: "i < arr.len()".to_string(),
                panic_type: FluxPanicType::BoundsCheck,
            }],
        );
        run_mii(rust_src, &expected_hints);
    }

    #[test]
    fn do_the_panic() {
        let rust_src = r#"
        #[inline(never)]
        fn do_something_cool(i: usize, arr: &[i32]) -> i32 {
            panic!("Oh no!! An explicit panic!");
            2
        }

        fn do_the_abort() {
            std::process::abort();
        }

        pub fn main() {
            let a: [i32; 3] = [1, 2, 3];
            let _result = do_something_cool(1, &a);
            let _result2 = do_the_abort();
        }
        "#;

        let mut expected_hints: HintsPerModule = std::collections::HashMap::new();
        expected_hints.insert(
            ROOT_ID.to_string(),
            vec![
                FluxHint {
                    function: "do_something_cool".to_string(),
                    span: rustc_span::DUMMY_SP,
                    assertion: "Explicit Panic".to_string(),
                    panic_type: FluxPanicType::ExplicitPanic,
                },
                FluxHint {
                    function: "do_the_abort".to_string(),
                    span: rustc_span::DUMMY_SP,
                    assertion: "Explicit Panic".to_string(),
                    panic_type: FluxPanicType::ExplicitPanic,
                },
            ],
        );

        run_mii(rust_src, &expected_hints);
    }
}
