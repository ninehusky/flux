// Regression: a `no_panic_if` condition must reach a nested closure.
//
// A closure has no signature of its own, so its panic-freedom obligation is the enclosing item's.
// That obligation used to be a bool -- "is `#[flux::no_panic]` set somewhere up the parent chain?"
// -- which cannot express a *conditional* one. A closure capturing a generic whose panic-freedom is
// conditional was therefore unprovable at its call site, even though the same call written directly
// verified.

#[flux::sig(fn(f: F) -> i32)]
#[flux::no_panic_if(F::no_panic())]
fn direct<F: FnOnce() -> i32>(f: F) -> i32 {
    f()
}

#[flux::sig(fn(f: F) -> i32)]
#[flux::no_panic_if(F::no_panic())]
fn via_closure<F: FnOnce() -> i32>(f: F) -> i32 {
    let g = || f();
    g()
}

#[flux::sig(fn(f: F) -> i32)]
#[flux::no_panic_if(F::no_panic())]
fn via_nested_closure<F: FnOnce() -> i32>(f: F) -> i32 {
    let g = || {
        let h = || f();
        h()
    };
    g()
}

// The condition reaches the closure without swallowing the surrounding obligations: a closure that
// captures nothing conditional still verifies.
#[flux::no_panic]
#[flux::sig(fn() -> i32)]
fn unconditional_closure() -> i32 {
    let g = || 1;
    g()
}
