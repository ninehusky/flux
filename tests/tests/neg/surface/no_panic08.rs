// Regression (negative): a `no_panic_if` condition reaching a closure must not discharge
// obligations the condition says nothing about.

fn boom() -> i32 {
    panic!()
}

// The condition is about `F`, not about `boom`.
#[flux::sig(fn(f: F) -> i32)]
#[flux::no_panic_if(F::no_panic())]
fn cond_does_not_cover_boom<F: FnOnce() -> i32>(f: F) -> i32 {
    let _ = f;
    let g = || boom(); //~ ERROR may panic
    g()
}

// The condition is about `G`, so `F`'s panic-freedom is not assumed.
#[flux::sig(fn(f: F, g: G) -> i32)]
#[flux::no_panic_if(G::no_panic())]
fn cond_on_other_param<F: FnOnce() -> i32, G: FnOnce() -> i32>(f: F, g: G) -> i32 {
    let _ = g;
    let h = || f(); //~ ERROR may panic
    h()
}

// An unconditional obligation on the enclosing item still reaches the closure body.
#[flux::no_panic]
#[flux::sig(fn() -> i32)]
fn unconditional<F>() -> i32 {
    let g = || boom(); //~ ERROR may panic
    g()
}
