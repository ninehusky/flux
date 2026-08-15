// Regression test: a closure bound in a surface where-clause whose argument mentions a reference.
//
// Rustc's `Fn`-sugar makes the elided lifetime late bound, so `predicates_of` yields
// `for<'a> F: FnOnce<(&'a mut [u8],)>` while the surface bound is converted under an empty binder.
// Matching the two used to fail with "cannot determine corresponding unrefined predicate".
//
// The bodies below hand `f` a buffer whose length is exactly `n`, so the precondition of the
// bound is discharged. See `neg/surface/closure17.rs` for the case where it is not.

#[flux::sig(fn(len: usize[@n], buf: &mut [u8][n], f: F) -> R where F: FnOnce(&mut [u8]{v: v == n}) -> R)]
fn consume<R, F>(len: usize, buf: &mut [u8], f: F) -> R
where
    F: FnOnce(&mut [u8]) -> R,
{
    let _ = len;
    f(buf)
}

fn consume_client() {
    let mut buf = [0u8; 4];
    consume(4, &mut buf, |buf| {
        let _x = buf[3];
    });
}

// The same shape on a trait method, which is where the bound is genuinely higher-ranked.
trait TxToken {
    #[flux::sig(fn(self: Self, len: usize[@n], buf: &mut [u8][n], f: F) -> R where F: FnOnce(&mut [u8]{v: v == n}) -> R)]
    fn consume<R, F>(self, len: usize, buf: &mut [u8], f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R;
}

struct Tok;

impl TxToken for Tok {
    // The refined bound has to be repeated here: an impl method with no signature is checked
    // against its own (unrefined) where-clause, and the trait's refinement of `F` would not
    // apply to this body.
    #[flux::sig(fn(self: Self, len: usize[@n], buf: &mut [u8][n], f: F) -> R where F: FnOnce(&mut [u8]{v: v == n}) -> R)]
    fn consume<R, F>(self, len: usize, buf: &mut [u8], f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        let _ = len;
        f(buf)
    }
}

fn tok_client<T: TxToken>(t: T) {
    let mut buf = [0u8; 4];
    t.consume(4, &mut buf, |buf| {
        let _x = buf[3];
    });
}
