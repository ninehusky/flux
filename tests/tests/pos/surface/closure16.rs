// Regression test: a closure bound in a surface where-clause whose argument mentions a reference.
//
// Rustc's `Fn`-sugar makes the elided lifetime late bound, so `predicates_of` yields
// `for<'a> F: FnOnce<(&'a mut [u8],)>` while the surface bound is converted under an empty binder.
// Matching the two used to fail with "cannot determine corresponding unrefined predicate".

#[flux::sig(fn(len: usize[@n], f: F) -> R where F: FnOnce(&mut [u8]{v: v == n}) -> R)]
fn consume<R, F>(len: usize, f: F) -> R
where
    F: FnOnce(&mut [u8]) -> R,
{
    let mut buf = [0u8; 32];
    f(&mut buf[..len])
}

fn consume_client() {
    consume(4, |buf| {
        let _x = buf[3];
    });
}

// The same shape on a trait method, which is where the bound is genuinely higher-ranked.
trait TxToken {
    #[flux::sig(fn(self: Self, len: usize[@n], f: F) -> R where F: FnOnce(&mut [u8]{v: v == n}) -> R)]
    fn consume<R, F>(self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R;
}

struct Tok;

impl TxToken for Tok {
    fn consume<R, F>(self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        let mut buf = [0u8; 32];
        f(&mut buf[..len])
    }
}

fn tok_client<T: TxToken>(t: T) {
    t.consume(4, |buf| {
        let _x = buf[3];
    });
}
