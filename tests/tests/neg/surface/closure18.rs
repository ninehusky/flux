// A refined `Fn*` bound on a *trait* method must constrain the impl body too.
//
// An impl method with no `#[flux::sig]` is checked against its own, unrefined, where-clause,
// so the body used to be free to call `f` with a buffer of any length while callers of the
// trait method still got to assume the refinement.

trait TxToken {
    #[flux::sig(fn(self: Self, len: usize[@n], f: F) -> R where F: FnOnce(&mut [u8]{v: v == n}) -> R)]
    fn consume<R, F>(self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R;
}

struct Unannotated;

impl TxToken for Unannotated {
    fn consume<R, F>(self, _len: usize, f: F) -> R //~ ERROR refinement type
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        let mut buf = [0u8; 42];
        f(&mut buf)
    }
}

struct Annotated;

impl TxToken for Annotated {
    #[flux::sig(fn(self: Self, len: usize[@n], f: F) -> R where F: FnOnce(&mut [u8]{v: v == n}) -> R)]
    fn consume<R, F>(self, _len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        let mut buf = [0u8; 42];
        f(&mut buf) //~ ERROR refinement type
    }
}
