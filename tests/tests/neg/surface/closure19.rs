// A refined `Fn*` bound must constrain calls made from inside a *closure* body too.
//
// The clauses in scope came from `predicates_of` on the item being checked, and a closure
// has none of its own -- they all live on its parent. So the body of a closure was checked
// with an empty param env, the refined bound was invisible there, and `f(buf)` proved
// nothing. This is the shape of every forwarding `TxToken` implementor.

pub trait TxToken {
    #[flux::sig(fn(self: Self, len: usize[@n], f: F) -> R where F: FnOnce(&mut [u8]{v: v == n}) -> R)]
    fn consume<R, F>(self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R;
}

// Asks the inner token for one byte more than `f` accepts.
#[flux::sig(fn(T, usize[@n], F) where F: FnOnce(&mut [u8]{v: v == n}) -> ())]
pub fn forward<T: TxToken, F>(tok: T, len: usize, f: F)
where
    F: FnOnce(&mut [u8]),
{
    tok.consume(len + 1, |buf| f(buf)) //~ ERROR refinement type
}
