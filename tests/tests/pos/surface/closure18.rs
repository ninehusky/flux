// The positive counterpart of `neg/surface/closure19.rs`: forwarding a refined `Fn*`
// parameter into an inner token's closure verifies when the lengths do line up.

pub trait TxToken {
    #[flux::sig(fn(self: Self, len: usize[@n], f: F) -> R where F: FnOnce(&mut [u8]{v: v == n}) -> R)]
    fn consume<R, F>(self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R;
}

#[flux::sig(fn(T, usize[@n], F) where F: FnOnce(&mut [u8]{v: v == n}) -> ())]
pub fn forward<T: TxToken, F>(tok: T, len: usize, f: F)
where
    F: FnOnce(&mut [u8]),
{
    tok.consume(len, |buf| f(buf))
}
