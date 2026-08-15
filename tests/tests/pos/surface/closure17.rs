// The positive counterpart of `neg/surface/closure17.rs`: calling an opaque `F: Fn*`
// parameter whose bound refines a *reference* argument must still verify when the
// argument genuinely satisfies the refinement.

#[flux::sig(fn(usize[@n], buf: &mut [u8][n], f: F) -> () where F: FnOnce(&mut [u8]{v: v == n}) -> ())]
pub fn call_mut_slice<F>(_n: usize, buf: &mut [u8], f: F)
where
    F: FnOnce(&mut [u8]) -> (),
{
    f(buf)
}

#[flux::sig(fn(usize[@n], buf: &[u8][n], f: F) -> () where F: FnOnce(&[u8]{v: v == n}) -> ())]
pub fn call_shr_slice<F>(_n: usize, buf: &[u8], f: F)
where
    F: FnOnce(&[u8]) -> (),
{
    f(buf)
}

#[flux::sig(fn(usize[@n], x: &usize[n], f: F) -> () where F: FnOnce(&usize{v: v == n}) -> ())]
pub fn call_shr_ref<F>(_n: usize, x: &usize, f: F)
where
    F: FnOnce(&usize) -> (),
{
    f(x)
}

// The ASSUME side: a closure passed to such a function still gets to rely on the refinement.
pub fn client() {
    let mut arr = [0u8; 4];
    call_mut_slice(4, &mut arr, |buf| {
        let _x = buf[3];
    });
}
