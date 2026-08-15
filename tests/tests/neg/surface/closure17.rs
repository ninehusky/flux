// Calling an opaque `F: Fn*` parameter must PROVE the refinement on the argument.
//
// The bound is higher-ranked (`for<'a> F: FnOnce(&'a mut [u8]{v: v == n})`), and the
// obligation used to be dropped on the floor: the refined clause was matched against the
// projection obligation syntactically, regions included, so it never matched and every
// precondition attached to the bound was silently lost. See `pos/surface/closure17.rs`.

#[flux::sig(fn(usize[@n], f: F) -> () where F: FnOnce(&mut [u8]{v: v == n}) -> ())]
pub fn call_mut_slice<F>(_n: usize, f: F)
where
    F: FnOnce(&mut [u8]) -> (),
{
    let mut arr = [0u8; 4];
    f(&mut arr) //~ ERROR refinement type
}

#[flux::sig(fn(usize[@n], f: F) -> () where F: FnOnce(&[u8]{v: v == n}) -> ())]
pub fn call_shr_slice<F>(_n: usize, f: F)
where
    F: FnOnce(&[u8]) -> (),
{
    let arr = [0u8; 4];
    f(&arr) //~ ERROR refinement type
}

#[flux::sig(fn(usize[@n], f: F) -> () where F: FnOnce(&usize{v: v == n}) -> ())]
pub fn call_shr_ref<F>(_n: usize, f: F)
where
    F: FnOnce(&usize) -> (),
{
    let x = 4;
    f(&x) //~ ERROR refinement type
}
