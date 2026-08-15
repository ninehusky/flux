// Regression test: naming a *reference* type as the self type of a qualified refinement path.
//
// Converting `&T` creates a region hole, but an `AliasReft` lives inside a refinement expression,
// and `struct_compat::Zipper` only fills region holes by walking types. The hole was therefore
// never filled and `Holes::replace_holes` ICEd with `unfilled region hole '?0`.
//
// NOT a test that a reference self type can carry a refinement. The `impl Len for &'a T` below has
// a *constant* body that never mentions `self`, so it never asks what sort a reference has. Write
// `{ <T as Len>::len(self) }` instead and it fails with `expected 'T::sort', found '()'` -- see
// tests/tests/todo/assoc_reft_ref_self_sort.rs.

use flux_attrs::*;

pub trait Len {
    #![reft(fn len(self: Self) -> int)]
}

pub struct Wrapper;

impl Len for Wrapper {
    #![reft(fn len(self: Self) -> int { 0 })]
}

impl<'a, T: Len> Len for &'a T {
    #![reft(fn len(self: Self) -> int { 0 })]
}

#[refined_by(v: T)]
pub struct Cell<T> {
    #[field(T[v])]
    pub val: T,
}

// The self type of the qualified path is a reference written without a lifetime.
#[sig(fn(&Cell<&T>[@v]) requires <&T as Len>::len(v) >= 0)]
pub fn takes_ref<T: Len>(_c: &Cell<&T>)
where
    for<'a> &'a T: Len,
{
}

#[sig(fn(&Cell<&Wrapper>[@v]) requires <&Wrapper as Len>::len(v) >= 0)]
pub fn takes_concrete_ref(_c: &Cell<&Wrapper>) {}
