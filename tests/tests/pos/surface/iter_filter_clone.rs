// Regression test: normalizing `<Filter<I, P> as Iterator>::Item` walks the projection
// predicates of `impl<I, P> Iterator for Filter<I, P>`, which include the higher-ranked
// clause `P: for<'a> FnMut(&'a I::Item) -> bool`. Blindly skipping that `for<'a>` binder
// left `'a` escaping in the obligation `<P as FnOnce<(&'a I::Item,)>>::Output`, which then
// tripped the escaping-bound-vars guard in `assemble_candidates_from_impls`.
//
// Note the predicate must be a closure and the adapter must be cloned to reach that path.

pub fn filter_clone_any(xs: core::slice::Iter<u32>, k: u32) -> bool {
    let f = xs.filter(|x| **x > k);
    f.clone().any(|v| *v == k)
}
