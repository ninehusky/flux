#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_trait_selection;

use std::{
    io,
    panic::{AssertUnwindSafe, catch_unwind},
    path::Path,
};

use flux_rustc_bridge::lowering::resolve_call_query;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::{
    mir::TerminatorKind,
    ty::{TyCtxt, TypingMode},
};
use rustc_span::{FileName, Span};
use rustc_trait_selection::traits::SelectionContext;

/// The call graph maps each function to its callees along with the call-site span.
pub type CallGraph = FxHashMap<DefId, Vec<(DefId, Span)>>;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum PanicSpec {
    WillNotPanic,
    MightPanic(PanicReason),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PanicReason {
    Unknown,
    // Transitively panicking means that the function itself has at least one callee chain
    // that eventually leads to one of the other panic reasons.
    Transitive,
    CannotResolve(CannotResolveReason),
    NotInCallGraph,
    NoMIRAvailable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CannotResolveReason {
    NoMIRAvailable(DefId, DefKind),
    UnresolvedTraitMethod(DefId),
    NotFnDef(DefId),
}

#[derive(Debug, Clone)]
struct GraphBuildResult {
    call_graph: CallGraph,
    pub resolution_failures: FxHashMap<DefId, CannotResolveReason>,
}

/// The entry point for no-panic inference. Given a root function, explores its call graph and returns
/// an over-approximation of if it might panic and why.
pub fn infer_no_panics(tcx: TyCtxt, root: DefId) -> FxHashMap<DefId, PanicSpec> {
    // 1. Build the call graph.
    let GraphBuildResult { call_graph, resolution_failures } = build_call_graph(tcx, &[root]);

    // 2. Seed the call graph with initial panic specs -- if the previous step found
    //    resolution failures, add those reasons here. Otherwise, seed with Unknown.
    let mut initial_specs: FxHashMap<DefId, PanicSpec> = FxHashMap::default();

    for def_id in call_graph.keys() {
        if let Some(resolution_error) = resolution_failures.get(def_id) {
            initial_specs.insert(
                *def_id,
                PanicSpec::MightPanic(PanicReason::CannotResolve(*resolution_error)),
            );
        } else {
            initial_specs.insert(*def_id, PanicSpec::MightPanic(PanicReason::Unknown));
        }
    }

    // 3. Run fixpoint to propagate panic specs through the call graph.
    run_fixpoint(&call_graph, &mut initial_specs);

    initial_specs
}

/// Given a function that is known to transitively panic, returns:
/// - The chain of intermediate calls: each entry is `(callee, call_site_span)` where
///   `call_site_span` is the span of the call to `callee` within the previous function.
/// - The leaf `(DefId, PanicReason)`: the function at the end of the chain and the
///   reason it panics (always non-Transitive).
///
/// Returns `None` if no trace can be computed (e.g. no MIR available for `start`).
pub fn panic_trace_for(tcx: TyCtxt, start: DefId) -> Option<(Vec<(DefId, Span)>, (DefId, PanicReason))> {
    if !tcx.is_mir_available(start) {
        return None;
    }

    let GraphBuildResult { call_graph, resolution_failures } = build_call_graph(tcx, &[start]);

    let mut initial_specs: FxHashMap<DefId, PanicSpec> = FxHashMap::default();
    for def_id in call_graph.keys() {
        if let Some(reason) = resolution_failures.get(def_id) {
            initial_specs.insert(*def_id, PanicSpec::MightPanic(PanicReason::CannotResolve(*reason)));
        } else {
            initial_specs.insert(*def_id, PanicSpec::MightPanic(PanicReason::Unknown));
        }
    }

    let witnesses = run_fixpoint(&call_graph, &mut initial_specs);

    // Follow the witness chain from `start`, guarding against cycles.
    let mut trace = Vec::new();
    let mut current = start;
    let mut visited = FxHashSet::default();
    visited.insert(current);
    while let Some(&(next, span)) = witnesses.get(&current) {
        trace.push((next, span));
        if !visited.insert(next) {
            break;
        }
        current = next;
    }

    // `current` is now the leaf — the function whose panic reason is non-Transitive.
    // If it's not in initial_specs, it's a resolution failure callee that was never
    // added to the call graph; look it up in resolution_failures for the real reason.
    let leaf_reason = match initial_specs.get(&current) {
        Some(PanicSpec::MightPanic(reason)) => *reason,
        _ => resolution_failures
            .get(&current)
            .map(|r| PanicReason::CannotResolve(*r))
            .unwrap_or(PanicReason::Unknown),
    };

    Some((trace, (current, leaf_reason)))
}

/// Builds the call graph starting from the root function. If we encounter a call we can't resolve, we add it to the resolution_failures map and keep going.
fn build_call_graph(tcx: TyCtxt, roots: &[DefId]) -> GraphBuildResult {
    let mut resolution_failures = FxHashMap::default();
    let mut call_graph: CallGraph = FxHashMap::default();

    if roots.iter().any(|root| !tcx.def_kind(*root).is_fn_like()) {
        flux_common::bug!(
            "flux-opt::infer_no_panics: all root DefIds must be functions, but found non-function roots: {:?}",
            roots
                .iter()
                .filter(|root| !tcx.def_kind(**root).is_fn_like())
                .map(|root| tcx.def_path_str(*root))
                .collect::<Vec<_>>()
        );
    }

    explore(tcx, roots, &mut call_graph, &mut resolution_failures);

    GraphBuildResult { call_graph, resolution_failures }
}

/// Tries to resolve a trait method call to an impl method. If successful, returns the DefId of the impl method.
fn try_resolve<'tcx>(
    tcx: &TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Result<DefId, CannotResolveReason> {
    let param_env = tcx.param_env(def_id);
    let infcx = tcx
        .infer_ctxt()
        .with_next_trait_solver(true)
        .build(TypingMode::non_body_analysis());
    let mut selcx = SelectionContext::new(&infcx);

    let resolved = resolve_call_query(*tcx, &mut selcx, param_env, def_id, args);

    let Some((impl_id, _)) = resolved else {
        // Error case 1: we fail to resolve a trait method to an impl.
        return Err(CannotResolveReason::UnresolvedTraitMethod(def_id));
    };

    if !tcx.is_mir_available(impl_id) {
        return Err(CannotResolveReason::NoMIRAvailable(impl_id, tcx.def_kind(impl_id)));
    }

    Ok(impl_id)
}

/// Returns the callees of a function with their call-site spans, or an error if we fail to resolve any callees.
fn get_callees(tcx: &TyCtxt, def_id: DefId) -> Result<Vec<(DefId, Span)>, CannotResolveReason> {
    let body = tcx.optimized_mir(def_id);

    let mut callees = Vec::new();
    for bb in body.basic_blocks.iter() {
        if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
            let call_span = bb.terminator().source_info.span;
            let ty = func.ty(&body.local_decls, *tcx);

            match ty.kind() {
                rustc_middle::ty::TyKind::FnDef(def_id, args) => {
                    let Some(_trait_id) = tcx.trait_of_assoc(*def_id) else {
                        // If it's a free function, there's no need to resolve.
                        callees.push((*def_id, call_span));
                        continue;
                    };

                    let impl_id = try_resolve(tcx, *def_id, args)?;

                    if !tcx.is_mir_available(impl_id) {
                        return Err(CannotResolveReason::NoMIRAvailable(
                            impl_id,
                            tcx.def_kind(impl_id),
                        ));
                    }

                    callees.push((impl_id, call_span));
                }
                _ => {
                    // Error case 2: We're trying to reason about something that's not an FnDef.
                    return Err(CannotResolveReason::NotFnDef(def_id));
                }
            };
        }
    }
    Ok(callees)
}

/// Explores the call graph starting from the root function, populating the call graph and resolution failures.
fn explore(
    tcx: TyCtxt,
    roots: &[DefId],
    call_graph: &mut CallGraph,
    resolution_failures: &mut FxHashMap<DefId, CannotResolveReason>,
) {
    let mut worklist: Vec<DefId> = roots.to_vec();

    // 1. Seed the worklist with the root functions, and add their callees to the call graph.
    for root in roots {
        let root = *root;
        if !tcx.is_mir_available(root) {
            let def_kind = tcx.def_kind(root);
            if matches!(def_kind, DefKind::AssocFn) {
                resolution_failures.insert(root, CannotResolveReason::UnresolvedTraitMethod(root));
            } else {
                resolution_failures
                    .insert(root, CannotResolveReason::NoMIRAvailable(root, def_kind));
            }
            call_graph.insert(root, Vec::new());
            return;
        }

        match get_callees(&tcx, root) {
            Ok(callees) => {
                call_graph.insert(root, callees);
            }
            Err(reason) => {
                call_graph.insert(root, Vec::new());
                resolution_failures.insert(root, reason);
                return;
            }
        }
    }

    // 2. Explore reachable callees (build closed call graph)
    while let Some(f) = worklist.pop() {
        let callees = call_graph.get(&f).unwrap().clone();

        for (callee, _span) in callees {
            if !call_graph.contains_key(&callee) {
                if tcx.is_mir_available(callee) {
                    match get_callees(&tcx, callee) {
                        Ok(callees) => {
                            call_graph.insert(callee, callees);
                            worklist.push(callee);
                        }
                        Err(reason) => {
                            resolution_failures.insert(callee, reason);
                            continue;
                        }
                    }
                } else {
                    resolution_failures.insert(
                        callee,
                        CannotResolveReason::NoMIRAvailable(callee, tcx.def_kind(callee)),
                    );
                    continue;
                }
            }
        }
    }
}

/// Runs a fixpoint algorithm over the call graph to propagate panic specs.
/// If all callees are known to not panic, then this function is known to not panic.
/// If a function has a callee that might panic, then it transitively might panic.
///
/// Returns a witness map: for each function marked `Transitive`, the immediate bad callee
/// and the call-site span that caused it.
fn run_fixpoint(
    call_graph: &CallGraph,
    fn_to_no_panic: &mut FxHashMap<DefId, PanicSpec>,
) -> FxHashMap<DefId, (DefId, Span)> {
    let mut witnesses: FxHashMap<DefId, (DefId, Span)> = FxHashMap::default();
    let mut changed = true;
    while changed {
        changed = false;

        let keys: Vec<DefId> = call_graph.keys().copied().collect();

        for f in keys {
            // Skip functions we've already seeded.
            let current_spec = fn_to_no_panic.get(&f).unwrap();

            match current_spec {
                PanicSpec::WillNotPanic | PanicSpec::MightPanic(PanicReason::CannotResolve(_)) => {
                    continue;
                }
                _ => (),
            };

            let callees = match call_graph.get(&f) {
                Some(callees) => callees,
                None => {
                    unreachable!("run_fixpoint: call graph should contain all reachable functions");
                }
            };

            let mut bad_callees: Vec<(DefId, Span)> = Vec::new();

            for (callee, span) in callees {
                match fn_to_no_panic.get(callee) {
                    Some(PanicSpec::WillNotPanic) => {}
                    _ => bad_callees.push((*callee, *span)),
                }
            }

            // Case 1: All callees are known to not panic, so this function is also known to not panic.
            if bad_callees.is_empty() {
                changed = true;
                fn_to_no_panic.insert(f, PanicSpec::WillNotPanic);
            // Case 2: This function has a callee that transitively might panic, so this function transitively might panic.
            } else if matches!(current_spec, PanicSpec::MightPanic(PanicReason::Unknown)) {
                let current_spec = fn_to_no_panic.get_mut(&f).unwrap();
                changed = true;
                *current_spec = PanicSpec::MightPanic(PanicReason::Transitive);
                // Record the first bad callee as the witness for this function.
                witnesses.entry(f).or_insert(bad_callees[0]);
            }
        }
    }
    witnesses
}

/// Classification of a single call-site edge for the per-crate callgraph dump.
#[derive(Debug, Clone, Copy)]
enum DumpEdgeKind {
    /// A direct call to a free function (no trait dispatch).
    Direct,
    /// A trait method call that resolved to a concrete impl `DefId`.
    TraitDispatchResolved,
}

impl DumpEdgeKind {
    fn as_str(self) -> &'static str {
        match self {
            DumpEdgeKind::Direct => "direct",
            DumpEdgeKind::TraitDispatchResolved => "trait_dispatch_resolved",
        }
    }
}

struct CallSiteAnalysis {
    edges: Vec<(DefId, Span, DumpEdgeKind)>,
    unresolved: Vec<(Span, CannotResolveReason)>,
}

/// Like [`get_callees`] but records per-call-site resolution failures instead of
/// short-circuiting on the first failure. Intended for the callgraph dump where
/// we want as much information as possible per function.
fn analyze_callees(tcx: &TyCtxt, def_id: DefId) -> CallSiteAnalysis {
    let body = tcx.optimized_mir(def_id);
    let mut edges = Vec::new();
    let mut unresolved = Vec::new();

    for bb in body.basic_blocks.iter() {
        let TerminatorKind::Call { func, .. } = &bb.terminator().kind else { continue };
        let call_span = bb.terminator().source_info.span;
        let ty = func.ty(&body.local_decls, *tcx);

        match ty.kind() {
            rustc_middle::ty::TyKind::FnDef(callee_def_id, args) => {
                if tcx.trait_of_assoc(*callee_def_id).is_none() {
                    edges.push((*callee_def_id, call_span, DumpEdgeKind::Direct));
                    continue;
                }
                match try_resolve(tcx, *callee_def_id, args) {
                    Ok(impl_id) => {
                        edges.push((impl_id, call_span, DumpEdgeKind::TraitDispatchResolved));
                    }
                    Err(reason) => unresolved.push((call_span, reason)),
                }
            }
            _ => unresolved.push((call_span, CannotResolveReason::NotFnDef(def_id))),
        }
    }

    CallSiteAnalysis { edges, unresolved }
}

fn format_span(tcx: TyCtxt, span: Span) -> String {
    let sm = tcx.sess.source_map();
    let loc = sm.lookup_char_pos(span.lo());
    let FileName::Real(real) = &loc.file.name else {
        return format!("<unknown>:{}", loc.line);
    };
    let p = real.local_path_if_available();
    let path = if p.is_absolute() {
        let working_dir = tcx.sess.opts.working_dir.local_path_if_available();
        p.strip_prefix(working_dir).unwrap_or(p)
    } else {
        p
    };
    format!("{}:{}", path.display(), loc.line)
}

fn cannot_resolve_reason_str(tcx: TyCtxt, reason: CannotResolveReason) -> String {
    match reason {
        CannotResolveReason::NoMIRAvailable(def_id, _) => {
            format!("NoMIRAvailable({})", tcx.def_path_str(def_id))
        }
        CannotResolveReason::UnresolvedTraitMethod(def_id) => {
            format!("UnresolvedTraitMethod({})", tcx.def_path_str(def_id))
        }
        CannotResolveReason::NotFnDef(def_id) => {
            format!("NotFnDef({})", tcx.def_path_str(def_id))
        }
    }
}

/// Emit a per-crate call graph as JSON. The output schema is:
///
/// ```json
/// {
///   "crate": "<crate name>",
///   "edges": [
///     { "caller": "<def_path_str>",
///       "callee": "<def_path_str>",
///       "span":   "<rel/path.rs:LINE>",
///       "edge_kind": "direct" | "trait_dispatch_resolved" }
///   ],
///   "unresolved": [
///     { "caller": "<def_path_str>",
///       "site":   "<rel/path.rs:LINE>",
///       "reason": "<CannotResolveReason debug>" }
///   ]
/// }
/// ```
///
/// Edges originate at functions defined in the current crate. Callees may live in
/// any crate; the workspace-wide aggregation step is responsible for stitching
/// per-crate JSONs together.
pub fn dump_call_graph(tcx: TyCtxt, crate_name: &str, out_path: &Path) -> io::Result<()> {
    use serde_json::json;

    let mut edges = Vec::new();
    let mut unresolved = Vec::new();

    for local_id in tcx.iter_local_def_id() {
        let kind = tcx.def_kind(local_id);
        if !matches!(kind, DefKind::Fn | DefKind::AssocFn | DefKind::Closure) {
            continue;
        }
        if !tcx.is_mir_available(local_id) {
            continue;
        }

        let caller_def_id = local_id.to_def_id();
        let caller_path = tcx.def_path_str(caller_def_id);

        // Per-fn `catch_unwind`: rustc trait-selection can ICE on some bodies
        // (e.g. const-trait bounds with bound vars). Don't let one bad function
        // sink the whole crate's dump — record the panic as an unresolved entry
        // and keep going.
        let analysis = match catch_unwind(AssertUnwindSafe(|| analyze_callees(&tcx, caller_def_id)))
        {
            Ok(a) => a,
            Err(payload) => {
                let msg = if let Some(s) = payload.downcast_ref::<&'static str>() {
                    (*s).to_string()
                } else if let Some(s) = payload.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "<non-string panic payload>".to_string()
                };
                unresolved.push(json!({
                    "caller": caller_path,
                    "site": format_span(tcx, tcx.def_span(caller_def_id)),
                    "reason": format!("AnalyzerPanic({msg})"),
                }));
                continue;
            }
        };

        for (callee, span, edge_kind) in analysis.edges {
            edges.push(json!({
                "caller": caller_path,
                "callee": tcx.def_path_str(callee),
                "span": format_span(tcx, span),
                "edge_kind": edge_kind.as_str(),
            }));
        }
        for (span, reason) in analysis.unresolved {
            unresolved.push(json!({
                "caller": caller_path,
                "site": format_span(tcx, span),
                "reason": cannot_resolve_reason_str(tcx, reason),
            }));
        }
    }

    let payload = json!({
        "crate": crate_name,
        "edges": edges,
        "unresolved": unresolved,
    });

    if let Some(parent) = out_path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent)?;
        }
    }

    let file = std::fs::File::create(out_path)?;
    serde_json::to_writer_pretty(file, &payload).map_err(io::Error::other)?;
    Ok(())
}
