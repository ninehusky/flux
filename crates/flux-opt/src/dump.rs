//! Serializable mirror of the no-panic call graph, dumped to JSON for offline analysis.
//!
//! The in-memory [`CallGraph`] is keyed by `Instance` (monomorphized) and holds rustc types
//! (`Instance`, `DefId`, `Location`) that don't implement `Serialize`. This module collapses the
//! graph to **source-level** nodes (one per `DefId`), dedupes edges, and writes a plain JSON
//! mirror. It computes no reachability/SCCs/transitive closure — it is a faithful structural dump.
//!
//! Enabled with `-Fdump-call-graph`. One file `<crate>-call-graph.json` is written per analyzed
//! crate into [`flux_config::log_dir`]; sibling Flux-analyzed crates appear as `ExternalCrate`
//! stub nodes, so cross-crate edges are preserved as `Resolved` edges pointing at those stubs and
//! can be stitched across files by matching `callee_def_path` to another file's `def_path`.

use std::{collections::BTreeMap, fs, io};

use flux_config as config;
use flux_middle::global_env::GlobalEnv;
use rustc_data_structures::fx::FxIndexMap;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_span::FileName;
use serde::Serialize;

use crate::call_graph::{CallGraph, CallSiteKind, NodeKind};

const SCHEMA_VERSION: u32 = 1;

#[derive(Serialize)]
struct CallGraphDump {
    crate_name: String,
    schema_version: u32,
    /// Source-level nodes. The index of a node in this vec is its `id` (used by edges/callers).
    nodes: Vec<NodeDump>,
    /// Nico's materialized reverse map, collapsed to source ids and deduped. Built from `Resolved`
    /// edges only (mirrors `CallGraph::build_callers`), so a transpose of the dumped edge list will
    /// match only if you likewise restrict to `Resolved` edges. Keyed by callee id.
    callers: BTreeMap<usize, Vec<usize>>,
    diagnostics: Diagnostics,
}

#[derive(Serialize)]
struct NodeDump {
    id: usize,
    /// `tcx.def_path_str` — crate-qualified, the join key across per-crate dumps.
    def_path: String,
    /// Function definition span, or `null` when no source span is recoverable.
    def_span: Option<SpanDump>,
    /// `"Analyzed"` | `"ExternalCrate"` | `"Leaf"`.
    node_kind: &'static str,
    /// rustc `DefKind` (the payload of `NodeKind::Leaf`, useful for telling sinks apart).
    def_kind: String,
    /// A non-mono (identity) instance of this function was in the graph.
    has_identity_instance: bool,
    /// Number of distinct monomorphizations folded into this source node.
    monomorphization_count: usize,
    /// This node has an outgoing `Unresolved` edge — any caller set through it is a lower bound.
    has_unresolved_edge: bool,
    /// This node has an outgoing `DynamicDispatch` edge — likewise a lower bound.
    has_dynamic_edge: bool,
    /// Deduped source-level outgoing edges. MIR `Location`s are dropped (not source locations and
    /// not meaningful once monomorphizations are collapsed).
    edges: Vec<EdgeDump>,
}

#[derive(Serialize)]
struct SpanDump {
    file: String,
    start_line: usize,
    start_col: usize,
    end_line: usize,
    end_col: usize,
}

#[derive(Serialize)]
#[serde(tag = "kind")]
enum EdgeDump {
    /// Call resolved to a concrete callee. `callee` is the node id; `callee_def_path` lets you
    /// stitch to another crate's dump when the callee is an `ExternalCrate` stub here.
    Resolved { callee: usize, callee_def_path: String },
    /// Implicit `core::panicking::panic` from an `Assert` terminator — the in-graph panic source.
    SynthesizedPanic,
    /// `FnDef` call whose `Instance::try_resolve` failed (e.g. a trait method). A structural hole.
    Unresolved { callee_def_path: String },
    /// Function-pointer / closure call with no static callee. A structural hole.
    DynamicDispatch,
}

#[derive(Serialize, Default)]
struct Diagnostics {
    /// Node ids whose `def_span` is `null`.
    nodes_without_span: Vec<usize>,
    /// `def_path`s of `Resolved` callees that had no node in the graph (expected to be empty).
    resolved_callee_missing_node: Vec<String>,
}

/// Ordered, deduped edge representation before node ids are resolved.
#[derive(PartialEq, Eq, Hash, Clone, Copy)]
enum EdgeKey {
    Resolved(DefId),
    SynthesizedPanic,
    Unresolved(DefId),
    DynamicDispatch,
}

/// Per-source-node accumulator while folding instances together.
struct NodeAcc {
    def_id: DefId,
    node_kind_rank: u8,
    has_identity_instance: bool,
    monomorphization_count: usize,
    edge_order: Vec<EdgeKey>,
    edge_seen: rustc_hash::FxHashSet<EdgeKey>,
}

// Higher rank wins when several instances of the same `DefId` disagree on classification.
const RANK_LEAF: u8 = 0;
const RANK_EXTERNAL: u8 = 1;
const RANK_ANALYZED: u8 = 2;

fn rank_name(rank: u8) -> &'static str {
    match rank {
        RANK_ANALYZED => "Analyzed",
        RANK_EXTERNAL => "ExternalCrate",
        _ => "Leaf",
    }
}

/// Writes `<crate>-call-graph.json` to the log dir if `-Fdump-call-graph` is set. Errors are
/// logged rather than propagated — a debug dump should never fail the analysis.
pub(crate) fn dump_call_graph(genv: GlobalEnv, graph: &CallGraph<'_>) {
    if !config::dump_call_graph() {
        return;
    }
    if let Err(err) = try_dump(genv, graph) {
        tracing::warn!("failed to dump call graph: {err}");
    }
}

fn try_dump(genv: GlobalEnv, graph: &CallGraph<'_>) -> io::Result<()> {
    let dump = build_dump(genv, graph);
    fs::create_dir_all(config::log_dir())?;
    let path = config::log_dir().join(format!("{}-call-graph.json", dump.crate_name));
    let mut file = fs::File::create(path)?;
    serde_json::to_writer_pretty(&mut file, &dump)?;
    Ok(())
}

fn build_dump(genv: GlobalEnv, graph: &CallGraph<'_>) -> CallGraphDump {
    let tcx = genv.tcx();

    // Pass A: assign a stable id per source-level `DefId` (insertion order of the graph's nodes is
    // deterministic within a run) and fold every instance's info into its source node.
    let mut id_of: FxIndexMap<DefId, usize> = FxIndexMap::default();
    let mut accs: Vec<NodeAcc> = Vec::new();

    for (instance, node) in &graph.nodes {
        let def_id = instance.def_id();
        let idx = *id_of.entry(def_id).or_insert_with(|| {
            accs.push(NodeAcc {
                def_id,
                node_kind_rank: RANK_LEAF,
                has_identity_instance: false,
                monomorphization_count: 0,
                edge_order: Vec::new(),
                edge_seen: rustc_hash::FxHashSet::default(),
            });
            accs.len() - 1
        });
        let acc = &mut accs[idx];

        match node.kind {
            NodeKind::Analyzed { is_mono } => {
                acc.node_kind_rank = acc.node_kind_rank.max(RANK_ANALYZED);
                if is_mono {
                    acc.monomorphization_count += 1;
                } else {
                    acc.has_identity_instance = true;
                }
            }
            NodeKind::ExternalCrate => {
                acc.node_kind_rank = acc.node_kind_rank.max(RANK_EXTERNAL);
            }
            NodeKind::Leaf(_) => {}
        }

        for site in &node.call_sites {
            let key = match site.kind {
                CallSiteKind::Resolved { callee } => EdgeKey::Resolved(callee.def_id()),
                CallSiteKind::SynthesizedPanic => EdgeKey::SynthesizedPanic,
                CallSiteKind::Unresolved { def_id } => EdgeKey::Unresolved(def_id),
                CallSiteKind::DynamicDispatch => EdgeKey::DynamicDispatch,
            };
            if acc.edge_seen.insert(key) {
                acc.edge_order.push(key);
            }
        }
    }

    // Pass B: materialize nodes, resolving `Resolved` edge targets to node ids.
    let mut diagnostics = Diagnostics::default();
    let mut nodes = Vec::with_capacity(accs.len());

    for (idx, acc) in accs.iter().enumerate() {
        let def_span = span_dump(genv, acc.def_id);
        if def_span.is_none() {
            diagnostics.nodes_without_span.push(idx);
        }

        let mut edges = Vec::with_capacity(acc.edge_order.len());
        let mut has_unresolved_edge = false;
        let mut has_dynamic_edge = false;
        for key in &acc.edge_order {
            let edge = match *key {
                EdgeKey::Resolved(callee_def_id) => {
                    let callee_def_path = tcx.def_path_str(callee_def_id);
                    match id_of.get(&callee_def_id) {
                        Some(&callee) => EdgeDump::Resolved { callee, callee_def_path },
                        None => {
                            diagnostics.resolved_callee_missing_node.push(callee_def_path);
                            continue;
                        }
                    }
                }
                EdgeKey::SynthesizedPanic => EdgeDump::SynthesizedPanic,
                EdgeKey::Unresolved(def_id) => {
                    has_unresolved_edge = true;
                    EdgeDump::Unresolved { callee_def_path: tcx.def_path_str(def_id) }
                }
                EdgeKey::DynamicDispatch => {
                    has_dynamic_edge = true;
                    EdgeDump::DynamicDispatch
                }
            };
            edges.push(edge);
        }

        nodes.push(NodeDump {
            id: idx,
            def_path: tcx.def_path_str(acc.def_id),
            def_span,
            node_kind: rank_name(acc.node_kind_rank),
            def_kind: format!("{:?}", tcx.def_kind(acc.def_id)),
            has_identity_instance: acc.has_identity_instance,
            monomorphization_count: acc.monomorphization_count,
            has_unresolved_edge,
            has_dynamic_edge,
            edges,
        });
    }

    // Nico's reverse map, collapsed to source ids and deduped. `UnordMap` iteration is order-
    // guarding, so map each (callee, caller) instance pair to (callee_id, caller_id) and sort for
    // deterministic output before folding into the map.
    let caller_pairs = graph
        .callers
        .items()
        .flat_map(|(callee, callers)| {
            let callee_id = id_of.get(&callee.def_id()).copied();
            callers
                .iter()
                .filter_map(|caller| Some((callee_id?, *id_of.get(&caller.def_id())?)))
                .collect::<Vec<(usize, usize)>>()
        })
        .into_sorted_stable_ord();
    let mut callers: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (callee_id, caller_id) in caller_pairs {
        let entry = callers.entry(callee_id).or_default();
        if entry.last() != Some(&caller_id) {
            entry.push(caller_id);
        }
    }

    CallGraphDump {
        crate_name: tcx.crate_name(LOCAL_CRATE).to_string(),
        schema_version: SCHEMA_VERSION,
        nodes,
        callers,
        diagnostics,
    }
}

/// Structured span, or `None` when the span is dummy/unrecoverable.
fn span_dump(genv: GlobalEnv, def_id: DefId) -> Option<SpanDump> {
    let tcx = genv.tcx();
    let span = tcx.def_span(def_id);
    if span.is_dummy() {
        return None;
    }
    let sm = tcx.sess.source_map();
    let file = match sm.span_to_filename(span) {
        FileName::Real(name) => name.local_path_if_available().display().to_string(),
        other => format!("{other:?}"),
    };
    let lo = sm.lookup_char_pos(span.lo());
    let hi = sm.lookup_char_pos(span.hi());
    Some(SpanDump {
        file,
        start_line: lo.line,
        start_col: lo.col_display,
        end_line: hi.line,
        end_col: hi.col_display,
    })
}
