/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.OfSimpleGraph
public import TauCeti.Combinatorics.Graph.Simple
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Basic

/-!
# Ear decompositions of graphs associated to simple graphs

This file transports ears, initial stages, and ear decompositions of `Graph.ofSimpleGraph G` to the
subgraph-based ear interface of a simple graph `G`. The decomposition transport preserves every
prefix subgraph, the initial vertex or cycle, and the walk and kind of every ear.
-/

public section

open Set
open scoped Sym2

universe u

namespace Graph

variable {V : Type u} {G : SimpleGraph V}

/-- The traced graph of a walk in `Graph.ofSimpleGraph G` becomes the subgraph traced by the
corresponding simple-graph walk. -/
@[simp]
theorem walkGraph_toSimpleGraphSubgraph {x y : V} (p : (Graph.ofSimpleGraph G).Walk x y)
    (h : (Graph.ofSimpleGraph G).walkGraph p ≤ Graph.ofSimpleGraph G) :
    ((Graph.ofSimpleGraph G).walkGraph p).toSimpleGraphSubgraph h =
      p.toSimpleGraph.toSubgraph := by
  ext a b
  · simp
  · rw [← SimpleGraph.Subgraph.mem_edgeSet, ← SimpleGraph.Subgraph.mem_edgeSet]
    simp

end Graph

namespace Graph.EarKind

/-- Forget edge identities in the kind of a multigraph ear. -/
@[expose]
def toSimpleGraph : Graph.EarKind → SimpleGraph.EarKind
  | .open => .open
  | .closed => .closed

@[simp] theorem toSimpleGraph_open : toSimpleGraph .open = .open := rfl
@[simp] theorem toSimpleGraph_closed : toSimpleGraph .closed = .closed := rfl

end Graph.EarKind

namespace Graph.Ear

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Transport an ear of `Graph.ofSimpleGraph G` to an ear over the corresponding simple
subgraph. -/
@[expose]
def toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    G.Ear (K.toSimpleGraphSubgraph e.base_le) :=
  match e with
  | .open _ p hp hs ht hst hinter hedge =>
      .«open» p.toSimpleGraph (p.isPath_toSimpleGraph_iff.mpr hp) (by simpa using hs)
        (by simpa using ht) hst
        (by simpa using hinter) (by simpa using hedge)
  | .closed _ p hp hs hinter _ =>
      .closed p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp) (by simpa using hs)
        (by simpa using hinter)

@[simp]
theorem kind_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.kind = e.kind.toSimpleGraph := by
  cases e <;> simp [toSimpleGraph, Graph.EarKind.toSimpleGraph]

@[simp]
theorem toWalk_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.toWalk =
      ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toSimpleGraph⟩ := by
  cases e with
  | «open» => unfold toSimpleGraph; rw [SimpleGraph.Ear.toWalk_open, Graph.Ear.toWalk_open]
  | «closed» => unfold toSimpleGraph; rw [SimpleGraph.Ear.toWalk_closed, Graph.Ear.toWalk_closed]

/-- Transport commutes with adjoining an ear to its base graph. -/
@[simp]
theorem toSimpleGraphSubgraph_add (e : (Graph.ofSimpleGraph G).Ear K)
    (hAdd : e.add ≤ Graph.ofSimpleGraph G) :
    e.add.toSimpleGraphSubgraph hAdd = e.toSimpleGraph.adjoin := by
  ext x y
  · rw [Graph.verts_toSimpleGraphSubgraph, SimpleGraph.Ear.verts_adjoin,
      Graph.Ear.vertexSet_add, Graph.Ear.vertexSet_toGraph,
      SimpleGraph.Ear.toSubgraph_eq_toWalk, SimpleGraph.Walk.verts_toSubgraph,
      toWalk_toSimpleGraph, Graph.Walk.support_toSimpleGraph]
    simp
  · rw [← SimpleGraph.Subgraph.mem_edgeSet, ← SimpleGraph.Subgraph.mem_edgeSet,
      Graph.edgeSet_toSimpleGraphSubgraph, SimpleGraph.Ear.edgeSet_adjoin,
      Graph.Ear.edgeSet_add, Graph.Ear.edgeSet_toGraph,
      SimpleGraph.Ear.toSubgraph_eq_toWalk, SimpleGraph.Walk.edgeSet_toSubgraph,
      toWalk_toSimpleGraph]
    simp [SimpleGraph.Walk.edgeSet, Graph.Walk.edges_toSimpleGraph]

end Graph.Ear

namespace Graph.EarStart

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

private theorem SimpleGraph.EarStart.isCycle_eqRec {H L : G.Subgraph} (h : H = L)
    (s : G.EarStart H) : (h ▸ s).IsCycle ↔ s.IsCycle := by
  subst h
  rfl

/-- Transport the initial vertex or cycle of a multigraph ear decomposition to the corresponding
simple subgraph. -/
@[expose]
def toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    G.EarStart (K.toSimpleGraphSubgraph s.le) := by
  cases s with
  | vertex v =>
      exact (Graph.toSimpleGraphSubgraph_noEdge_singleton v.1
        (Graph.EarStart.vertex v).le).symm ▸ .vertex v.1
  | cycle p hp =>
      exact (Graph.walkGraph_toSimpleGraphSubgraph p
        (Graph.EarStart.cycle p hp).le).symm ▸
          .cycle p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)

/-- Transporting a vertex initial stage selects the corresponding simple-graph vertex stage. -/
theorem heq_toSimpleGraph_vertex (v : V(Graph.ofSimpleGraph G)) :
    HEq (Graph.EarStart.vertex v).toSimpleGraph
      (SimpleGraph.EarStart.vertex (G := G) v.1) := by
  unfold toSimpleGraph
  exact eqRec_heq _ _

/-- Transporting a cycle initial stage selects the corresponding simple-graph cycle stage. -/
theorem heq_toSimpleGraph_cycle {x : V} (p : (Graph.ofSimpleGraph G).Walk x x)
    (hp : p.IsCycle) :
    HEq (Graph.EarStart.cycle p hp).toSimpleGraph
      (SimpleGraph.EarStart.cycle p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)) := by
  unfold toSimpleGraph
  exact eqRec_heq _ _

@[simp]
theorem isCycle_toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    s.toSimpleGraph.IsCycle ↔ s.IsCycle := by
  cases s with
  | vertex v =>
      exact (SimpleGraph.EarStart.isCycle_eqRec _ _).trans
        ((SimpleGraph.EarStart.isCycle_vertex v.1).trans
          (Graph.EarStart.isCycle_vertex v).symm)
  | cycle p hp =>
      exact (SimpleGraph.EarStart.isCycle_eqRec _ _).trans
        ((SimpleGraph.EarStart.isCycle_cycle p.toSimpleGraph _).trans
          (Graph.EarStart.isCycle_cycle p hp).symm)

end Graph.EarStart

namespace Graph.EarDecomposition

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Transport a decomposition of a subgraph of `Graph.ofSimpleGraph G` to a decomposition of the
corresponding simple subgraph, retaining every prefix and displayed ear. -/
@[expose]
def toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    G.EarDecomposition (K.toSimpleGraphSubgraph d.final_le) where
  length := d.length
  subgraphAfter i := (d.graphAfter i).toSimpleGraphSubgraph (d.graphAfter_le i)
  start := d.start.toSimpleGraph
  earAt i :=
    (d.earAt i).2.toSimpleGraph.copy
      (Graph.toSimpleGraphSubgraph_congr (d.earAt_fst i) (d.earAt i).2.base_le
        (d.graphAfter_le i.castSucc))
  subgraphAfter_succ i := by
    let e := (d.earAt i).2
    let hbase := Graph.toSimpleGraphSubgraph_congr (d.earAt_fst i) e.base_le
      (d.graphAfter_le i.castSucc)
    change (d.graphAfter i.succ).toSimpleGraphSubgraph (d.graphAfter_le i.succ) =
      (e.toSimpleGraph.copy hbase).adjoin
    calc
      _ = e.add.toSimpleGraphSubgraph e.add_le :=
        Graph.toSimpleGraphSubgraph_congr (d.graphAfter_succ i) _ _
      _ = e.toSimpleGraph.adjoin := e.toSimpleGraphSubgraph_add e.add_le
      _ = (d.graphAfter i.castSucc).toSimpleGraphSubgraph
            (d.graphAfter_le i.castSucc) ⊔ e.toSimpleGraph.toSubgraph := by
        rw [SimpleGraph.Ear.adjoin_def]
        exact congrArg (fun H : G.Subgraph ↦ H ⊔ e.toSimpleGraph.toSubgraph) hbase
      _ = (e.toSimpleGraph.copy hbase).adjoin :=
        (SimpleGraph.Ear.adjoin_copy _ _).symm
  subgraphAfter_last :=
    Graph.toSimpleGraphSubgraph_congr d.graphAfter_last
      (d.graphAfter_le (Fin.last d.length)) d.final_le

@[simp]
theorem length_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.length = d.length := rfl

@[simp]
theorem subgraphAfter_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin (d.length + 1)) :
    d.toSimpleGraph.subgraphAfter i =
      (d.graphAfter i).toSimpleGraphSubgraph (d.graphAfter_le i) := rfl

@[simp]
theorem initial_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.initial =
      (d.graphAfter 0).toSimpleGraphSubgraph (d.graphAfter_le 0) :=
  (SimpleGraph.EarDecomposition.subgraphAfter_zero d.toSimpleGraph).symm

@[simp]
theorem start_isCycle_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.start.IsCycle ↔ d.start.IsCycle :=
  d.start.isCycle_toSimpleGraph

@[simp]
theorem kindAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) : d.toSimpleGraph.kindAt i = (d.kindAt i).toSimpleGraph := by
  simp [SimpleGraph.EarDecomposition.kindAt_def, Graph.EarDecomposition.kindAt_eq,
    toSimpleGraph]

@[simp]
theorem walkAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) :
    d.toSimpleGraph.walkAt i =
      ⟨(d.walkAt i).1, (d.walkAt i).2.1, (d.walkAt i).2.2.toSimpleGraph⟩ := by
  rw [Graph.EarDecomposition.walkAt_eq]
  simp [SimpleGraph.EarDecomposition.walkAt_def, toSimpleGraph]

/-- Transport preserves the open-ear-decomposition predicate. -/
@[simp]
theorem isOpen_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.IsOpen ↔ d.IsOpen := by
  rw [SimpleGraph.EarDecomposition.isOpen_iff, Graph.EarDecomposition.isOpen_iff]
  change (d.toSimpleGraph.start.IsCycle ∧
      ∀ i : Fin d.length, d.toSimpleGraph.kindAt i = .open) ↔
    d.start.IsCycle ∧ ∀ i : Fin d.length, d.kindAt i = .open
  rw [start_isCycle_toSimpleGraph]
  constructor
  · rintro ⟨hstart, hears⟩
    refine ⟨hstart, fun i ↦ ?_⟩
    cases hkind : d.kindAt i with
    | «open» => rfl
    | closed =>
        have h := hears i
        rw [kindAt_toSimpleGraph, hkind, Graph.EarKind.toSimpleGraph_closed] at h
        exact SimpleGraph.EarKind.noConfusion h
  · rintro ⟨hstart, hears⟩
    refine ⟨hstart, fun i ↦ ?_⟩
    rw [kindAt_toSimpleGraph, hears i]
    exact Graph.EarKind.toSimpleGraph_open

end Graph.EarDecomposition
