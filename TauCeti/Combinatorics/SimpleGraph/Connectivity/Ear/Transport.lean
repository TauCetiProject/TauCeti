/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Basic
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Basic

/-!
# Transporting ear decompositions of simple graphs

This file transports ear data between the subgraph interface of a simple graph `G` and the
edge-labelled interface of `Graph.ofSimpleGraph G`. The maps preserve lengths, stage graphs,
displayed ears, walks, kinds, initial data, prefix decompositions, and openness. The underlying
subgraph conversions are mutually inverse.
-/

public section

open Set

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

namespace EarKind

/-- Identify simple-graph ear kinds with edge-labelled graph ear kinds. -/
@[expose]
def toGraph : SimpleGraph.EarKind → Graph.EarKind
  | .open => .open
  | .closed => .closed

@[simp] theorem toGraph_open : SimpleGraph.EarKind.open.toGraph = .open := rfl
@[simp] theorem toGraph_closed : SimpleGraph.EarKind.closed.toGraph = .closed := rfl

@[simp]
theorem toGraph_eq_open (kind : SimpleGraph.EarKind) : kind.toGraph = .open ↔ kind = .open := by
  cases kind <;> simp

@[simp]
theorem toGraph_eq_closed (kind : SimpleGraph.EarKind) :
    kind.toGraph = .closed ↔ kind = .closed := by
  cases kind <;> simp

end EarKind

namespace Ear

/-- Transport a simple-graph ear to the edge-labelled graph interface. -/
@[expose]
def toGraph (e : G.Ear H) : (Graph.ofSimpleGraph G).Ear H.toGraph := by
  cases e with
  | «open» p hp hu hv huv hint hedge =>
      exact .open H.toGraph_le p.toGraph (p.isPath_toGraph_iff.mpr hp)
        (by simpa) (by simpa) huv
        (by simpa only [SimpleGraph.Walk.support_toGraph, Subgraph.vertexSet_toGraph] using hint)
        (by simpa only [SimpleGraph.Walk.edges_toGraph, Subgraph.edgeSet_toGraph] using hedge)
  | closed c hc hu hint =>
      exact .closed H.toGraph_le c.toGraph (c.isCycle_toGraph_iff.mpr hc)
        (by simpa)
        (by simpa only [SimpleGraph.Walk.support_toGraph, Subgraph.vertexSet_toGraph] using hint)
        (by simpa only [SimpleGraph.Walk.edges_toGraph, Subgraph.edgeSet_toGraph]
          using fun f hf ↦ closed_edges_notMem_edgeSet hint hf)

@[simp]
theorem kind_toGraph (e : G.Ear H) : e.toGraph.kind = e.kind.toGraph := by
  cases e <;> simp [toGraph]

@[simp]
theorem toWalk_toGraph (e : G.Ear H) :
    e.toGraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toGraph⟩ := by
  cases e with
  | «open» =>
      dsimp only [toGraph]
      rw [SimpleGraph.Ear.toWalk_open, Graph.Ear.toWalk_open]
  | closed =>
      dsimp only [toGraph]
      rw [SimpleGraph.Ear.toWalk_closed, Graph.Ear.toWalk_closed]

@[simp]
theorem toGraph_toGraph (e : G.Ear H) : e.toGraph.toGraph = e.toSubgraph.toGraph := by
  cases e <;> simp [toGraph]

/-- Transport commutes with adjoining a simple-graph ear. -/
@[simp]
theorem toGraph_adjoin (e : G.Ear H) : e.adjoin.toGraph = e.toGraph.add := by
  apply (Graph.Compatible.of_le_le e.adjoin.toGraph_le e.toGraph.add_le).ext
  · simp [SimpleGraph.Ear.adjoin_def]
  · simp [SimpleGraph.Ear.adjoin_def]

end Ear

namespace EarStart

/-- Transport initial ear-decomposition data to the edge-labelled graph interface. -/
@[expose]
def toGraph (s : G.EarStart H) : (Graph.ofSimpleGraph G).EarStart H.toGraph := by
  cases s with
  | vertex v =>
      exact (Subgraph.toGraph_singletonSubgraph (G := G) v).symm ▸
        Graph.EarStart.vertex ⟨v, by simp⟩
  | cycle c hc =>
      exact (SimpleGraph.Walk.toGraph_toSubgraph c).symm ▸
        Graph.EarStart.cycle c.toGraph (c.isCycle_toGraph_iff.mpr hc)

/-- Transport sends a vertex-start witness to the same vertex-start witness. -/
theorem heq_toGraph_vertex (v : V) :
    HEq (EarStart.vertex (G := G) v).toGraph
      (Graph.EarStart.vertex (G := Graph.ofSimpleGraph G) ⟨v, by simp⟩) := by
  dsimp only [toGraph]
  exact eqRec_heq _ _

/-- Transport sends a cycle-start witness to the corresponding edge-labelled cycle. -/
theorem heq_toGraph_cycle {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    HEq (EarStart.cycle c hc).toGraph
      (Graph.EarStart.cycle c.toGraph (c.isCycle_toGraph_iff.mpr hc)) := by
  dsimp only [toGraph]
  exact eqRec_heq _ _

@[simp]
theorem isCycle_toGraph (s : G.EarStart H) : s.toGraph.IsCycle ↔ s.IsCycle := by
  cases s with
  | vertex v =>
      exact Graph.EarStart.isCycle_iff_of_heq
        (Subgraph.toGraph_singletonSubgraph (G := G) v) (eqRec_heq _ _) |>.trans (by simp)
  | cycle c hc =>
      exact Graph.EarStart.isCycle_iff_of_heq
        (SimpleGraph.Walk.toGraph_toSubgraph c) (eqRec_heq _ _) |>.trans (by simp)

end EarStart

namespace EarDecomposition

/-- Transport a simple-graph ear decomposition to `Graph.ofSimpleGraph G`. -/
@[expose]
def toGraph (d : G.EarDecomposition H) :
    (Graph.ofSimpleGraph G).EarDecomposition H.toGraph where
  length := d.length
  graphAfter i := (d.subgraphAfter i).toGraph
  start := d.start.toGraph
  earAt i := ⟨(d.subgraphAfter i.castSucc).toGraph, (d.earAt i).toGraph⟩
  earAt_fst _ := rfl
  graphAfter_succ i := by simp [d.subgraphAfter_succ]
  graphAfter_last := congrArg Subgraph.toGraph d.subgraphAfter_last

@[simp]
theorem length_toGraph (d : G.EarDecomposition H) : d.toGraph.length = d.length := rfl

@[simp]
theorem graphAfter_toGraph (d : G.EarDecomposition H)
    (i : Fin (d.toGraph.length + 1)) :
    d.toGraph.graphAfter i =
      (d.subgraphAfter (Fin.cast (congrArg (fun n ↦ n + 1) (length_toGraph d)) i)).toGraph :=
  rfl

@[simp]
theorem earAt_toGraph (d : G.EarDecomposition H) (i : Fin d.toGraph.length) :
    d.toGraph.earAt i =
      ⟨(d.subgraphAfter (Fin.cast (length_toGraph d) i).castSucc).toGraph,
        (d.earAt (Fin.cast (length_toGraph d) i)).toGraph⟩ :=
  rfl

theorem kindAt_toGraph (d : G.EarDecomposition H) (i : Fin d.toGraph.length) :
    d.toGraph.kindAt i = (d.kindAt (Fin.cast (length_toGraph d) i)).toGraph := by
  rw [Graph.EarDecomposition.kindAt_eq, earAt_toGraph,
    SimpleGraph.EarDecomposition.kindAt_def, Ear.kind_toGraph]

theorem walkAt_toGraph (d : G.EarDecomposition H) (i : Fin d.toGraph.length) :
    d.toGraph.walkAt i =
      ⟨(d.walkAt (Fin.cast (length_toGraph d) i)).1,
        (d.walkAt (Fin.cast (length_toGraph d) i)).2.1,
        (d.walkAt (Fin.cast (length_toGraph d) i)).2.2.toGraph⟩ := by
  rw [Graph.EarDecomposition.walkAt_eq, earAt_toGraph,
    SimpleGraph.EarDecomposition.walkAt_def, Ear.toWalk_toGraph]

theorem heq_start_toGraph (d : G.EarDecomposition H) :
    HEq d.toGraph.start d.start.toGraph := HEq.rfl

@[simp]
theorem graphAfter_zero_toGraph (d : G.EarDecomposition H) :
    (d.subgraphAfter
      (Fin.cast (congrArg (fun n ↦ n + 1) (length_toGraph d)) 0)).toGraph =
        d.initial.toGraph :=
    (congrArg SimpleGraph.Subgraph.toGraph d.subgraphAfter_zero)

theorem initial_toGraph (d : G.EarDecomposition H) : d.toGraph.initial = d.initial.toGraph := by
  rw [Graph.EarDecomposition.initial_eq_graphAfter, graphAfter_toGraph,
    graphAfter_zero_toGraph]

@[simp]
theorem start_isCycle_toGraph (d : G.EarDecomposition H) :
    d.toGraph.start.IsCycle ↔ d.start.IsCycle := EarStart.isCycle_toGraph d.start

@[simp]
theorem isVertexStart_toGraph (d : G.EarDecomposition H) :
    d.toGraph.IsVertexStart ↔ ¬ d.start.IsCycle := by
  rw [Graph.EarDecomposition.isVertexStart_iff_not_start_isCycle, start_isCycle_toGraph]

@[simp]
theorem isOpen_toGraph (d : G.EarDecomposition H) : d.toGraph.IsOpen ↔ d.IsOpen := by
  rw [Graph.EarDecomposition.isOpen_iff, SimpleGraph.EarDecomposition.isOpen_iff,
    start_isCycle_toGraph]
  constructor
  · rintro ⟨hstart, hkinds⟩
    refine ⟨hstart, fun i ↦ ?_⟩
    have hkind := hkinds (Fin.cast (length_toGraph d).symm i)
    rw [kindAt_toGraph] at hkind
    exact (EarKind.toGraph_eq_open _).mp hkind
  · rintro ⟨hstart, hkinds⟩
    refine ⟨hstart, fun i ↦ ?_⟩
    rw [kindAt_toGraph]
    exact (EarKind.toGraph_eq_open _).mpr (hkinds _)

/-- Transporting a prefix gives the corresponding prefix of the transported decomposition. -/
theorem toGraph_prefix (d : G.EarDecomposition H) (k : Fin (d.length + 1)) :
    (d.prefix k).toGraph = d.toGraph.prefix k := by
  apply Graph.EarDecomposition.ext
  · rfl
  · simp [toGraph, Graph.EarDecomposition.prefix]
  · exact HEq.rfl
  · simp [toGraph, Graph.EarDecomposition.prefix]

end EarDecomposition

end SimpleGraph

namespace Graph

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

namespace EarKind

/-- Identify edge-labelled graph ear kinds with simple-graph ear kinds. -/
@[expose]
def toSimpleGraph : Graph.EarKind → SimpleGraph.EarKind
  | .open => .open
  | .closed => .closed

@[simp] theorem toSimpleGraph_open : Graph.EarKind.open.toSimpleGraph = .open := rfl
@[simp] theorem toSimpleGraph_closed : Graph.EarKind.closed.toSimpleGraph = .closed := rfl

@[simp]
theorem toSimpleGraph_eq_open (kind : Graph.EarKind) :
    kind.toSimpleGraph = .open ↔ kind = .open := by
  cases kind <;> simp

@[simp]
theorem toSimpleGraph_eq_closed (kind : Graph.EarKind) :
    kind.toSimpleGraph = .closed ↔ kind = .closed := by
  cases kind <;> simp

@[simp]
theorem toSimpleGraph_toGraph (kind : SimpleGraph.EarKind) :
    kind.toGraph.toSimpleGraph = kind := by cases kind <;> rfl

@[simp]
theorem toGraph_toSimpleGraph (kind : Graph.EarKind) :
    kind.toSimpleGraph.toGraph = kind := by cases kind <;> rfl

end EarKind

namespace Ear

/-- Transport an ear in a subgraph of `Graph.ofSimpleGraph G` to the simple-graph interface. -/
@[expose]
def toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    G.Ear (K.toSubgraphOfSimpleGraph e.base_le) := by
  cases e with
  | «open» _ p hp hu hv huv hint hedge =>
      exact .open p.toSimpleGraph (p.isPath_toSimpleGraph_iff.mpr hp)
        (by simpa) (by simpa) huv
        (by simpa only [Graph.Walk.support_toSimpleGraph, verts_toSubgraphOfSimpleGraph]
          using hint)
        (by simpa only [Graph.Walk.edges_toSimpleGraph, edgeSet_toSubgraphOfSimpleGraph]
          using hedge)
  | closed _ c hc hu hint _ =>
      exact .closed c.toSimpleGraph (c.isCycle_toSimpleGraph_iff.mpr hc)
        (by simpa)
        (by simpa only [Graph.Walk.support_toSimpleGraph, verts_toSubgraphOfSimpleGraph] using hint)

@[simp]
theorem kind_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.kind = e.kind.toSimpleGraph := by
  cases e <;> simp [toSimpleGraph]

@[simp]
theorem toWalk_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toSimpleGraph⟩ := by
  cases e with
  | «open» =>
      dsimp only [toSimpleGraph]
      rw [Graph.Ear.toWalk_open, SimpleGraph.Ear.toWalk_open]
  | closed =>
      dsimp only [toSimpleGraph]
      rw [Graph.Ear.toWalk_closed, SimpleGraph.Ear.toWalk_closed]

@[simp]
theorem toSubgraph_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.toSubgraph.toGraph = e.toGraph := by
  cases e with
  | «open» =>
      dsimp only [toSimpleGraph]
      rw [SimpleGraph.Ear.toSubgraph_open,
        SimpleGraph.Walk.toGraph_toSubgraph, Graph.Walk.toGraph_toSimpleGraph,
        Graph.Ear.toGraph_open]
  | closed =>
      dsimp only [toSimpleGraph]
      rw [SimpleGraph.Ear.toSubgraph_closed,
        SimpleGraph.Walk.toGraph_toSubgraph, Graph.Walk.toGraph_toSimpleGraph,
        Graph.Ear.toGraph_closed]

/-- Converting an ear to the simple-graph interface and back preserves the graph obtained by
adjoining it. -/
theorem add_toGraph_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.toGraph.add = e.add := by
  have hbase : (K.toSubgraphOfSimpleGraph e.base_le).toGraph = K := by simp
  have htrace : e.toSimpleGraph.toGraph.toGraph = e.toGraph := by
    rw [SimpleGraph.Ear.toGraph_toGraph, e.toSubgraph_toSimpleGraph]
  apply le_antisymm
  · rw [Graph.Ear.add_le_iff]
    exact ⟨hbase.le.trans e.base_le_add, htrace.le.trans e.toGraph_le_add⟩
  · rw [Graph.Ear.add_le_iff]
    exact ⟨hbase.ge.trans e.toSimpleGraph.toGraph.base_le_add,
      htrace.ge.trans e.toSimpleGraph.toGraph.toGraph_le_add⟩

/-- Transport to the simple-graph interface commutes with adjoining an ear. -/
@[simp]
theorem toSubgraphOfSimpleGraph_add (e : (Graph.ofSimpleGraph G).Ear K) :
    e.add.toSubgraphOfSimpleGraph e.add_le = e.toSimpleGraph.adjoin := by
  apply SimpleGraph.Subgraph.toGraph_injective G
  dsimp only
  rw [SimpleGraph.Ear.toGraph_adjoin, e.add_toGraph_toSimpleGraph,
    Graph.toGraph_toSubgraphOfSimpleGraph]

/-- Transporting a simple-graph ear to `Graph` and back preserves it after reindexing its base. -/
@[simp]
theorem toSimpleGraph_toGraph (e : G.Ear H) :
    e.toGraph.toSimpleGraph.copy H.toSubgraphOfSimpleGraph_toGraph = e := by
  apply SimpleGraph.Ear.ext
  rw [SimpleGraph.Ear.toWalk_copy, toWalk_toSimpleGraph, SimpleGraph.Ear.toWalk_toGraph,
    SimpleGraph.Walk.toSimpleGraph_toGraph]

end Ear

namespace EarStart

/-- Transport initial ear-decomposition data from `Graph.ofSimpleGraph G` to the simple-graph
interface. -/
@[expose]
def toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    G.EarStart (K.toSubgraphOfSimpleGraph s.le) := by
  cases s with
  | vertex v =>
      exact (toSubgraphOfSimpleGraph_noEdge_singleton v.1 _).symm ▸
        SimpleGraph.EarStart.vertex v.1
  | cycle p hp =>
      exact (SimpleGraph.Walk.toSubgraphOfSimpleGraph_walkGraph p hp.start_mem).symm ▸
        SimpleGraph.EarStart.cycle p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)

/-- Reverse transport sends a vertex-start witness to the same vertex. -/
theorem heq_toSimpleGraph_vertex (v : V(Graph.ofSimpleGraph G)) :
    HEq (Graph.EarStart.vertex v).toSimpleGraph
      (SimpleGraph.EarStart.vertex (G := G) v.1) := by
  dsimp only [toSimpleGraph]
  exact eqRec_heq _ _

/-- Reverse transport sends a cycle-start witness to the corresponding simple-graph cycle. -/
theorem heq_toSimpleGraph_cycle {u : V}
    (p : (Graph.ofSimpleGraph G).Walk u u) (hp : p.IsCycle) :
    HEq (Graph.EarStart.cycle p hp).toSimpleGraph
      (SimpleGraph.EarStart.cycle p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)) := by
  dsimp only [toSimpleGraph]
  exact eqRec_heq _ _

@[simp]
theorem isCycle_toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    s.toSimpleGraph.IsCycle ↔ s.IsCycle := by
  cases s with
  | vertex v =>
      exact SimpleGraph.EarStart.isCycle_iff_of_heq
        (toSubgraphOfSimpleGraph_noEdge_singleton v.1 _) (eqRec_heq _ _) |>.trans (by simp)
  | cycle p hp =>
      exact SimpleGraph.EarStart.isCycle_iff_of_heq
        (SimpleGraph.Walk.toSubgraphOfSimpleGraph_walkGraph p hp.start_mem)
        (eqRec_heq _ _) |>.trans (by simp)

end EarStart

namespace EarDecomposition

/-- Transport an ear decomposition of a subgraph of `Graph.ofSimpleGraph G` to the simple-graph
interface. -/
@[expose]
def toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    G.EarDecomposition (K.toSubgraphOfSimpleGraph d.final_le) where
  length := d.length
  subgraphAfter i := (d.graphAfter i).toSubgraphOfSimpleGraph (d.graphAfter_le i)
  start := d.start.toSimpleGraph
  earAt i :=
    (d.earAt i).2.toSimpleGraph.copy <|
      toSubgraphOfSimpleGraph_congr (d.earAt_fst i)
        (d.earAt i).2.base_le (d.graphAfter_le i.castSucc)
  subgraphAfter_succ i := by
    rw [toSubgraphOfSimpleGraph_congr (d.graphAfter_succ i)
      (d.graphAfter_le i.succ) (d.earAt i).2.add_le,
      (d.earAt i).2.toSubgraphOfSimpleGraph_add,
      SimpleGraph.Ear.adjoin_def, SimpleGraph.Ear.adjoin_copy]
    exact congrArg (fun L ↦ L ⊔ (d.earAt i).2.toSimpleGraph.toSubgraph) <|
      toSubgraphOfSimpleGraph_congr (d.earAt_fst i)
        (d.earAt i).2.base_le (d.graphAfter_le i.castSucc)
  subgraphAfter_last :=
    toSubgraphOfSimpleGraph_congr d.graphAfter_last
      (d.graphAfter_le (Fin.last d.length)) d.final_le

@[simp]
theorem length_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.length = d.length := rfl

@[simp]
theorem subgraphAfter_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin (d.toSimpleGraph.length + 1)) :
    d.toSimpleGraph.subgraphAfter i =
      Graph.toSubgraphOfSimpleGraph
        (d.graphAfter (Fin.cast (congrArg (fun n ↦ n + 1) (length_toSimpleGraph d)) i))
        (d.graphAfter_le _) :=
  rfl

@[simp]
theorem earAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.toSimpleGraph.length) :
    d.toSimpleGraph.earAt i =
      (d.earAt (Fin.cast (length_toSimpleGraph d) i)).2.toSimpleGraph.copy
        (toSubgraphOfSimpleGraph_congr (d.earAt_fst _)
          (d.earAt _).2.base_le (d.graphAfter_le _)) :=
  rfl

private theorem kindAt_toSimpleGraph_cast (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) :
    d.toSimpleGraph.kindAt (Fin.cast (length_toSimpleGraph d).symm i) =
      (d.kindAt i).toSimpleGraph := by
  simp only [SimpleGraph.EarDecomposition.kindAt_def, Graph.EarDecomposition.kindAt_eq,
    toSimpleGraph, Fin.cast_eq_self, SimpleGraph.Ear.kind_copy, Ear.kind_toSimpleGraph]

private theorem walkAt_toSimpleGraph_cast (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) :
    d.toSimpleGraph.walkAt (Fin.cast (length_toSimpleGraph d).symm i) =
      ⟨(d.walkAt i).1, (d.walkAt i).2.1, (d.walkAt i).2.2.toSimpleGraph⟩ := by
  rw [SimpleGraph.EarDecomposition.walkAt_def, Graph.EarDecomposition.walkAt_eq]
  simp only [toSimpleGraph, Fin.cast_eq_self, SimpleGraph.Ear.toWalk_copy,
    Ear.toWalk_toSimpleGraph]

@[simp]
theorem kindAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.toSimpleGraph.length) :
    d.toSimpleGraph.kindAt i =
      (d.kindAt (Fin.cast (length_toSimpleGraph d) i)).toSimpleGraph := by
  have h := kindAt_toSimpleGraph_cast d (Fin.cast (length_toSimpleGraph d) i)
  rw [Fin.cast_cast] at h
  exact h

@[simp]
theorem walkAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.toSimpleGraph.length) :
    d.toSimpleGraph.walkAt i =
      ⟨(d.walkAt (Fin.cast (length_toSimpleGraph d) i)).1,
        (d.walkAt (Fin.cast (length_toSimpleGraph d) i)).2.1,
        (d.walkAt (Fin.cast (length_toSimpleGraph d) i)).2.2.toSimpleGraph⟩ := by
  have h := walkAt_toSimpleGraph_cast d (Fin.cast (length_toSimpleGraph d) i)
  rw [Fin.cast_cast] at h
  exact h

theorem heq_start_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    HEq d.toSimpleGraph.start d.start.toSimpleGraph := HEq.rfl

@[simp]
theorem initial_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.initial =
      (d.graphAfter 0).toSubgraphOfSimpleGraph (d.graphAfter_le 0) := by
  rw [← SimpleGraph.EarDecomposition.subgraphAfter_zero]
  exact d.subgraphAfter_toSimpleGraph 0

@[simp]
theorem start_isCycle_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.start.IsCycle ↔ d.start.IsCycle := EarStart.isCycle_toSimpleGraph d.start

@[simp]
theorem isOpen_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.IsOpen ↔ d.IsOpen := by
  rw [SimpleGraph.EarDecomposition.isOpen_iff, Graph.EarDecomposition.isOpen_iff,
    start_isCycle_toSimpleGraph]
  constructor
  · rintro ⟨hstart, hkinds⟩
    refine ⟨hstart, fun i ↦ ?_⟩
    have hkind := hkinds (Fin.cast (length_toSimpleGraph d).symm i)
    rw [kindAt_toSimpleGraph_cast] at hkind
    exact (EarKind.toSimpleGraph_eq_open _).mp hkind
  · rintro ⟨hstart, hkinds⟩
    refine ⟨hstart, fun i ↦ ?_⟩
    have hkind := hkinds (Fin.cast (length_toSimpleGraph d) i)
    have htransport := kindAt_toSimpleGraph_cast d (Fin.cast (length_toSimpleGraph d) i)
    rw [Fin.cast_cast] at htransport
    exact htransport.trans ((EarKind.toSimpleGraph_eq_open _).mpr hkind)

/-- Transporting a prefix gives the corresponding prefix of the transported decomposition. -/
theorem toSimpleGraph_prefix (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (k : Fin (d.length + 1)) :
    HEq (d.prefix k).toSimpleGraph (d.toSimpleGraph.prefix k) := by
  rfl

/-- A full edge-labelled decomposition transports to the top simple-graph subgraph. -/
@[expose]
def toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    G.EarDecomposition (⊤ : G.Subgraph) :=
  d.toSimpleGraph.copy toSubgraphOfSimpleGraph_ofSimpleGraph

theorem toSimpleGraphTop_eq_copy
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    d.toSimpleGraphTop = d.toSimpleGraph.copy toSubgraphOfSimpleGraph_ofSimpleGraph := rfl

@[simp]
theorem initial_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    d.toSimpleGraphTop.initial =
      (d.graphAfter 0).toSubgraphOfSimpleGraph (d.graphAfter_le 0) := by
  rw [toSimpleGraphTop_eq_copy, SimpleGraph.EarDecomposition.initial_copy,
    initial_toSimpleGraph]

end EarDecomposition

end Graph

namespace SimpleGraph.EarDecomposition

variable {V : Type u} {G : SimpleGraph V}

/-- A full simple-graph decomposition transports to a full decomposition of its edge-labelled
graph. -/
@[expose]
def toGraphTop (d : G.EarDecomposition (⊤ : G.Subgraph)) :
    (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G) :=
  d.toGraph.copy SimpleGraph.Subgraph.toGraph_top

theorem toGraphTop_eq_copy (d : G.EarDecomposition (⊤ : G.Subgraph)) :
    d.toGraphTop = d.toGraph.copy SimpleGraph.Subgraph.toGraph_top := rfl

end SimpleGraph.EarDecomposition
