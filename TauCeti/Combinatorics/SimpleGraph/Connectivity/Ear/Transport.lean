/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.OfSimpleGraph

/-!
# Transporting ear decompositions of simple graphs

This file transports ear data from the subgraph interface of a simple graph `G` to the
edge-labelled interface of `Graph.ofSimpleGraph G`, complementing the transport
`Graph.EarDecomposition.toSimpleGraph` in the other direction. The maps preserve lengths, stage
graphs, displayed ears, walks, kinds, initial data, prefix decompositions, and openness.
`SimpleGraph.EarDecomposition.toGraphTop` and `Graph.EarDecomposition.toSimpleGraphTop` specialise
both transports to decompositions of the whole graph. The two transports are mutually inverse up
to reindexing the final graph along the subgraph round trips.
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
theorem toGraph_eq_open_iff {kind : SimpleGraph.EarKind} : kind.toGraph = .open ↔ kind = .open := by
  cases kind <;> simp

@[simp]
theorem toGraph_eq_closed_iff {kind : SimpleGraph.EarKind} :
    kind.toGraph = .closed ↔ kind = .closed := by
  cases kind <;> simp

end EarKind

namespace Ear

/-- Transport a simple-graph ear to the edge-labelled graph interface. -/
def toGraph (e : G.Ear H) : (Graph.ofSimpleGraph G).Ear H.toGraph := by
  cases e with
  | «open» p hp hu hv huv hint hedge =>
      exact .open H.toGraph_le_ofSimpleGraph p.toGraph (p.isPath_toGraph_iff.mpr hp)
        (by simpa) (by simpa) huv
        (by simpa only [SimpleGraph.Walk.support_toGraph, Subgraph.vertexSet_toGraph] using hint)
        (by simpa only [SimpleGraph.Walk.edges_toGraph, Subgraph.edgeSet_toGraph] using hedge)
  | closed c hc hu hint =>
      exact .closed H.toGraph_le_ofSimpleGraph c.toGraph (c.isCycle_toGraph_iff.mpr hc)
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
  apply (Graph.Compatible.of_le_le e.adjoin.toGraph_le_ofSimpleGraph e.toGraph.add_le).ext
  · simp [SimpleGraph.Ear.adjoin_def]
  · simp [SimpleGraph.Ear.adjoin_def]

end Ear

namespace EarStart

/-- Transport initial ear-decomposition data to the edge-labelled graph interface. -/
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

private theorem heq_toGraph_of_heq {H₁ H₂ : G.Subgraph} {s₁ : G.EarStart H₁}
    {s₂ : G.EarStart H₂} (hH : H₁ = H₂) (hs : HEq s₁ s₂) : HEq s₁.toGraph s₂.toGraph := by
  subst hH
  cases eq_of_heq hs
  rfl

end EarStart

namespace EarDecomposition

/-- Transport a simple-graph ear decomposition to `Graph.ofSimpleGraph G`. -/
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
theorem length_toGraph (d : G.EarDecomposition H) : d.toGraph.length = d.length := (rfl)

@[simp]
theorem graphAfter_toGraph (d : G.EarDecomposition H)
    (i : Fin (d.toGraph.length + 1)) :
    d.toGraph.graphAfter i =
      (d.subgraphAfter (Fin.cast (congrArg (fun n ↦ n + 1) (length_toGraph d)) i)).toGraph :=
  (rfl)

@[simp]
theorem earAt_toGraph (d : G.EarDecomposition H) (i : Fin d.toGraph.length) :
    d.toGraph.earAt i =
      ⟨(d.subgraphAfter (Fin.cast (length_toGraph d) i).castSucc).toGraph,
        (d.earAt (Fin.cast (length_toGraph d) i)).toGraph⟩ :=
  (rfl)

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

theorem initial_toGraph (d : G.EarDecomposition H) : d.toGraph.initial = d.initial.toGraph := by
  rw [Graph.EarDecomposition.initial_eq_graphAfter,
    ← SimpleGraph.EarDecomposition.subgraphAfter_zero]
  exact d.graphAfter_toGraph 0

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
    exact EarKind.toGraph_eq_open_iff.mp hkind
  · rintro ⟨hstart, hkinds⟩
    refine ⟨hstart, fun i ↦ ?_⟩
    rw [kindAt_toGraph]
    exact EarKind.toGraph_eq_open_iff.mpr (hkinds _)

/-- Transporting a prefix gives the corresponding prefix of the transported decomposition. -/
theorem toGraph_prefix (d : G.EarDecomposition H) (k : Fin (d.length + 1)) :
    (d.prefix k).toGraph =
      (d.toGraph.prefix (Fin.cast (congrArg (· + 1) (length_toGraph d).symm) k)).copy
        (d.graphAfter_toGraph _) := by
  have hlen : (d.prefix k).toGraph.length =
      ((d.toGraph.prefix (Fin.cast (congrArg (· + 1) (length_toGraph d).symm) k)).copy
        (d.graphAfter_toGraph _)).length := by simp
  refine Graph.EarDecomposition.ext _ _ hlen ?_ ?_
  · refine (heq_start_toGraph _).trans ?_
    rw [SimpleGraph.EarDecomposition.start_prefix]
    exact (heq_start_toGraph d).symm.trans
      ((Graph.EarDecomposition.heq_start_prefix _ _).symm.trans
        (Graph.EarDecomposition.heq_start_copy _ _).symm)
  · rw [Fin.heq_fun_iff hlen]
    intro j
    rw [Graph.EarDecomposition.earAt_copy]
    refine Eq.trans ?_ (d.toGraph.earAt_prefix _ ⟨j, by simpa using j.2⟩).symm
    simp only [earAt_toGraph]
    congr 2

end EarDecomposition

end SimpleGraph

namespace Graph

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

namespace EarKind

@[simp]
theorem toGraph_toSimpleGraph (kind : Graph.EarKind) :
    kind.toSimpleGraph.toGraph = kind := by cases kind <;> simp

end EarKind

namespace Ear

@[simp]
theorem toGraph_toSubgraph_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.toSubgraph.toGraph = e.toGraph := by
  rw [← e.toSimpleGraphSubgraph_toGraph e.toGraph_le, Graph.toGraph_toSimpleGraphSubgraph]

/-- Converting an ear to the simple-graph interface and back preserves the graph obtained by
adjoining it. -/
@[simp]
theorem add_toGraph_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.toGraph.add = e.add := by
  have hbase : (K.toSimpleGraphSubgraph e.base_le).toGraph = K := by simp
  have htrace : e.toSimpleGraph.toGraph.toGraph = e.toGraph := by
    rw [SimpleGraph.Ear.toGraph_toGraph, e.toGraph_toSubgraph_toSimpleGraph]
  apply le_antisymm
  · rw [Graph.Ear.add_le_iff]
    exact ⟨hbase.le.trans e.base_le_add, htrace.le.trans e.toGraph_le_add⟩
  · rw [Graph.Ear.add_le_iff]
    exact ⟨hbase.ge.trans e.toSimpleGraph.toGraph.base_le_add,
      htrace.ge.trans e.toSimpleGraph.toGraph.toGraph_le_add⟩

/-- Transporting an ear to the simple-graph interface and back recovers it, over the recovered
base graph. -/
theorem heq_toGraph_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    HEq e.toSimpleGraph.toGraph e := by
  have key : ∀ {L : Graph V (Sym2 V)} (_ : L = K) (f : (Graph.ofSimpleGraph G).Ear L),
      f.toWalk = e.toWalk → HEq f e := by
    rintro _ rfl f hwalk
    exact heq_of_eq (Graph.Ear.ext f e hwalk)
  refine key (by simp) _ ?_
  rw [SimpleGraph.Ear.toWalk_toGraph, toWalk_toSimpleGraph, Graph.Walk.toGraph_toSimpleGraph]

end Ear

namespace EarStart

private theorem heq_toSimpleGraph_of_heq {K L : Graph V (Sym2 V)}
    {s : (Graph.ofSimpleGraph G).EarStart K} {t : (Graph.ofSimpleGraph G).EarStart L}
    (hKL : K = L) (hst : HEq s t) : HEq s.toSimpleGraph t.toSimpleGraph := by
  subst hKL
  cases eq_of_heq hst
  rfl

end EarStart

namespace EarDecomposition

private theorem walkAt_prefix' (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (k : Fin (d.length + 1)) (j : Fin (d.prefix k).length) :
    (d.prefix k).walkAt j =
      d.walkAt (Fin.castLE (Nat.le_of_lt_succ k.isLt) (Fin.cast (d.length_prefix k) j)) := by
  rw [Graph.EarDecomposition.walkAt_eq, Graph.EarDecomposition.walkAt_eq,
    ← d.earAt_prefix k]
  rfl

/-- Transporting a prefix gives the corresponding prefix of the transported decomposition. -/
theorem toSimpleGraph_prefix (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (k : Fin (d.length + 1)) :
    (d.prefix k).toSimpleGraph =
      (d.toSimpleGraph.prefix (Fin.cast (congrArg (· + 1) (length_toSimpleGraph d).symm) k)).copy
        (show d.toSimpleGraph.subgraphAfter _ =
          (d.graphAfter k).toSimpleGraphSubgraph (d.prefix k).final_le from rfl) := by
  have hlen : (d.prefix k).toSimpleGraph.length =
      ((d.toSimpleGraph.prefix (Fin.cast (congrArg (· + 1) (length_toSimpleGraph d).symm) k)).copy
        (show d.toSimpleGraph.subgraphAfter _ =
          (d.graphAfter k).toSimpleGraphSubgraph (d.prefix k).final_le from rfl)).length := by
    rw [SimpleGraph.EarDecomposition.length_copy, SimpleGraph.EarDecomposition.length_prefix,
      length_toSimpleGraph, Graph.EarDecomposition.length_prefix, Fin.val_cast]
  refine SimpleGraph.EarDecomposition.ext hlen ?_ ?_ fun i ↦ ?_
  · rw [SimpleGraph.EarDecomposition.initial_copy, SimpleGraph.EarDecomposition.initial_prefix,
      initial_toSimpleGraph, initial_toSimpleGraph]
    exact toSimpleGraphSubgraph_congr (by simpa using d.initial_prefix k) _ _
  · refine (EarStart.heq_toSimpleGraph_of_heq (by simpa using d.initial_prefix k)
      (d.heq_start_prefix k)).trans ?_
    rw [SimpleGraph.EarDecomposition.start_copy, SimpleGraph.EarDecomposition.start_prefix]
    exact .rfl
  · refine (walkAt_toSimpleGraph (d.prefix k) i).trans ?_
    refine (congrArg (fun p ↦ (⟨p.1, p.2.1, p.2.2.toSimpleGraph⟩ : Σ x y, G.Walk x y))
      (walkAt_prefix' d k i)).trans ?_
    exact ((SimpleGraph.EarDecomposition.walkAt_copy _ _ _).trans
      ((SimpleGraph.EarDecomposition.walkAt_prefix _ _ _).trans (walkAt_toSimpleGraph d _))).symm

/-- A full edge-labelled decomposition transports to the top simple-graph subgraph. -/
def toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    G.EarDecomposition (⊤ : G.Subgraph) :=
  d.toSimpleGraph.copy (toSimpleGraphSubgraph_ofSimpleGraph _)

theorem toSimpleGraphTop_def
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    d.toSimpleGraphTop = d.toSimpleGraph.copy (toSimpleGraphSubgraph_ofSimpleGraph _) := (rfl)

@[simp]
theorem length_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    d.toSimpleGraphTop.length = d.length := by
  rw [toSimpleGraphTop_def, SimpleGraph.EarDecomposition.length_copy, length_toSimpleGraph]

@[simp]
theorem initial_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    d.toSimpleGraphTop.initial =
      (d.graphAfter 0).toSimpleGraphSubgraph (d.graphAfter_le 0) := by
  rw [toSimpleGraphTop_def, SimpleGraph.EarDecomposition.initial_copy,
    initial_toSimpleGraph]

@[simp]
theorem isOpen_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    d.toSimpleGraphTop.IsOpen ↔ d.IsOpen := by
  rw [toSimpleGraphTop_def, SimpleGraph.EarDecomposition.isOpen_copy, isOpen_toSimpleGraph]

@[simp]
theorem subgraphAfter_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G))
    (i : Fin (d.toSimpleGraphTop.length + 1)) :
    d.toSimpleGraphTop.subgraphAfter i =
      Graph.toSimpleGraphSubgraph
        (d.graphAfter (Fin.cast (congrArg (fun n ↦ n + 1) (length_toSimpleGraphTop d)) i))
        (d.graphAfter_le _) :=
  d.subgraphAfter_toSimpleGraph _

@[simp]
theorem earAt_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G))
    (i : Fin d.toSimpleGraphTop.length) :
    d.toSimpleGraphTop.earAt i =
      (d.earAt (Fin.cast (length_toSimpleGraphTop d) i)).2.toSimpleGraph.copy (by
        rw [subgraphAfter_toSimpleGraphTop]
        exact toSimpleGraphSubgraph_congr (by rw [d.earAt_fst]; congr 1) _ _) :=
  d.earAt_toSimpleGraph _

@[simp]
theorem kindAt_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G))
    (i : Fin d.toSimpleGraphTop.length) :
    d.toSimpleGraphTop.kindAt i =
      (d.kindAt (Fin.cast (length_toSimpleGraphTop d) i)).toSimpleGraph := by
  rw [SimpleGraph.EarDecomposition.kindAt_def, earAt_toSimpleGraphTop, SimpleGraph.Ear.kind_copy,
    Ear.kind_toSimpleGraph, Graph.EarDecomposition.kindAt_eq]

@[simp]
theorem walkAt_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G))
    (i : Fin d.toSimpleGraphTop.length) :
    d.toSimpleGraphTop.walkAt i =
      ⟨(d.walkAt (Fin.cast (length_toSimpleGraphTop d) i)).1,
        (d.walkAt (Fin.cast (length_toSimpleGraphTop d) i)).2.1,
        (d.walkAt (Fin.cast (length_toSimpleGraphTop d) i)).2.2.toSimpleGraph⟩ := by
  rw [SimpleGraph.EarDecomposition.walkAt_def, earAt_toSimpleGraphTop,
    SimpleGraph.Ear.toWalk_copy, Ear.toWalk_toSimpleGraph, Graph.EarDecomposition.walkAt_eq]

theorem heq_start_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    HEq d.toSimpleGraphTop.start d.start.toSimpleGraph :=
  .rfl

@[simp]
theorem start_isCycle_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    d.toSimpleGraphTop.start.IsCycle ↔ d.start.IsCycle :=
  d.start.isCycle_toSimpleGraph

end EarDecomposition

end Graph


namespace SimpleGraph.EarDecomposition

variable {V : Type u} {G : SimpleGraph V}

/-- A full simple-graph decomposition transports to a full decomposition of its edge-labelled
graph. -/
def toGraphTop (d : G.EarDecomposition (⊤ : G.Subgraph)) :
    (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G) :=
  d.toGraph.copy SimpleGraph.Subgraph.toGraph_top

theorem toGraphTop_def (d : G.EarDecomposition (⊤ : G.Subgraph)) :
    d.toGraphTop = d.toGraph.copy SimpleGraph.Subgraph.toGraph_top := (rfl)

@[simp]
theorem length_toGraphTop (d : G.EarDecomposition (⊤ : G.Subgraph)) :
    d.toGraphTop.length = d.length := by
  rw [toGraphTop_def, Graph.EarDecomposition.length_copy,
    SimpleGraph.EarDecomposition.length_toGraph]

theorem initial_toGraphTop (d : G.EarDecomposition (⊤ : G.Subgraph)) :
    d.toGraphTop.initial = d.initial.toGraph := by
  rw [toGraphTop_def, Graph.EarDecomposition.initial_copy,
    SimpleGraph.EarDecomposition.initial_toGraph]

@[simp]
theorem isOpen_toGraphTop (d : G.EarDecomposition (⊤ : G.Subgraph)) :
    d.toGraphTop.IsOpen ↔ d.IsOpen := by
  rw [toGraphTop_def, Graph.EarDecomposition.isOpen_copy,
    SimpleGraph.EarDecomposition.isOpen_toGraph]

@[simp]
theorem graphAfter_toGraphTop (d : G.EarDecomposition (⊤ : G.Subgraph))
    (i : Fin (d.toGraphTop.length + 1)) :
    d.toGraphTop.graphAfter i =
      (d.subgraphAfter (Fin.cast (congrArg (fun n ↦ n + 1) (length_toGraphTop d)) i)).toGraph :=
  (Graph.EarDecomposition.graphAfter_copy d.toGraph _ i).trans (d.graphAfter_toGraph _)

@[simp]
theorem earAt_toGraphTop (d : G.EarDecomposition (⊤ : G.Subgraph)) (i : Fin d.toGraphTop.length) :
    d.toGraphTop.earAt i =
      ⟨(d.subgraphAfter (Fin.cast (length_toGraphTop d) i).castSucc).toGraph,
        (d.earAt (Fin.cast (length_toGraphTop d) i)).toGraph⟩ :=
  (Graph.EarDecomposition.earAt_copy d.toGraph _ i).trans (d.earAt_toGraph _)

theorem kindAt_toGraphTop (d : G.EarDecomposition (⊤ : G.Subgraph)) (i : Fin d.toGraphTop.length) :
    d.toGraphTop.kindAt i = (d.kindAt (Fin.cast (length_toGraphTop d) i)).toGraph :=
  (Graph.EarDecomposition.kindAt_copy d.toGraph _ i).trans (d.kindAt_toGraph _)

theorem walkAt_toGraphTop (d : G.EarDecomposition (⊤ : G.Subgraph)) (i : Fin d.toGraphTop.length) :
    d.toGraphTop.walkAt i =
      ⟨(d.walkAt (Fin.cast (length_toGraphTop d) i)).1,
        (d.walkAt (Fin.cast (length_toGraphTop d) i)).2.1,
        (d.walkAt (Fin.cast (length_toGraphTop d) i)).2.2.toGraph⟩ :=
  (Graph.EarDecomposition.walkAt_copy d.toGraph _ i).trans (d.walkAt_toGraph _)

theorem heq_start_toGraphTop (d : G.EarDecomposition (⊤ : G.Subgraph)) :
    HEq d.toGraphTop.start d.start.toGraph :=
  (Graph.EarDecomposition.heq_start_copy d.toGraph _).trans d.heq_start_toGraph

@[simp]
theorem start_isCycle_toGraphTop (d : G.EarDecomposition (⊤ : G.Subgraph)) :
    d.toGraphTop.start.IsCycle ↔ d.start.IsCycle :=
  (Graph.EarDecomposition.start_isCycle_copy d.toGraph _).trans d.start_isCycle_toGraph

@[simp]
theorem isVertexStart_toGraphTop (d : G.EarDecomposition (⊤ : G.Subgraph)) :
    d.toGraphTop.IsVertexStart ↔ ¬ d.start.IsCycle :=
  (Graph.EarDecomposition.isVertexStart_copy d.toGraph _).trans d.isVertexStart_toGraph

end SimpleGraph.EarDecomposition

/-! ### Round trips -/

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

namespace EarKind

@[simp]
theorem toSimpleGraph_toGraph (kind : SimpleGraph.EarKind) :
    kind.toGraph.toSimpleGraph = kind := by cases kind <;> simp

end EarKind

namespace Ear

/-- Transporting a simple-graph ear to `Graph` and back preserves it after reindexing its base. -/
@[simp]
theorem copy_toSimpleGraph_toGraph (e : G.Ear H) :
    e.toGraph.toSimpleGraph.copy (H.toSimpleGraphSubgraph_toGraph _) = e := by
  apply SimpleGraph.Ear.ext
  rw [SimpleGraph.Ear.toWalk_copy, Graph.Ear.toWalk_toSimpleGraph, toWalk_toGraph,
    SimpleGraph.Walk.toSimpleGraph_toGraph]

private theorem heq_toGraph_copy {H' : G.Subgraph} (e : G.Ear H) (h : H = H') :
    HEq (e.copy h).toGraph e.toGraph := by
  subst h
  rw [copy_rfl]

end Ear

namespace EarStart

/-- Transporting initial data to `Graph` and back recovers it, over the recovered subgraph. -/
theorem heq_toSimpleGraph_toGraph (s : G.EarStart H) : HEq s.toGraph.toSimpleGraph s := by
  cases s with
  | vertex v =>
      exact (Graph.EarStart.heq_toSimpleGraph_of_heq (Subgraph.toGraph_singletonSubgraph v)
        (heq_toGraph_vertex v)).trans (Graph.EarStart.heq_toSimpleGraph_vertex _)
  | cycle c hc =>
      refine (Graph.EarStart.heq_toSimpleGraph_of_heq (SimpleGraph.Walk.toGraph_toSubgraph c)
        (heq_toGraph_cycle c hc)).trans
        ((Graph.EarStart.heq_toSimpleGraph_cycle _ _).trans ?_)
      have key : ∀ (c' : G.Walk _ _) (hc' : c'.IsCycle), c' = c →
          HEq (EarStart.cycle c' hc') (EarStart.cycle c hc) := by
        rintro _ _ rfl
        rfl
      exact key _ _ (SimpleGraph.Walk.toSimpleGraph_toGraph c)

end EarStart

namespace EarDecomposition

/-- Transporting a decomposition to `Graph` and back recovers it after reindexing its final
subgraph. -/
@[simp]
theorem copy_toSimpleGraph_toGraph (d : G.EarDecomposition H) :
    d.toGraph.toSimpleGraph.copy (H.toSimpleGraphSubgraph_toGraph _) = d := by
  refine SimpleGraph.EarDecomposition.ext (by simp) (by simp) ?_ fun i ↦ ?_
  · rw [start_copy]
    exact ((Graph.EarStart.heq_toSimpleGraph_of_heq (by simp) d.heq_start_toGraph).trans
        d.start.heq_toSimpleGraph_toGraph)
  · refine (walkAt_copy _ _ _).trans
      ((Graph.EarDecomposition.walkAt_toSimpleGraph d.toGraph i).trans ?_)
    refine (congrArg (fun p ↦ (⟨p.1, p.2.1, p.2.2.toSimpleGraph⟩ : Σ x y, G.Walk x y))
      (walkAt_toGraph d i)).trans ?_
    simp only [SimpleGraph.Walk.toSimpleGraph_toGraph]
    congr 1

/-- Transporting a full decomposition to `Graph` and back recovers it. -/
@[simp]
theorem toSimpleGraphTop_toGraphTop (d : G.EarDecomposition (⊤ : G.Subgraph)) :
    d.toGraphTop.toSimpleGraphTop = d := by
  refine SimpleGraph.EarDecomposition.ext (by simp) (by simp) ?_ fun i ↦ ?_
  · exact (Graph.EarDecomposition.heq_start_toSimpleGraphTop _).trans
      ((Graph.EarStart.heq_toSimpleGraph_of_heq (by simp) d.heq_start_toGraphTop).trans
        d.start.heq_toSimpleGraph_toGraph)
  · rw [Graph.EarDecomposition.walkAt_toSimpleGraphTop, walkAt_toGraphTop]
    simp

end EarDecomposition

end SimpleGraph

namespace Graph

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

namespace EarStart

/-- Transporting initial data to the simple-graph interface and back recovers it, over the
recovered graph. -/
theorem heq_toGraph_toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    HEq s.toSimpleGraph.toGraph s := by
  cases s with
  | vertex v =>
      exact (SimpleGraph.EarStart.heq_toGraph_of_heq
        (toSimpleGraphSubgraph_noEdge_singleton v.1 _)
        (heq_toSimpleGraph_vertex v)).trans (SimpleGraph.EarStart.heq_toGraph_vertex _)
  | cycle p hp =>
      refine (SimpleGraph.EarStart.heq_toGraph_of_heq (p.toSimpleGraphSubgraph_walkGraph _)
        (heq_toSimpleGraph_cycle p hp)).trans
        ((SimpleGraph.EarStart.heq_toGraph_cycle _ _).trans ?_)
      have key : ∀ (p' : (Graph.ofSimpleGraph G).Walk _ _) (hp' : p'.IsCycle), p' = p →
          HEq (EarStart.cycle p' hp') (EarStart.cycle p hp) := by
        rintro _ _ rfl
        rfl
      exact key _ _ (Graph.Walk.toGraph_toSimpleGraph p)

end EarStart

namespace EarDecomposition

/-- Transporting a decomposition to the simple-graph interface and back recovers it after
reindexing its final graph. -/
@[simp]
theorem copy_toGraph_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.toGraph.copy (toGraph_toSimpleGraphSubgraph K d.final_le) = d := by
  have hlen :
      (d.toSimpleGraph.toGraph.copy (toGraph_toSimpleGraphSubgraph K d.final_le)).length =
        d.length := by simp
  refine Graph.EarDecomposition.ext _ _ hlen ?_ ?_
  · exact (heq_start_copy _ _).trans (d.toSimpleGraph.heq_start_toGraph.trans
      ((SimpleGraph.EarStart.heq_toGraph_of_heq (by simp) HEq.rfl).trans
        d.start.heq_toGraph_toSimpleGraph))
  · rw [Fin.heq_fun_iff hlen]
    intro i
    rw [earAt_copy, SimpleGraph.EarDecomposition.earAt_toGraph]
    refine Sigma.ext ?_ ?_
    · exact (congrArg _ (d.subgraphAfter_toSimpleGraph _)).trans
        ((toGraph_toSimpleGraphSubgraph _ _).trans (d.earAt_fst _).symm)
    · exact (SimpleGraph.Ear.heq_toGraph_copy _ _).trans (Ear.heq_toGraph_toSimpleGraph _)

/-- Transporting a full decomposition to the simple-graph interface and back recovers it. -/
@[simp]
theorem toGraphTop_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph G).EarDecomposition (Graph.ofSimpleGraph G)) :
    d.toSimpleGraphTop.toGraphTop = d := by
  have hlen : d.toSimpleGraphTop.toGraphTop.length = d.length := by simp
  refine Graph.EarDecomposition.ext _ _ hlen ?_ ?_
  · exact d.toSimpleGraphTop.heq_start_toGraphTop.trans
      ((SimpleGraph.EarStart.heq_toGraph_of_heq (by simp) d.heq_start_toSimpleGraphTop).trans
        d.start.heq_toGraph_toSimpleGraph)
  · rw [Fin.heq_fun_iff hlen]
    intro i
    rw [SimpleGraph.EarDecomposition.earAt_toGraphTop]
    refine Sigma.ext ?_ ?_
    · simp only [subgraphAfter_toSimpleGraphTop, toGraph_toSimpleGraphSubgraph, d.earAt_fst]
      congr 1
    · rw [earAt_toSimpleGraphTop]
      exact (SimpleGraph.Ear.heq_toGraph_copy _ _).trans (Ear.heq_toGraph_toSimpleGraph _)

end EarDecomposition

end Graph
