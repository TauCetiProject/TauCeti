/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Characterization
public import TauCeti.Combinatorics.Graph.Connectivity.VertexConnectivity
public import TauCeti.Combinatorics.Graph.Subgraph.Connectivity
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Open

/-!
# Transporting ear decompositions between simple graphs and multigraphs

Tau Ceti provides both a simple-graph ear-decomposition API (`SimpleGraph.Ear`,
`SimpleGraph.EarStart`, `SimpleGraph.EarDecomposition`) over `S : H.Subgraph` and an edge-labelled
multigraph ear-decomposition API (`Graph.Ear`, `Graph.EarStart`, `Graph.EarDecomposition`) over
`K ≤ G`. On `G = Graph.ofSimpleGraph H`, edge identities are determined by unordered endpoint pairs,
and `SimpleGraph.Ear.closed_edges_notMem_edgeSet` supplies the multigraph unused-edge condition for
closed ears automatically.

This file builds computable equivalences between the two representations at every level—ear kinds,
ears, initial stages, partial ear decompositions over `S : H.Subgraph` versus `S.toGraph`, and full
ear decompositions of `⊤ : H.Subgraph` versus `Graph.ofSimpleGraph H`—preserving length, prefix
subgraphs, initial witnesses, ear kinds, ear walks, openness, vertex-start predicates, `copy`,
`vertex`, `cycle`, and `prefix`.

Using this dictionary:
* computable start replacement (`SimpleGraph.EarDecomposition.replaceInitial`) and cycle-to-vertex
  start normalization (`SimpleGraph.EarDecomposition.toVertexStart`) transfer from multigraphs to
  `SimpleGraph.EarDecomposition` with no finiteness assumptions;
* partial-decomposition completion (`SimpleGraph.EarDecomposition.extend`), prescribed-vertex and
  prescribed-cycle constructors, and Robbins's `2`-edge-connectivity characterization transfer to
  `SimpleGraph.EarDecomposition` under edge finiteness `[Finite H.edgeSet]` rather than vertex
  finiteness `[Finite V]`;
* Whitney's open-ear soundness and completeness theorems for `2`-vertex-connectivity transfer from
  `SimpleGraph.EarDecomposition` to multigraph ear decompositions on `Graph.ofSimpleGraph H`.

## Implementation notes

Matching `TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Basic`, all predicates, equivalences,
and high-level combinators (`EarKind.toGraph`, `Ear.toGraph`, `EarStart.toGraph`,
`EarDecomposition.toGraphTop`, `Graph.EarDecomposition.toSimpleGraphTop`,
`EarDecomposition.IsVertexStart`, `EarDecomposition.replaceInitial`,
`EarDecomposition.toVertexStart`, `EarDecomposition.extend`) remain unexposed, with characteristic
`@[simp]` lemmas proved via `:= (rfl)`. Only the three length-preserving stage translations
`SimpleGraph.EarDecomposition.toGraph`, `Graph.EarDecomposition.toSimpleGraph`, and
`Graph.EarDecomposition.toSimpleGraphSubgraph` carry `@[expose]` so dependent `Fin` indices over
`.length` compute in public theorem signatures.

## References

* H. Whitney, *Congruent graphs and the connectivity of graphs*, Amer. J. Math. 54 (1932), 150–168.
* H. E. Robbins, *A theorem on graphs, with an application to a problem of traffic control*,
  Amer. Math. Monthly 46 (1939), 281–283.
* R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer, 2017,
  Section 3.1.
-/

public section

open Set
open scoped Graph Sym2

universe u

/-! ### Ear kinds -/

namespace SimpleGraph.EarKind

/-- Convert a simple-graph ear kind to a multigraph ear kind. -/
def toGraph : SimpleGraph.EarKind → Graph.EarKind
  | .«open» => .open
  | .closed => .closed

@[simp] theorem toGraph_open : (EarKind.«open»).toGraph = .open := (rfl)
@[simp] theorem toGraph_closed : (EarKind.closed).toGraph = .closed := (rfl)

end SimpleGraph.EarKind

namespace Graph.EarKind

/-- Convert a multigraph ear kind to a simple-graph ear kind. -/
def toSimpleGraph : Graph.EarKind → SimpleGraph.EarKind
  | .open => .«open»
  | .closed => .closed

@[simp] theorem toSimpleGraph_open : (EarKind.open).toSimpleGraph = .«open» := (rfl)
@[simp] theorem toSimpleGraph_closed : (EarKind.closed).toSimpleGraph = .closed := (rfl)

@[simp]
theorem toGraph_toSimpleGraph (k : Graph.EarKind) : k.toSimpleGraph.toGraph = k := by
  cases k <;> rfl

@[simp]
theorem toSimpleGraph_eq_open_iff {k : Graph.EarKind} :
    k.toSimpleGraph = .«open» ↔ k = .open := by
  cases k <;> simp

@[simp]
theorem toSimpleGraph_eq_closed_iff {k : Graph.EarKind} :
    k.toSimpleGraph = .closed ↔ k = .closed := by
  cases k <;> simp

end Graph.EarKind

namespace SimpleGraph

namespace EarKind

@[simp]
theorem toSimpleGraph_toGraph (k : SimpleGraph.EarKind) : k.toGraph.toSimpleGraph = k := by
  cases k <;> rfl

@[simp]
theorem toGraph_eq_open_iff {k : SimpleGraph.EarKind} : k.toGraph = .open ↔ k = .«open» := by
  cases k <;> simp

@[simp]
theorem toGraph_eq_closed_iff {k : SimpleGraph.EarKind} : k.toGraph = .closed ↔ k = .closed := by
  cases k <;> simp

end EarKind

/-- Canonical equivalence between `SimpleGraph.EarKind` and `Graph.EarKind`. -/
def earKindEquiv : SimpleGraph.EarKind ≃ Graph.EarKind where
  toFun := EarKind.toGraph
  invFun := Graph.EarKind.toSimpleGraph
  left_inv := EarKind.toSimpleGraph_toGraph
  right_inv := Graph.EarKind.toGraph_toSimpleGraph

end SimpleGraph

/-! ### Ears across `Graph.ofSimpleGraph` -/

namespace SimpleGraph.Ear

variable {V : Type u} {H : SimpleGraph V} {S : H.Subgraph}

/-- Regard an ear `e : H.Ear S` over `S : H.Subgraph` as an ear in `Graph.ofSimpleGraph H` over
`S.toGraph`. -/
def toGraph : H.Ear S → (Graph.ofSimpleGraph H).Ear S.toGraph
  | .«open» p hp hu hv huv hint hedge =>
      .open S.toGraph_le_ofSimpleGraph p.toGraph ((Walk.isPath_toGraph_iff p).mpr hp)
        (S.vertexSet_toGraph.symm ▸ hu) (S.vertexSet_toGraph.symm ▸ hv) huv
        (fun w hw hwu hwv ↦ S.vertexSet_toGraph.symm ▸
          hint w (by simpa only [Walk.support_toGraph] using hw) hwu hwv)
        (fun e he ↦ S.edgeSet_toGraph.symm ▸
          hedge e (by simpa only [Walk.edges_toGraph] using he))
  | .closed c hc hu hint =>
      .closed S.toGraph_le_ofSimpleGraph c.toGraph ((Walk.isCycle_toGraph_iff c).mpr hc)
        (S.vertexSet_toGraph.symm ▸ hu)
        (fun w hw hwu ↦ S.vertexSet_toGraph.symm ▸
          hint w (by simpa only [Walk.support_toGraph] using hw) hwu)
        (fun e he ↦ S.edgeSet_toGraph.symm ▸
          Ear.closed_edges_notMem_edgeSet hint (by simpa only [Walk.edges_toGraph] using he))

@[simp]
theorem kind_toGraph (e : H.Ear S) : e.toGraph.kind = e.kind.toGraph := by
  cases e <;> simp [toGraph]

@[simp]
theorem toWalk_toGraph (e : H.Ear S) :
    e.toGraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toGraph⟩ := by
  cases e with
  | «open» => rw [toGraph, toWalk_open, Graph.Ear.toWalk_open]
  | closed => rw [toGraph, toWalk_closed, Graph.Ear.toWalk_closed]

@[simp]
theorem earToGraph_toGraph (e : H.Ear S) :
    Graph.Ear.toGraph e.toGraph = e.toSubgraph.toGraph := by
  cases e <;> simp [toGraph, Walk.toSubgraph_toGraph]

@[simp]
theorem add_toGraph (e : H.Ear S) : e.toGraph.add = e.adjoin.toGraph := by
  rw [Ear.adjoin_def, Subgraph.sup_toGraph]
  exact Graph.ext (by simp) fun _ _ _ ↦ by simp

end SimpleGraph.Ear

namespace Graph.Ear

variable {V : Type u} {H : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Recover a simple-graph ear over `e.base_le.toSimpleGraphSubgraph` from an ear in
`Graph.ofSimpleGraph H`. -/
def toSimpleGraph : (e : (Graph.ofSimpleGraph H).Ear K) → H.Ear e.base_le.toSimpleGraphSubgraph
  | .open hKG p hp hu hv huv hint hedge =>
      .«open» p.toSimpleGraph ((Walk.isPath_toSimpleGraph_iff p).mpr hp)
        (hKG.verts_toSimpleGraphSubgraph.symm ▸ hu) (hKG.verts_toSimpleGraphSubgraph.symm ▸ hv) huv
        (fun w hw hwu hwv ↦ hKG.verts_toSimpleGraphSubgraph.symm ▸
          hint w (by simpa only [Walk.support_toSimpleGraph] using hw) hwu hwv)
        (fun f hf ↦ hKG.edgeSet_toSimpleGraphSubgraph.symm ▸
          hedge f (by simpa only [Walk.edges_toSimpleGraph] using hf))
  | .closed hKG c hc hu hint _ =>
      .closed c.toSimpleGraph ((Walk.isCycle_toSimpleGraph_iff c).mpr hc)
        (hKG.verts_toSimpleGraphSubgraph.symm ▸ hu)
        (fun w hw hwu ↦ hKG.verts_toSimpleGraphSubgraph.symm ▸
          hint w (by simpa only [Walk.support_toSimpleGraph] using hw) hwu)

@[simp]
theorem kind_toSimpleGraph (e : (Graph.ofSimpleGraph H).Ear K) :
    e.toSimpleGraph.kind = e.kind.toSimpleGraph := by
  cases e <;> simp [toSimpleGraph]

@[simp]
theorem toWalk_toSimpleGraph (e : (Graph.ofSimpleGraph H).Ear K) :
    e.toSimpleGraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toSimpleGraph⟩ := by
  cases e with
  | «open» => rw [toSimpleGraph, toWalk_open, SimpleGraph.Ear.toWalk_open]
  | closed => rw [toSimpleGraph, toWalk_closed, SimpleGraph.Ear.toWalk_closed]

@[simp]
theorem toSubgraph_toSimpleGraph_toGraph (e : (Graph.ofSimpleGraph H).Ear K) :
    e.toSimpleGraph.toSubgraph.toGraph = e.toGraph := by
  cases e <;> simp [toSimpleGraph, SimpleGraph.Walk.toSubgraph_toGraph, Walk.toGraph_toSimpleGraph]

/-- Recover a simple-graph ear over `S` from an ear in `Graph.ofSimpleGraph H` over `S.toGraph`. -/
def toSimpleGraphSubgraph {S : H.Subgraph} (e : (Graph.ofSimpleGraph H).Ear S.toGraph) : H.Ear S :=
  e.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph e.base_le)

@[simp]
theorem kind_toSimpleGraphSubgraph {S : H.Subgraph} (e : (Graph.ofSimpleGraph H).Ear S.toGraph) :
    e.toSimpleGraphSubgraph.kind = e.kind.toSimpleGraph := by
  simp [toSimpleGraphSubgraph]

@[simp]
theorem toWalk_toSimpleGraphSubgraph {S : H.Subgraph} (e : (Graph.ofSimpleGraph H).Ear S.toGraph) :
    e.toSimpleGraphSubgraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toSimpleGraph⟩ := by
  rw [toSimpleGraphSubgraph, SimpleGraph.Ear.toWalk_copy, toWalk_toSimpleGraph]

@[simp]
theorem toGraph_toSimpleGraphSubgraph {S : H.Subgraph}
    (e : (Graph.ofSimpleGraph H).Ear S.toGraph) :
    e.toSimpleGraphSubgraph.toGraph = e := by
  apply Ear.ext
  · simp
  · rw [SimpleGraph.Ear.toWalk_toGraph, toWalk_toSimpleGraphSubgraph, Walk.toGraph_toSimpleGraph]

end Graph.Ear

namespace SimpleGraph.Ear

variable {V : Type u} {H : SimpleGraph V}

@[simp]
theorem toSimpleGraphSubgraph_toGraph {S : H.Subgraph} (e : H.Ear S) :
    e.toGraph.toSimpleGraphSubgraph = e := by
  ext : 1
  rw [Graph.Ear.toWalk_toSimpleGraphSubgraph, toWalk_toGraph, Walk.toSimpleGraph_toGraph]

/-- Canonical equivalence between simple-graph ears over `S` and multigraph ears in
`Graph.ofSimpleGraph H` over `S.toGraph`. -/
def equivOfSimpleGraph (S : H.Subgraph) :
    H.Ear S ≃ (Graph.ofSimpleGraph H).Ear S.toGraph where
  toFun := Ear.toGraph
  invFun := Graph.Ear.toSimpleGraphSubgraph
  left_inv := toSimpleGraphSubgraph_toGraph
  right_inv := Graph.Ear.toGraph_toSimpleGraphSubgraph

@[simp]
theorem equivOfSimpleGraph_apply (S : H.Subgraph) (e : H.Ear S) :
    equivOfSimpleGraph S e = e.toGraph := (rfl)

@[simp]
theorem equivOfSimpleGraph_symm_apply (S : H.Subgraph)
    (e : (Graph.ofSimpleGraph H).Ear S.toGraph) :
    (equivOfSimpleGraph S).symm e = e.toSimpleGraphSubgraph := (rfl)

end SimpleGraph.Ear

/-! ### Initial subgraphs (`EarStart`) across `Graph.ofSimpleGraph` -/

namespace SimpleGraph.EarStart

variable {V : Type u} {H : SimpleGraph V}

/-- Regard an initial-subgraph witness `s : H.EarStart S` as a multigraph `EarStart` for
`S.toGraph`. -/
def toGraph {S : H.Subgraph} : H.EarStart S → (Graph.ofSimpleGraph H).EarStart S.toGraph
  | .vertex v =>
      (Graph.EarStart.vertex ⟨v, mem_univ v⟩).copy (Subgraph.singletonSubgraph_toGraph v).symm
  | .cycle c hc =>
      (Graph.EarStart.cycle c.toGraph ((Walk.isCycle_toGraph_iff c).mpr hc)).copy
        (Walk.toSubgraph_toGraph c).symm

theorem heq_toGraph_copy {S S' : H.Subgraph} (s : H.EarStart S) (h : S = S') :
    HEq (s.copy h).toGraph s.toGraph := by
  subst h; rw [copy_rfl]

theorem heq_toGraph_of_heq {S₁ S₂ : H.Subgraph} {s₁ : H.EarStart S₁} {s₂ : H.EarStart S₂}
    (hS : S₁ = S₂) (hs : HEq s₁ s₂) : HEq s₁.toGraph s₂.toGraph := by
  subst hS
  cases eq_of_heq hs
  rfl

@[simp]
theorem isCycle_toGraph_iff {S : H.Subgraph} (s : H.EarStart S) :
    s.toGraph.IsCycle ↔ s.IsCycle := by
  cases s <;> simp [toGraph]

end SimpleGraph.EarStart

namespace Graph.EarStart

variable {V : Type u} {H : SimpleGraph V}

/-- Recover a simple-graph `EarStart` witness from an `EarStart` in `Graph.ofSimpleGraph H`. -/
def toSimpleGraph {K : Graph V (Sym2 V)} :
    (s : (Graph.ofSimpleGraph H).EarStart K) → H.EarStart s.le.toSimpleGraphSubgraph
  | .vertex v =>
      (SimpleGraph.EarStart.vertex v.1).copy
        (IsSubgraph.noEdge_singleton_toSimpleGraphSubgraph _).symm
  | .cycle c hc =>
      (SimpleGraph.EarStart.cycle c.toSimpleGraph ((Walk.isCycle_toSimpleGraph_iff c).mpr hc)).copy
        (Walk.walkGraph_toSimpleGraphSubgraph c _).symm

theorem heq_toSimpleGraph_copy {K K' : Graph V (Sym2 V)}
    (s : (Graph.ofSimpleGraph H).EarStart K) (h : K = K') :
    HEq (s.copy h).toSimpleGraph s.toSimpleGraph := by
  subst h; rw [copy_rfl]

theorem heq_toSimpleGraph_of_heq {K L : Graph V (Sym2 V)} {s₁ : (Graph.ofSimpleGraph H).EarStart K}
    {s₂ : (Graph.ofSimpleGraph H).EarStart L} (hKL : K = L) (hs : HEq s₁ s₂) :
    HEq s₁.toSimpleGraph s₂.toSimpleGraph := by
  subst hKL
  cases eq_of_heq hs
  rfl

@[simp]
theorem isCycle_toSimpleGraph_iff {K : Graph V (Sym2 V)}
    (s : (Graph.ofSimpleGraph H).EarStart K) :
    s.toSimpleGraph.IsCycle ↔ s.IsCycle := by
  cases s <;> simp [toSimpleGraph]

/-- Recover a simple-graph `EarStart` witness over `S` from a multigraph `EarStart` over
`S.toGraph`. -/
def toSimpleGraphSubgraph {S : H.Subgraph} (s : (Graph.ofSimpleGraph H).EarStart S.toGraph) :
    H.EarStart S :=
  s.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph s.le)

private theorem heq_cycle_of_walk_eq {x : V} {c₁ c₂ : (Graph.ofSimpleGraph H).Walk x x}
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle) (h : c₁ = c₂) :
    HEq (EarStart.cycle c₁ hc₁) (EarStart.cycle c₂ hc₂) := by
  subst h; rfl

theorem heq_toGraph_toSimpleGraph {K : Graph V (Sym2 V)}
    (s : (Graph.ofSimpleGraph H).EarStart K) : HEq s.toSimpleGraph.toGraph s := by
  cases s with
  | vertex v =>
      have hv : (⟨v.1, mem_univ v.1⟩ : V(Graph.ofSimpleGraph H)) = v := Subtype.ext rfl
      refine (SimpleGraph.EarStart.heq_toGraph_copy _ _).trans ?_
      simpa only [SimpleGraph.EarStart.toGraph, hv] using heq_copy (EarStart.vertex v) _
  | cycle c hc =>
      refine (SimpleGraph.EarStart.heq_toGraph_copy _ _).trans ?_
      dsimp only [SimpleGraph.EarStart.toGraph]
      exact (heq_copy _ _).trans (heq_cycle_of_walk_eq _ hc (Walk.toGraph_toSimpleGraph c))

@[simp]
theorem toGraph_toSimpleGraphSubgraph {S : H.Subgraph}
    (s : (Graph.ofSimpleGraph H).EarStart S.toGraph) :
    s.toSimpleGraphSubgraph.toGraph = s :=
  eq_of_heq ((SimpleGraph.EarStart.heq_toGraph_copy s.toSimpleGraph _).trans
    s.heq_toGraph_toSimpleGraph)

end Graph.EarStart

namespace SimpleGraph.EarStart

variable {V : Type u} {H : SimpleGraph V}

private theorem heq_cycle_of_walk_eq {x : V} {c₁ c₂ : H.Walk x x}
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle) (h : c₁ = c₂) :
    HEq (EarStart.cycle c₁ hc₁) (EarStart.cycle c₂ hc₂) := by
  subst h; rfl

theorem heq_toSimpleGraph_toGraph {S : H.Subgraph} (s : H.EarStart S) :
    HEq s.toGraph.toSimpleGraph s := by
  cases s with
  | vertex v =>
      refine (Graph.EarStart.heq_toSimpleGraph_copy _ _).trans ?_
      simpa only [Graph.EarStart.toSimpleGraph] using heq_copy (EarStart.vertex v) _
  | cycle c hc =>
      refine (Graph.EarStart.heq_toSimpleGraph_copy _ _).trans ?_
      dsimp only [Graph.EarStart.toSimpleGraph]
      exact (heq_copy _ _).trans (heq_cycle_of_walk_eq _ hc (Walk.toSimpleGraph_toGraph c))

@[simp]
theorem toSimpleGraphSubgraph_toGraph {S : H.Subgraph} (s : H.EarStart S) :
    s.toGraph.toSimpleGraphSubgraph = s :=
  eq_of_heq ((heq_copy s.toGraph.toSimpleGraph _).trans s.heq_toSimpleGraph_toGraph)

/-- Canonical equivalence between simple-graph `EarStart` witnesses over `S` and multigraph
`EarStart` witnesses in `Graph.ofSimpleGraph H` over `S.toGraph`. -/
def equivOfSimpleGraph (S : H.Subgraph) :
    H.EarStart S ≃ (Graph.ofSimpleGraph H).EarStart S.toGraph where
  toFun := EarStart.toGraph
  invFun := Graph.EarStart.toSimpleGraphSubgraph
  left_inv := toSimpleGraphSubgraph_toGraph
  right_inv := Graph.EarStart.toGraph_toSimpleGraphSubgraph

end SimpleGraph.EarStart

/-! ### Ear decompositions across `Graph.ofSimpleGraph` -/

namespace SimpleGraph.EarDecomposition

variable {V : Type u} {H : SimpleGraph V} {S S' : H.Subgraph}

/-- Regard an ear decomposition `d : H.EarDecomposition S` as a multigraph ear decomposition in
`Graph.ofSimpleGraph H` with final graph `S.toGraph`. -/
@[expose]
def toGraph (d : H.EarDecomposition S) : (Graph.ofSimpleGraph H).EarDecomposition S.toGraph where
  length := d.length
  graphAfter k := (d.subgraphAfter k).toGraph
  start := d.start.toGraph
  earAt i := ⟨(d.subgraphAfter i.castSucc).toGraph, (d.earAt i).toGraph⟩
  earAt_fst _ := rfl
  graphAfter_succ i := by rw [d.subgraphAfter_succ i, (d.earAt i).add_toGraph]
  graphAfter_last := congrArg Subgraph.toGraph d.subgraphAfter_last

@[simp] theorem length_toGraph (d : H.EarDecomposition S) : d.toGraph.length = d.length := (rfl)

@[simp]
theorem graphAfter_toGraph (d : H.EarDecomposition S) (k : Fin (d.length + 1)) :
    d.toGraph.graphAfter k = (d.subgraphAfter k).toGraph := (rfl)

theorem initial_toGraph (d : H.EarDecomposition S) : d.toGraph.initial = d.initial.toGraph :=
  d.toGraph.initial_eq_graphAfter.trans (congrArg Subgraph.toGraph d.subgraphAfter_zero)

@[simp]
theorem start_toGraph (d : H.EarDecomposition S) : d.toGraph.start = d.start.toGraph := (rfl)

theorem start_isCycle_toGraph_iff (d : H.EarDecomposition S) :
    d.toGraph.start.IsCycle ↔ d.start.IsCycle :=
  d.start.isCycle_toGraph_iff

@[simp]
theorem earAt_toGraph (d : H.EarDecomposition S) (i : Fin d.length) :
    d.toGraph.earAt i = ⟨(d.subgraphAfter i.castSucc).toGraph, (d.earAt i).toGraph⟩ := (rfl)

@[simp]
theorem kindAt_toGraph (d : H.EarDecomposition S) (i : Fin d.length) :
    d.toGraph.kindAt i = (d.kindAt i).toGraph :=
  (d.toGraph.kindAt_eq i).trans
    ((Ear.kind_toGraph (d.earAt i)).trans (congrArg EarKind.toGraph (d.kindAt_def i).symm))

@[simp]
theorem walkAt_toGraph (d : H.EarDecomposition S) (i : Fin d.length) :
    d.toGraph.walkAt i = ⟨(d.walkAt i).1, (d.walkAt i).2.1, (d.walkAt i).2.2.toGraph⟩ :=
  (d.toGraph.walkAt_eq i).trans ((Ear.toWalk_toGraph (d.earAt i)).trans
    (congrArg (fun w : (u : V) × (v : V) × H.Walk u v ↦
      (⟨w.1, w.2.1, w.2.2.toGraph⟩ : (u : V) × (v : V) × (Graph.ofSimpleGraph H).Walk u v))
      (d.walkAt_def i).symm))

@[simp]
theorem isOpen_toGraph_iff (d : H.EarDecomposition S) : d.toGraph.IsOpen ↔ d.IsOpen := by
  rw [Graph.EarDecomposition.isOpen_iff, isOpen_iff, start_isCycle_toGraph_iff]
  exact and_congr_right fun _ ↦
    ⟨fun h i ↦ EarKind.toGraph_eq_open_iff.mp ((d.kindAt_toGraph i).symm.trans (h i)),
      fun h i ↦ (d.kindAt_toGraph i).trans (EarKind.toGraph_eq_open_iff.mpr (h i))⟩

@[simp]
theorem copy_toGraph (d : H.EarDecomposition S) (h : S = S') :
    (d.copy h).toGraph = d.toGraph.copy (congrArg Subgraph.toGraph h) := by
  cases h
  exact d.toGraph.copy_rfl.symm

@[simp]
theorem prefix_toGraph (d : H.EarDecomposition S) (k : Fin (d.length + 1)) :
    (d.prefix k).toGraph = d.toGraph.prefix k :=
  Graph.EarDecomposition.ext_of_cast (d.toGraph.length_prefix k).symm
    (fun j ↦ (d.toGraph.graphAfter_prefix k j).symm)
    (d.toGraph.heq_start_prefix k).symm
    (fun j ↦ (d.toGraph.earAt_prefix k j).symm)

theorem vertex_toGraph (v : V) :
    (EarDecomposition.vertex H v).toGraph =
      (Graph.EarDecomposition.vertex (G := Graph.ofSimpleGraph H) ⟨v, mem_univ v⟩).copy
        (Subgraph.singletonSubgraph_toGraph (H := H) v).symm := by
  let vG : V(Graph.ofSimpleGraph H) := ⟨v, mem_univ v⟩
  have hlen : (vertex H v).toGraph.length =
      ((Graph.EarDecomposition.vertex vG).copy
        (Subgraph.singletonSubgraph_toGraph (H := H) v).symm).length := by simp
  refine Graph.EarDecomposition.ext_of_cast hlen (fun k ↦ ?_) ?_
    (fun i ↦ Fin.elim0 (i.cast (length_vertex v)))
  · have hk : k = 0 := Fin.ext (Nat.lt_one_iff.mp (by simpa [length_vertex] using k.isLt))
    subst hk
    have hc : Fin.cast (congrArg (· + 1) ((Graph.EarDecomposition.vertex vG).length_copy _))
        (Fin.cast (congrArg (· + 1) hlen) 0) = 0 := Fin.ext rfl
    rw [Graph.EarDecomposition.graphAfter_copy, hc, Graph.EarDecomposition.graphAfter_vertex_zero]
    exact ((congrArg Subgraph.toGraph (subgraphAfter_vertex v 0)).trans
      (Subgraph.singletonSubgraph_toGraph (H := H) v))
  · have hs : HEq (vertex H v).start (EarStart.vertex (G := H) v) := by
      rw [start_vertex]
      exact eqRec_heq _ _
    exact (EarStart.heq_toGraph_of_heq (subgraphAfter_vertex v 0) hs).trans
      ((Graph.EarStart.heq_copy _ _).trans
        ((Graph.EarDecomposition.heq_start_vertex vG).symm.trans
          (Graph.EarDecomposition.heq_start_copy _ _).symm))

theorem cycle_toGraph {u : V} (c : H.Walk u u) (hc : c.IsCycle) :
    (EarDecomposition.cycle c hc).toGraph =
      (Graph.EarDecomposition.cycle c.toGraph ((Walk.isCycle_toGraph_iff c).mpr hc)).copy
        (Walk.toSubgraph_toGraph c).symm := by
  have hlen : (cycle c hc).toGraph.length =
      ((Graph.EarDecomposition.cycle c.toGraph ((Walk.isCycle_toGraph_iff c).mpr hc)).copy
        (Walk.toSubgraph_toGraph c).symm).length := by simp
  refine Graph.EarDecomposition.ext_of_cast hlen (fun k ↦ ?_) ?_
    (fun i ↦ Fin.elim0 (i.cast (length_cycle c hc)))
  · have hk : k = 0 := Fin.ext (Nat.lt_one_iff.mp (by simpa [length_cycle] using k.isLt))
    subst hk
    have hc0 : Fin.cast (congrArg (· + 1)
        ((Graph.EarDecomposition.cycle c.toGraph _).length_copy _))
        (Fin.cast (congrArg (· + 1) hlen) 0) = 0 := Fin.ext rfl
    rw [Graph.EarDecomposition.graphAfter_copy, hc0, Graph.EarDecomposition.graphAfter_cycle_zero]
    exact (congrArg Subgraph.toGraph (subgraphAfter_cycle c hc 0)).trans (Walk.toSubgraph_toGraph c)
  · have hs : HEq (cycle c hc).start (EarStart.cycle c hc) := by
      rw [start_cycle]
      exact eqRec_heq _ _
    exact (EarStart.heq_toGraph_of_heq (subgraphAfter_cycle c hc 0) hs).trans
      ((Graph.EarStart.heq_copy _ _).trans
        ((Graph.EarDecomposition.heq_start_cycle c.toGraph _).symm.trans
          (Graph.EarDecomposition.heq_start_copy _ _).symm))

end SimpleGraph.EarDecomposition

namespace Graph.EarDecomposition

variable {V : Type u} {H : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Recover a simple-graph ear decomposition over `d.final_le.toSimpleGraphSubgraph` from a
multigraph ear decomposition in `Graph.ofSimpleGraph H`. -/
@[expose]
def toSimpleGraph (d : (Graph.ofSimpleGraph H).EarDecomposition K) :
    H.EarDecomposition d.final_le.toSimpleGraphSubgraph where
  length := d.length
  subgraphAfter k := (d.graphAfter_le k).toSimpleGraphSubgraph
  start := d.start.toSimpleGraph
  earAt i :=
    (d.earAt i).2.toSimpleGraph.copy
      ((IsSubgraph.toSimpleGraphSubgraph_inj _ _).mpr (d.earAt_fst i))
  subgraphAfter_succ i := by
    rw [← SimpleGraph.Subgraph.toGraph_inj, (d.graphAfter_le i.succ).toGraph_toSimpleGraphSubgraph,
      SimpleGraph.Ear.adjoin_copy, SimpleGraph.Subgraph.sup_toGraph]
    refine (Compatible.of_le_le (d.graphAfter_le i.succ)
      (IsSubgraph.union_le (SimpleGraph.Subgraph.toGraph_le_ofSimpleGraph _)
        (SimpleGraph.Subgraph.toGraph_le_ofSimpleGraph _))).ext ?_ ?_
    · rw [d.graphAfter_succ i, Ear.vertexSet_add, Compatible.vertexSet_union,
        (d.graphAfter_le i.castSucc).toGraph_toSimpleGraphSubgraph,
        Ear.toSubgraph_toSimpleGraph_toGraph, congrArg vertexSet (d.earAt_fst i)]
    · rw [d.graphAfter_succ i, Ear.edgeSet_add, Compatible.edgeSet_union,
        (d.graphAfter_le i.castSucc).toGraph_toSimpleGraphSubgraph,
        Ear.toSubgraph_toSimpleGraph_toGraph, congrArg edgeSet (d.earAt_fst i)]
  subgraphAfter_last := (IsSubgraph.toSimpleGraphSubgraph_inj _ _).mpr d.graphAfter_last

@[simp]
theorem length_toSimpleGraph (d : (Graph.ofSimpleGraph H).EarDecomposition K) :
    d.toSimpleGraph.length = d.length := (rfl)

@[simp]
theorem subgraphAfter_toSimpleGraph (d : (Graph.ofSimpleGraph H).EarDecomposition K)
    (k : Fin (d.length + 1)) :
    d.toSimpleGraph.subgraphAfter k = (d.graphAfter_le k).toSimpleGraphSubgraph := (rfl)

@[simp]
theorem initial_toSimpleGraph (d : (Graph.ofSimpleGraph H).EarDecomposition K) :
    d.toSimpleGraph.initial = (d.graphAfter_le 0).toSimpleGraphSubgraph :=
  d.toSimpleGraph.subgraphAfter_zero.symm

@[simp]
theorem start_toSimpleGraph (d : (Graph.ofSimpleGraph H).EarDecomposition K) :
    d.toSimpleGraph.start = d.start.toSimpleGraph := (rfl)

@[simp]
theorem walkAt_toSimpleGraph (d : (Graph.ofSimpleGraph H).EarDecomposition K) (i : Fin d.length) :
    d.toSimpleGraph.walkAt i =
      ⟨(d.walkAt i).1, (d.walkAt i).2.1, (d.walkAt i).2.2.toSimpleGraph⟩ :=
  (d.toSimpleGraph.walkAt_def i).trans (((d.earAt i).2.toSimpleGraph.toWalk_copy _).trans
    ((Ear.toWalk_toSimpleGraph (d.earAt i).2).trans
      (congrArg (fun w : (u : V) × (v : V) × (Graph.ofSimpleGraph H).Walk u v ↦
        (⟨w.1, w.2.1, w.2.2.toSimpleGraph⟩ : (u : V) × (v : V) × H.Walk u v))
        (d.walkAt_eq i).symm)))

@[simp]
theorem kindAt_toSimpleGraph (d : (Graph.ofSimpleGraph H).EarDecomposition K) (i : Fin d.length) :
    d.toSimpleGraph.kindAt i = (d.kindAt i).toSimpleGraph :=
  (d.toSimpleGraph.kindAt_def i).trans (((d.earAt i).2.toSimpleGraph.kind_copy _).trans
    ((Ear.kind_toSimpleGraph (d.earAt i).2).trans
      (congrArg EarKind.toSimpleGraph (d.kindAt_eq i).symm)))

@[simp]
theorem isOpen_toSimpleGraph_iff (d : (Graph.ofSimpleGraph H).EarDecomposition K) :
    d.toSimpleGraph.IsOpen ↔ d.IsOpen :=
  d.toSimpleGraph.isOpen_iff.trans ((and_congr d.start.isCycle_toSimpleGraph_iff
    ⟨fun h i ↦ EarKind.toSimpleGraph_eq_open_iff.mp ((d.kindAt_toSimpleGraph i).symm.trans (h i)),
      fun h i ↦
        (d.kindAt_toSimpleGraph i).trans (EarKind.toSimpleGraph_eq_open_iff.mpr (h i))⟩).trans
    d.isOpen_iff.symm)

/-- Recover a simple-graph ear decomposition over `S` from a multigraph ear decomposition in
`Graph.ofSimpleGraph H` over `S.toGraph`. -/
@[expose]
def toSimpleGraphSubgraph {S : H.Subgraph}
    (d : (Graph.ofSimpleGraph H).EarDecomposition S.toGraph) : H.EarDecomposition S :=
  d.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph d.final_le)

@[simp]
theorem initial_toSimpleGraphSubgraph {S : H.Subgraph}
    (d : (Graph.ofSimpleGraph H).EarDecomposition S.toGraph) :
    d.toSimpleGraphSubgraph.initial = (d.graphAfter_le 0).toSimpleGraphSubgraph := by
  rw [toSimpleGraphSubgraph, SimpleGraph.EarDecomposition.initial_copy, initial_toSimpleGraph]

@[simp]
theorem walkAt_toSimpleGraphSubgraph {S : H.Subgraph}
    (d : (Graph.ofSimpleGraph H).EarDecomposition S.toGraph) (i : Fin d.length) :
    d.toSimpleGraphSubgraph.walkAt i =
      ⟨(d.walkAt i).1, (d.walkAt i).2.1, (d.walkAt i).2.2.toSimpleGraph⟩ :=
  (d.toSimpleGraph.walkAt_copy _ i).trans (d.walkAt_toSimpleGraph i)

@[simp]
theorem kindAt_toSimpleGraphSubgraph {S : H.Subgraph}
    (d : (Graph.ofSimpleGraph H).EarDecomposition S.toGraph) (i : Fin d.length) :
    d.toSimpleGraphSubgraph.kindAt i = (d.kindAt i).toSimpleGraph :=
  (d.toSimpleGraph.kindAt_copy _ i).trans (d.kindAt_toSimpleGraph i)

@[simp]
theorem isOpen_toSimpleGraphSubgraph_iff {S : H.Subgraph}
    (d : (Graph.ofSimpleGraph H).EarDecomposition S.toGraph) :
    d.toSimpleGraphSubgraph.IsOpen ↔ d.IsOpen :=
  (d.toSimpleGraph.isOpen_copy _).trans d.isOpen_toSimpleGraph_iff

@[simp]
theorem toGraph_toSimpleGraphSubgraph {S : H.Subgraph}
    (d : (Graph.ofSimpleGraph H).EarDecomposition S.toGraph) :
    d.toSimpleGraphSubgraph.toGraph = d := by
  refine ext_of_cast rfl (fun k ↦ (d.graphAfter_le k).toGraph_toSimpleGraphSubgraph)
    d.start.heq_toGraph_toSimpleGraph fun i ↦ ?_
  refine Ear.sigma_ext (((d.graphAfter_le i.castSucc).toGraph_toSimpleGraphSubgraph).trans
      (d.earAt_fst i).symm) ?_ ?_
  · dsimp only [SimpleGraph.EarDecomposition.toGraph, toSimpleGraphSubgraph,
      SimpleGraph.EarDecomposition.copy, toSimpleGraph]
    rw [SimpleGraph.Ear.kind_toGraph, SimpleGraph.Ear.kind_copy, Ear.kind_toSimpleGraph,
      EarKind.toGraph_toSimpleGraph]
    rfl
  · dsimp only [SimpleGraph.EarDecomposition.toGraph, toSimpleGraphSubgraph,
      SimpleGraph.EarDecomposition.copy, toSimpleGraph]
    rw [SimpleGraph.Ear.toWalk_toGraph, SimpleGraph.Ear.toWalk_copy, Ear.toWalk_toSimpleGraph,
      Walk.toGraph_toSimpleGraph]
    rfl

/-- Recover an ear decomposition of `⊤ : H.Subgraph` from a full multigraph ear decomposition of
`Graph.ofSimpleGraph H`. -/
def toSimpleGraphTop
    (d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)) :
    H.EarDecomposition (⊤ : H.Subgraph) :=
  d.toSimpleGraph.copy (IsSubgraph.ofSimpleGraph_toSimpleGraphSubgraph d.final_le)

@[simp]
theorem length_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)) :
    d.toSimpleGraphTop.length = d.length := (rfl)

@[simp]
theorem initial_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)) :
    d.toSimpleGraphTop.initial = (d.graphAfter_le 0).toSimpleGraphSubgraph := by
  rw [toSimpleGraphTop, SimpleGraph.EarDecomposition.initial_copy, initial_toSimpleGraph]

@[simp]
theorem isOpen_toSimpleGraphTop_iff
    (d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)) :
    d.toSimpleGraphTop.IsOpen ↔ d.IsOpen :=
  (d.toSimpleGraph.isOpen_copy _).trans d.isOpen_toSimpleGraph_iff

end Graph.EarDecomposition

namespace SimpleGraph

variable {V : Type u} {H : SimpleGraph V}

namespace EarDecomposition

@[simp]
theorem toSimpleGraphSubgraph_toGraph {S : H.Subgraph} (d : H.EarDecomposition S) :
    d.toGraph.toSimpleGraphSubgraph = d := by
  refine ext rfl
    (d.toGraph.initial_toSimpleGraphSubgraph.trans
      (((d.subgraphAfter 0).toSimpleGraphSubgraph_toGraph _).trans d.subgraphAfter_zero))
    d.start.heq_toSimpleGraph_toGraph fun i ↦ ?_
  refine (d.toGraph.walkAt_toSimpleGraphSubgraph i).trans ?_
  refine (congrArg (fun w : (u : V) × (v : V) × (Graph.ofSimpleGraph H).Walk u v ↦
    (⟨w.1, w.2.1, w.2.2.toSimpleGraph⟩ : (u : V) × (v : V) × H.Walk u v))
    (d.walkAt_toGraph i)).trans ?_
  simp only [Walk.toSimpleGraph_toGraph]
  rfl

/-- Regard an ear decomposition of `⊤ : H.Subgraph` as a full multigraph ear decomposition of
`Graph.ofSimpleGraph H`. -/
def toGraphTop (d : H.EarDecomposition (⊤ : H.Subgraph)) :
    (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H) :=
  d.toGraph.copy Subgraph.top_toGraph

@[simp]
theorem length_toGraphTop (d : H.EarDecomposition (⊤ : H.Subgraph)) :
    d.toGraphTop.length = d.length := by
  simp [toGraphTop]

theorem initial_toGraphTop (d : H.EarDecomposition (⊤ : H.Subgraph)) :
    d.toGraphTop.initial = d.initial.toGraph := by
  rw [toGraphTop, Graph.EarDecomposition.initial_copy, initial_toGraph]

@[simp]
theorem graphAfter_toGraphTop_zero (d : H.EarDecomposition (⊤ : H.Subgraph)) :
    d.toGraphTop.graphAfter 0 = d.initial.toGraph :=
  d.toGraphTop.initial_eq_graphAfter.symm.trans d.initial_toGraphTop

@[simp]
theorem start_isCycle_toGraphTop_iff (d : H.EarDecomposition (⊤ : H.Subgraph)) :
    d.toGraphTop.start.IsCycle ↔ d.start.IsCycle :=
  (d.toGraph.start_isCycle_copy Subgraph.top_toGraph).trans d.start_isCycle_toGraph_iff

@[simp]
theorem isOpen_toGraphTop_iff (d : H.EarDecomposition (⊤ : H.Subgraph)) :
    d.toGraphTop.IsOpen ↔ d.IsOpen :=
  (d.toGraph.isOpen_copy Subgraph.top_toGraph).trans d.isOpen_toGraph_iff

@[simp]
theorem toSimpleGraphTop_toGraphTop (d : H.EarDecomposition (⊤ : H.Subgraph)) :
    d.toGraphTop.toSimpleGraphTop = d := by
  have hlen : d.toGraphTop.toSimpleGraphTop.length = d.length := by simp
  refine ext hlen ?_ ?_ fun i ↦ ?_
  · rw [Graph.EarDecomposition.initial_toSimpleGraphTop, ← Subgraph.toGraph_inj,
      Graph.IsSubgraph.toGraph_toSimpleGraphSubgraph,
      ← Graph.EarDecomposition.initial_eq_graphAfter, initial_toGraphTop]
  · have h0 : d.toGraphTop.graphAfter 0 = d.toGraph.graphAfter 0 :=
      d.toGraph.graphAfter_copy Subgraph.top_toGraph 0
    exact (Graph.EarStart.heq_toSimpleGraph_of_heq h0
      (d.toGraph.heq_start_copy Subgraph.top_toGraph)).trans d.start.heq_toSimpleGraph_toGraph
  · dsimp only [Graph.EarDecomposition.toSimpleGraphTop]
    refine ((d.toGraphTop.toSimpleGraph.walkAt_copy _ i).trans
      (d.toGraphTop.walkAt_toSimpleGraph i)).trans ?_
    have hw : d.toGraphTop.walkAt i =
        ⟨(d.walkAt (i.cast hlen)).1, (d.walkAt (i.cast hlen)).2.1,
          (d.walkAt (i.cast hlen)).2.2.toGraph⟩ :=
      (d.toGraph.walkAt_copy Subgraph.top_toGraph i).trans (d.walkAt_toGraph (i.cast hlen))
    rw [hw]
    simp only [Walk.toSimpleGraph_toGraph]
    rfl

end EarDecomposition

@[simp]
theorem _root_.Graph.EarDecomposition.toGraphTop_toSimpleGraphTop
    (d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)) :
    d.toSimpleGraphTop.toGraphTop = d := by
  rw [EarDecomposition.toGraphTop, Graph.EarDecomposition.toSimpleGraphTop,
    EarDecomposition.copy_toGraph, Graph.EarDecomposition.copy_copy]
  refine Graph.EarDecomposition.ext_of_cast (by simp) (fun k ↦ ?_) ?_ (fun i ↦ ?_)
  · rw [Graph.EarDecomposition.graphAfter_copy]
    exact (d.graphAfter_le _).toGraph_toSimpleGraphSubgraph
  · exact (d.toSimpleGraph.toGraph.heq_start_copy _).trans d.start.heq_toGraph_toSimpleGraph
  · rw [Graph.EarDecomposition.earAt_copy]
    refine Graph.Ear.sigma_ext
      (((d.graphAfter_le _).toGraph_toSimpleGraphSubgraph).trans (d.earAt_fst _).symm) ?_ ?_
    · dsimp only [EarDecomposition.toGraph, Graph.EarDecomposition.toSimpleGraph]
      simp
    · dsimp only [EarDecomposition.toGraph, Graph.EarDecomposition.toSimpleGraph]
      rw [Ear.toWalk_toGraph, Ear.toWalk_copy, Graph.Ear.toWalk_toSimpleGraph,
        Graph.Walk.toGraph_toSimpleGraph]

/-- Canonical equivalence between ear decompositions of `S : H.Subgraph` and multigraph ear
decompositions in `Graph.ofSimpleGraph H` with final graph `S.toGraph`. -/
def earDecompositionEquivOfSimpleGraph (S : H.Subgraph) :
    H.EarDecomposition S ≃ (Graph.ofSimpleGraph H).EarDecomposition S.toGraph where
  toFun := EarDecomposition.toGraph
  invFun := Graph.EarDecomposition.toSimpleGraphSubgraph
  left_inv := EarDecomposition.toSimpleGraphSubgraph_toGraph
  right_inv := Graph.EarDecomposition.toGraph_toSimpleGraphSubgraph

@[simp]
theorem earDecompositionEquivOfSimpleGraph_apply (S : H.Subgraph) (d : H.EarDecomposition S) :
    earDecompositionEquivOfSimpleGraph S d = d.toGraph := (rfl)

@[simp]
theorem earDecompositionEquivOfSimpleGraph_symm_apply (S : H.Subgraph)
    (d : (Graph.ofSimpleGraph H).EarDecomposition S.toGraph) :
    (earDecompositionEquivOfSimpleGraph S).symm d = d.toSimpleGraphSubgraph := (rfl)

/-- Canonical equivalence between ear decompositions of `⊤ : H.Subgraph` and full multigraph ear
decompositions of `Graph.ofSimpleGraph H`. -/
def earDecompositionTopEquivOfSimpleGraph (H : SimpleGraph V) :
    H.EarDecomposition (⊤ : H.Subgraph) ≃
      (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H) where
  toFun := EarDecomposition.toGraphTop
  invFun := Graph.EarDecomposition.toSimpleGraphTop
  left_inv := EarDecomposition.toSimpleGraphTop_toGraphTop
  right_inv := Graph.EarDecomposition.toGraphTop_toSimpleGraphTop

@[simp]
theorem earDecompositionTopEquivOfSimpleGraph_apply (H : SimpleGraph V)
    (d : H.EarDecomposition (⊤ : H.Subgraph)) :
    earDecompositionTopEquivOfSimpleGraph H d = d.toGraphTop := (rfl)

@[simp]
theorem earDecompositionTopEquivOfSimpleGraph_symm_apply (H : SimpleGraph V)
    (d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)) :
    (earDecompositionTopEquivOfSimpleGraph H).symm d = d.toSimpleGraphTop := (rfl)

/-! ### Vertex-started decompositions, start replacement, and normalization on `SimpleGraph` -/

namespace EarDecomposition

variable {S S' : H.Subgraph}

/-- An ear decomposition in a simple graph is *vertex-started* if its initial subgraph is a single
vertex. -/
def IsVertexStart (d : H.EarDecomposition S) : Prop :=
  ∃ v : V, d.initial = H.singletonSubgraph v

theorem isVertexStart_iff (d : H.EarDecomposition S) :
    d.IsVertexStart ↔ ∃ v : V, d.initial = H.singletonSubgraph v := (Iff.rfl)

@[simp]
theorem isVertexStart_toGraph_iff (d : H.EarDecomposition S) :
    d.toGraph.IsVertexStart ↔ d.IsVertexStart := by
  rw [Graph.EarDecomposition.isVertexStart_iff, isVertexStart_iff]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v.1, Subgraph.toGraph_inj.mp ?_⟩
    rw [← initial_toGraph, hv, Subgraph.singletonSubgraph_toGraph]
  · rintro ⟨v, hv⟩
    refine ⟨⟨v, mem_univ v⟩, ?_⟩
    rw [initial_toGraph, hv, Subgraph.singletonSubgraph_toGraph]

@[simp]
theorem isVertexStart_toGraphTop_iff (d : H.EarDecomposition (⊤ : H.Subgraph)) :
    d.toGraphTop.IsVertexStart ↔ d.IsVertexStart :=
  (d.toGraph.isVertexStart_copy Subgraph.top_toGraph).trans d.isVertexStart_toGraph_iff

theorem isVertexStart_iff_not_start_isCycle (d : H.EarDecomposition S) :
    d.IsVertexStart ↔ ¬d.start.IsCycle := by
  rw [← isVertexStart_toGraph_iff, d.toGraph.isVertexStart_iff_not_start_isCycle,
    start_isCycle_toGraph_iff]

@[simp]
theorem isVertexStart_vertex (v : V) : (vertex H v).IsVertexStart :=
  ⟨v, initial_vertex v⟩

@[simp]
theorem not_isVertexStart_cycle {u : V} (c : H.Walk u u) (hc : c.IsCycle) :
    ¬(cycle c hc).IsVertexStart := by
  rw [isVertexStart_iff_not_start_isCycle, not_not]
  exact (isOpen_cycle c hc).start_isCycle

@[simp]
theorem isVertexStart_copy (d : H.EarDecomposition S) (h : S = S') :
    (d.copy h).IsVertexStart ↔ d.IsVertexStart := by
  simp [isVertexStart_iff]

@[simp]
theorem isVertexStart_snoc (d : H.EarDecomposition S) (e : H.Ear S) :
    (d.snoc e).IsVertexStart ↔ d.IsVertexStart := by
  simp [isVertexStart_iff]

@[simp]
theorem isVertexStart_prefix (d : H.EarDecomposition S) (k : Fin (d.length + 1)) :
    (d.prefix k).IsVertexStart ↔ d.IsVertexStart := by
  simp [isVertexStart_iff]

/-- Replay the displayed ears of `d : H.EarDecomposition S` on top of an ear decomposition `d₀` of
`d.initial`. -/
def replaceInitial (d : H.EarDecomposition S) (d₀ : H.EarDecomposition d.initial) :
    H.EarDecomposition S :=
  (d.toGraph.replaceInitial (d₀.toGraph.copy d.initial_toGraph.symm)).toSimpleGraphSubgraph

@[simp]
theorem toGraph_replaceInitial (d : H.EarDecomposition S) (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).toGraph =
      d.toGraph.replaceInitial (d₀.toGraph.copy d.initial_toGraph.symm) :=
  Graph.EarDecomposition.toGraph_toSimpleGraphSubgraph _

@[simp]
theorem length_replaceInitial (d : H.EarDecomposition S) (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).length = d₀.length + d.length :=
  (Graph.EarDecomposition.length_replaceInitial _ _).trans (by simp)

@[simp]
theorem initial_replaceInitial (d : H.EarDecomposition S) (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).initial = d₀.initial := by
  rw [← Subgraph.toGraph_inj, ← initial_toGraph, toGraph_replaceInitial,
    Graph.EarDecomposition.initial_replaceInitial, Graph.EarDecomposition.initial_copy,
    initial_toGraph]

@[simp]
theorem start_isCycle_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).start.IsCycle ↔ d₀.start.IsCycle := by
  rw [← start_isCycle_toGraph_iff, toGraph_replaceInitial,
    Graph.EarDecomposition.start_isCycle_replaceInitial,
    Graph.EarDecomposition.start_isCycle_copy, start_isCycle_toGraph_iff]

@[simp]
theorem isVertexStart_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).IsVertexStart ↔ d₀.IsVertexStart := by
  simp [isVertexStart_iff]

@[simp]
theorem isOpen_replaceInitial (d : H.EarDecomposition S) (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).IsOpen ↔ d₀.IsOpen ∧ ∀ i, d.kindAt i = .«open» := by
  rw [← isOpen_toGraph_iff, toGraph_replaceInitial, Graph.EarDecomposition.isOpen_replaceInitial,
    Graph.EarDecomposition.isOpen_copy, isOpen_toGraph_iff]
  exact and_congr_right fun _ ↦
    ⟨fun h i ↦ EarKind.toGraph_eq_open_iff.mp ((d.kindAt_toGraph i).symm.trans (h i)),
      fun h i ↦ (d.kindAt_toGraph i).trans (EarKind.toGraph_eq_open_iff.mpr (h i))⟩

/-- Normalize any ear decomposition in a simple graph so that it starts at a single vertex,
turning an initial cycle into a first closed ear. -/
def toVertexStart (d : H.EarDecomposition S) : H.EarDecomposition S :=
  d.toGraph.toVertexStart.toSimpleGraphSubgraph

@[simp]
theorem toGraph_toVertexStart (d : H.EarDecomposition S) :
    d.toVertexStart.toGraph = d.toGraph.toVertexStart :=
  Graph.EarDecomposition.toGraph_toSimpleGraphSubgraph _

@[simp]
theorem isVertexStart_toVertexStart (d : H.EarDecomposition S) :
    d.toVertexStart.IsVertexStart := by
  rw [← isVertexStart_toGraph_iff, toGraph_toVertexStart]
  exact d.toGraph.isVertexStart_toVertexStart

@[simp]
theorem not_start_isCycle_toVertexStart (d : H.EarDecomposition S) :
    ¬d.toVertexStart.start.IsCycle :=
  d.toVertexStart.isVertexStart_iff_not_start_isCycle.mp d.isVertexStart_toVertexStart

theorem length_toVertexStart (d : H.EarDecomposition S) :
    d.toVertexStart.length = (if d.start.IsCycle then 1 else 0) + d.length :=
  d.toGraph.length_toVertexStart.trans
    (congrArg (· + d.length) (if_congr d.start_isCycle_toGraph_iff rfl rfl))

theorem toVertexStart_eq_self {d : H.EarDecomposition S} (hd : d.IsVertexStart) :
    d.toVertexStart = d := by
  apply (earDecompositionEquivOfSimpleGraph S).injective
  rw [earDecompositionEquivOfSimpleGraph_apply, earDecompositionEquivOfSimpleGraph_apply,
    toGraph_toVertexStart]
  exact d.toGraph.toVertexStart_eq_self (d.isVertexStart_toGraph_iff.mpr hd)

end EarDecomposition

/-- A subgraph of a simple graph admits an ear decomposition if and only if it admits a
vertex-started ear decomposition. -/
theorem nonempty_earDecomposition_iff_exists_isVertexStart {S : H.Subgraph} :
    Nonempty (H.EarDecomposition S) ↔ ∃ d : H.EarDecomposition S, d.IsVertexStart :=
  ⟨fun ⟨d⟩ ↦ ⟨d.toVertexStart, d.isVertexStart_toVertexStart⟩, fun ⟨d, _⟩ ↦ ⟨d⟩⟩

/-! ### Edge-finite completion and `2`-edge-connectivity characterizations on `SimpleGraph` -/

namespace EarDecomposition

/-- Complete any partial ear decomposition `d : H.EarDecomposition S` in a `2`-edge-connected
simple graph with finitely many edges to an ear decomposition of `⊤`, preserving `d` as a prefix. -/
noncomputable def extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) {S : H.Subgraph}
    (d : H.EarDecomposition S) : H.EarDecomposition (⊤ : H.Subgraph) :=
  (d.toGraph.extend ((Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH)).toSimpleGraphTop

@[simp]
theorem toGraphTop_extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) {S : H.Subgraph}
    (d : H.EarDecomposition S) :
    (d.extend hH).toGraphTop =
      d.toGraph.extend ((Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH) :=
  Graph.EarDecomposition.toGraphTop_toSimpleGraphTop _

theorem length_le_length_extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) {S : H.Subgraph}
    (d : H.EarDecomposition S) : d.length ≤ (d.extend hH).length :=
  d.toGraph.length_le_length_extend ((Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH)

@[simp]
theorem subgraphAfter_extend_castLE [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) {S : H.Subgraph}
    (d : H.EarDecomposition S) (i : Fin (d.length + 1)) :
    (d.extend hH).subgraphAfter
      (Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hH)) i) = d.subgraphAfter i := by
  have hH' := (Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH
  rw [← Subgraph.toGraph_inj]
  dsimp only [extend, Graph.EarDecomposition.toSimpleGraphTop]
  exact ((d.toGraph.extend hH').graphAfter_le _).toGraph_toSimpleGraphSubgraph.trans
    (d.toGraph.graphAfter_extend_castLE hH' i)

theorem initial_extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) {S : H.Subgraph}
    (d : H.EarDecomposition S) : (d.extend hH).initial = d.initial := by
  simpa only [← subgraphAfter_zero, Fin.castLE_zero] using d.subgraphAfter_extend_castLE hH 0

@[simp]
theorem walkAt_extend_castLE [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) {S : H.Subgraph}
    (d : H.EarDecomposition S) (i : Fin d.length) :
    (d.extend hH).walkAt (Fin.castLE (d.length_le_length_extend hH) i) = d.walkAt i := by
  have hH' := (Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH
  let j : Fin (d.toGraph.extend hH').length :=
    Fin.castLE (d.length_le_length_extend hH) i
  have h1 : (d.extend hH).walkAt j =
      ⟨((d.toGraph.extend hH').walkAt j).1,
        ((d.toGraph.extend hH').walkAt j).2.1,
        ((d.toGraph.extend hH').walkAt j).2.2.toSimpleGraph⟩ := by
    dsimp only [extend, Graph.EarDecomposition.toSimpleGraphTop]
    exact ((d.toGraph.extend hH').toSimpleGraph.walkAt_copy
      (Graph.IsSubgraph.ofSimpleGraph_toSimpleGraphSubgraph
        (d.toGraph.extend hH').final_le) j).trans
      ((d.toGraph.extend hH').walkAt_toSimpleGraph j)
  have h2 : (d.toGraph.extend hH').walkAt j = d.toGraph.walkAt i :=
    ((d.toGraph.extend hH').walkAt_eq j).trans
      ((congrArg (fun p : (K : Graph V (Sym2 V)) × (Graph.ofSimpleGraph H).Ear K ↦ p.2.toWalk)
        (d.toGraph.earAt_extend_castLE hH' i)).trans
        (d.toGraph.walkAt_eq i).symm)
  refine h1.trans ?_
  rw [h2, d.walkAt_toGraph i]
  simp [Walk.toSimpleGraph_toGraph]

theorem heq_start_extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) {S : H.Subgraph}
    (d : H.EarDecomposition S) : HEq (d.extend hH).start d.start := by
  have hH' := (Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH
  have h0 : (d.toGraph.extend hH').graphAfter 0 = d.toGraph.graphAfter 0 :=
    d.toGraph.graphAfter_extend_castLE hH' 0
  rw [extend, Graph.EarDecomposition.toSimpleGraphTop, start_copy,
    Graph.EarDecomposition.start_toSimpleGraph]
  exact (Graph.EarStart.heq_toSimpleGraph_of_heq h0
    (d.toGraph.heq_start_extend hH')).trans d.start.heq_toSimpleGraph_toGraph

@[simp]
theorem start_isCycle_extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) {S : H.Subgraph}
    (d : H.EarDecomposition S) : (d.extend hH).start.IsCycle ↔ d.start.IsCycle := by
  rw [← start_isCycle_toGraphTop_iff, toGraphTop_extend, d.toGraph.start_isCycle_extend,
    start_isCycle_toGraph_iff]

@[simp]
theorem isVertexStart_extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) {S : H.Subgraph}
    (d : H.EarDecomposition S) : (d.extend hH).IsVertexStart ↔ d.IsVertexStart := by
  simp [isVertexStart_iff, d.initial_extend hH]

theorem prefix_extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) {S : H.Subgraph}
    (d : H.EarDecomposition S) :
    ((d.extend hH).prefix
      (Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hH)) (Fin.last d.length))).copy
      ((d.subgraphAfter_extend_castLE hH (Fin.last d.length)).trans d.subgraphAfter_last) = d := by
  let k := Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hH)) (Fin.last d.length)
  let hc := (d.subgraphAfter_extend_castLE hH (Fin.last d.length)).trans d.subgraphAfter_last
  have hlen : (((d.extend hH).prefix k).copy hc).length = d.length := by simp [k]
  refine ext hlen (by simp [d.initial_extend hH]) (d.heq_start_extend hH) fun i ↦ ?_
  refine (((d.extend hH).prefix k).walkAt_copy hc i).trans ?_
  refine ((d.extend hH).walkAt_prefix k i).trans ?_
  exact (congrArg (d.extend hH).walkAt (Fin.ext rfl)).trans
    (d.walkAt_extend_castLE hH (i.cast hlen))

end EarDecomposition

/-- Construct an ear decomposition of `⊤` in a `2`-edge-connected simple graph with finitely many
edges starting at a prescribed vertex `v`. -/
noncomputable def IsEdgeConnected.earDecompositionOfVertex [Finite H.edgeSet]
    (hH : H.IsEdgeConnected 2) (v : V) : H.EarDecomposition (⊤ : H.Subgraph) :=
  (EarDecomposition.vertex H v).extend hH

theorem IsEdgeConnected.initial_earDecompositionOfVertex [Finite H.edgeSet]
    (hH : H.IsEdgeConnected 2) (v : V) :
    (hH.earDecompositionOfVertex v).initial = H.singletonSubgraph v :=
  ((EarDecomposition.vertex H v).initial_extend hH).trans (EarDecomposition.initial_vertex v)

@[simp]
theorem IsEdgeConnected.isVertexStart_earDecompositionOfVertex [Finite H.edgeSet]
    (hH : H.IsEdgeConnected 2) (v : V) : (hH.earDecompositionOfVertex v).IsVertexStart := by
  rw [earDecompositionOfVertex, EarDecomposition.isVertexStart_extend]
  exact EarDecomposition.isVertexStart_vertex v

/-- Construct an ear decomposition of `⊤` in a `2`-edge-connected simple graph with finitely many
edges starting from a prescribed cycle `c`. -/
noncomputable def IsEdgeConnected.earDecompositionOfCycle [Finite H.edgeSet]
    (hH : H.IsEdgeConnected 2) {u : V} (c : H.Walk u u) (hc : c.IsCycle) :
    H.EarDecomposition (⊤ : H.Subgraph) :=
  (EarDecomposition.cycle c hc).extend hH

theorem IsEdgeConnected.initial_earDecompositionOfCycle [Finite H.edgeSet]
    (hH : H.IsEdgeConnected 2) {u : V} (c : H.Walk u u) (hc : c.IsCycle) :
    (hH.earDecompositionOfCycle c hc).initial = c.toSubgraph :=
  ((EarDecomposition.cycle c hc).initial_extend hH).trans (EarDecomposition.initial_cycle c hc)

@[simp]
theorem IsEdgeConnected.start_isCycle_earDecompositionOfCycle [Finite H.edgeSet]
    (hH : H.IsEdgeConnected 2) {u : V} (c : H.Walk u u) (hc : c.IsCycle) :
    (hH.earDecompositionOfCycle c hc).start.IsCycle := by
  rw [earDecompositionOfCycle, EarDecomposition.start_isCycle_extend]
  exact (EarDecomposition.isOpen_cycle c hc).start_isCycle

/-- A simple graph on a nonempty vertex type with finitely many edges is `2`-edge-connected if and
only if it admits a vertex-started ear decomposition of `⊤`. -/
theorem isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition_top [Finite H.edgeSet]
    [Nonempty V] :
    H.IsEdgeConnected 2 ↔ ∃ d : H.EarDecomposition (⊤ : H.Subgraph), d.IsVertexStart := by
  rw [H.isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition]
  exact ((earDecompositionTopEquivOfSimpleGraph H).exists_congr fun d ↦
    d.isVertexStart_toGraphTop_iff.symm).symm

/-- A simple graph on a nonempty vertex type with finitely many edges is `2`-edge-connected if and
only if it admits an ear decomposition of `⊤`. -/
theorem isEdgeConnected_two_iff_nonempty_earDecomposition_of_finite_edgeSet [Finite H.edgeSet]
    [Nonempty V] :
    H.IsEdgeConnected 2 ↔ Nonempty (H.EarDecomposition (⊤ : H.Subgraph)) := by
  rw [H.isEdgeConnected_two_iff_nonempty_earDecomposition_ofSimpleGraph]
  exact (earDecompositionTopEquivOfSimpleGraph H).symm.nonempty_congr

/-- A simple graph with finitely many edges is connected and bridgeless if and only if it admits an
ear decomposition of `⊤` (with no separate `[Nonempty V]` hypothesis). -/
theorem connected_and_forall_not_isBridge_iff_nonempty_earDecomposition [Finite H.edgeSet] :
    (H.Connected ∧ ∀ e, ¬H.IsBridge e) ↔ Nonempty (H.EarDecomposition (⊤ : H.Subgraph)) := by
  rw [(earDecompositionTopEquivOfSimpleGraph H).nonempty_congr,
    ← Graph.connected_and_forall_not_isBridge_iff_nonempty_earDecomposition,
    Graph.connected_ofSimpleGraph_iff]
  constructor
  · rintro ⟨hconn, hnb⟩
    exact ⟨hconn, ((Graph.preconnected_and_forall_not_isBridge_ofSimpleGraph_iff H).mpr hnb).2⟩
  · rintro ⟨hconn, hnb⟩
    exact ⟨hconn,
      (Graph.preconnected_and_forall_not_isBridge_ofSimpleGraph_iff H).mp ⟨hconn.preconnected, hnb⟩⟩

end SimpleGraph

/-! ### Open ear decompositions and `2`-vertex-connectivity on `Graph.ofSimpleGraph` -/

namespace Graph

variable {V : Type u} {H : SimpleGraph V}

/-- Every stage of an open ear decomposition in `Graph.ofSimpleGraph H` is `2`-vertex-connected,
with no finiteness assumption. -/
theorem EarDecomposition.IsOpen.isVertexConnected_two_graphAfter {K : Graph V (Sym2 V)}
    {d : (Graph.ofSimpleGraph H).EarDecomposition K} (hd : d.IsOpen) (i : Fin (d.length + 1)) :
    (d.graphAfter i).IsVertexConnected 2 := by
  have hS : (d.toSimpleGraph.subgraphAfter i).coe.IsVertexConnected 2 :=
    (d.isOpen_toSimpleGraph_iff.mpr hd).isVertexConnected_two_subgraphAfter i
  have hIso := (d.graphAfter_le i).toSimpleGraphSubgraph.toSimpleGraphToGraphIso
  have hG : (d.graphAfter_le i).toSimpleGraphSubgraph.toGraph.IsVertexConnected 2 := by
    simpa [Graph.IsVertexConnected] using hIso.isVertexConnected_iff.mp hS
  exact (d.graphAfter_le i).toGraph_toSimpleGraphSubgraph ▸ hG

/-- The final graph of an open ear decomposition in `Graph.ofSimpleGraph H` is `2`-vertex-connected,
with no finiteness assumption. -/
theorem EarDecomposition.IsOpen.isVertexConnected_two_of_ofSimpleGraph {K : Graph V (Sym2 V)}
    {d : (Graph.ofSimpleGraph H).EarDecomposition K} (hd : d.IsOpen) :
    K.IsVertexConnected 2 :=
  d.graphAfter_last ▸ hd.isVertexConnected_two_graphAfter (Fin.last d.length)

/-- **Whitney's open ear characterization on `Graph.ofSimpleGraph H`.** On a finite vertex type,
`Graph.ofSimpleGraph H` is `2`-vertex-connected if and only if it admits an open multigraph ear
decomposition. -/
theorem isVertexConnected_two_ofSimpleGraph_iff_exists_isOpen_earDecomposition [Finite V] :
    (Graph.ofSimpleGraph H).IsVertexConnected 2 ↔
      ∃ d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H), d.IsOpen := by
  rw [Graph.isVertexConnected_ofSimpleGraph_iff, Nat.cast_ofNat,
    H.isVertexConnected_two_iff_exists_isOpen_earDecomposition]
  exact (SimpleGraph.earDecompositionTopEquivOfSimpleGraph H).exists_congr fun d ↦
    d.isOpen_toGraphTop_iff.symm

/-- **Prescribed-cycle open ear decomposition on `Graph.ofSimpleGraph H`.** Every cycle in a finite
`2`-vertex-connected `Graph.ofSimpleGraph H` is the initial graph of an open multigraph ear
decomposition. -/
theorem IsVertexConnected.exists_isOpen_earDecomposition_ofSimpleGraph_initial_eq [Finite V]
    (hH : (Graph.ofSimpleGraph H).IsVertexConnected 2) {u : V}
    (c : (Graph.ofSimpleGraph H).Walk u u) (hc : c.IsCycle) :
    ∃ d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H),
      d.IsOpen ∧ d.initial = (Graph.ofSimpleGraph H).walkGraph c := by
  have hH' : H.IsVertexConnected 2 := (Graph.isVertexConnected_ofSimpleGraph_iff H 2).mp hH
  obtain ⟨d, hd, hinit⟩ :=
    hH'.exists_isOpen_earDecomposition_initial_eq c.toSimpleGraph
      ((Walk.isCycle_toSimpleGraph_iff c).mpr hc)
  refine ⟨d.toGraphTop, d.isOpen_toGraphTop_iff.mpr hd, ?_⟩
  rw [SimpleGraph.EarDecomposition.initial_toGraphTop, hinit,
    ← c.walkGraph_ofSimpleGraph_eq_toGraph]

/-- **Prescribed-edge open ear decomposition on `Graph.ofSimpleGraph H`.** Every edge of a finite
`2`-vertex-connected `Graph.ofSimpleGraph H` lies in the initial cycle of an open multigraph ear
decomposition. -/
theorem IsVertexConnected.exists_isOpen_earDecomposition_ofSimpleGraph_mem_edgeSet_initial
    [Finite V] (hH : (Graph.ofSimpleGraph H).IsVertexConnected 2) {e : Sym2 V}
    (he : e ∈ E(Graph.ofSimpleGraph H)) :
    ∃ d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H),
      d.IsOpen ∧ e ∈ E(d.initial) := by
  have hH' : H.IsVertexConnected 2 := (Graph.isVertexConnected_ofSimpleGraph_iff H 2).mp hH
  have he' : e ∈ H.edgeSet := by simpa only [Graph.edgeSet_ofSimpleGraph] using he
  obtain ⟨d, hd, hmem⟩ := hH'.exists_isOpen_earDecomposition_mem_edgeSet_initial he'
  refine ⟨d.toGraphTop, d.isOpen_toGraphTop_iff.mpr hd, ?_⟩
  simpa only [SimpleGraph.EarDecomposition.initial_toGraphTop,
    SimpleGraph.Subgraph.edgeSet_toGraph] using hmem

end Graph
