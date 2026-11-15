/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Characterization
public import TauCeti.Combinatorics.Graph.Connectivity.Subgraph
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Open

/-!
# Transporting ear decompositions between simple graphs and multigraphs

Mathlib's `SimpleGraph` and `Graph` give rise to two ear-decomposition data types:
`SimpleGraph.EarDecomposition H S`, indexed by a bundled subgraph `S : H.Subgraph`, and
`Graph.EarDecomposition G K`, indexed by a multigraph subgraph `K ≤ G`. On a multigraph, a closed
ear must explicitly avoid edges of `K` because a loop at the base vertex or a parallel edge can
meet `K` only at the base vertex while reusing an edge of `K`. On `Graph.ofSimpleGraph H`, by
contrast, every edge is determined by its two distinct endpoints, so any closed walk meeting `V(K)`
only at its base vertex automatically avoids `E(K)`
(`Graph.Walk.edges_notMem_edgeSet_of_le_ofSimpleGraph`).

Using the subgraph order isomorphism `SimpleGraph.subgraphOfSimpleGraphOrderIso`, this file builds
two-sided equivalences between the simple-graph and multigraph ear data over `Graph.ofSimpleGraph H`
for ear kinds, individual ears, initial stages, and full ear decompositions—preserving lengths,
prefix subgraphs, initial witnesses, ear kinds, ear walks, openness, vertex starts, and the
`vertex`, `cycle`, `copy`, `snoc`, and `prefix` combinators.

Transporting multigraph operations across these equivalences supplies initial-stage replacement
(`SimpleGraph.EarDecomposition.replaceInitial`), finiteness-free normalization of arbitrary ear
decompositions to vertex-started ones (`SimpleGraph.EarDecomposition.toVertexStart`), and—assuming
only `[Finite H.edgeSet]`, even on an infinite ambient vertex type—data-level completion of any
partial ear decomposition (`SimpleGraph.EarDecomposition.extend`), prescribed-vertex and
prescribed-cycle ear decompositions of `2`-edge-connected simple graphs, the bridgeless connected
ear characterization
(`SimpleGraph.connected_and_forall_not_isBridge_iff_nonempty_earDecomposition`), and Whitney's open
ear characterization on `Graph.ofSimpleGraph H`
(`SimpleGraph.isVertexConnected_two_iff_exists_isOpen_earDecomposition_ofSimpleGraph`).

## Main definitions

* `SimpleGraph.earKindEquivGraph`: equivalence `SimpleGraph.EarKind ≃ Graph.EarKind`.
* `Graph.Ear.closedOfSimpleGraph`: construct a closed ear of `Graph.ofSimpleGraph H` from the cycle
  and vertex-intersection conditions alone, deriving edge disjointness automatically.
* `SimpleGraph.earEquivOfSimpleGraph`: equivalence
  `H.Ear S ≃ (Graph.ofSimpleGraph H).Ear S.toGraph`.
* `SimpleGraph.earStartEquivOfSimpleGraph`: equivalence
  `H.EarStart S ≃ (Graph.ofSimpleGraph H).EarStart S.toGraph`.
* `SimpleGraph.earDecompositionEquivOfSimpleGraph`,
  `SimpleGraph.earDecompositionTopEquivOfSimpleGraph`: equivalences
  `H.EarDecomposition S ≃ (Graph.ofSimpleGraph H).EarDecomposition S.toGraph` and
  `H.EarDecomposition ⊤ ≃ (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)`.
* `SimpleGraph.EarDecomposition.IsVertexStart`, `SimpleGraph.EarDecomposition.replaceInitial`,
  `SimpleGraph.EarDecomposition.toVertexStart`: vertex-start predicate, initial-stage replacement,
  and vertex-start normalization on `SimpleGraph.EarDecomposition`.
* `SimpleGraph.EarDecomposition.extend`, `SimpleGraph.IsEdgeConnected.earDecompositionOfVertex`,
  `SimpleGraph.IsEdgeConnected.earDecompositionOfCycle`: under `[Finite H.edgeSet]`, complete any
  partial ear decomposition of a `2`-edge-connected simple graph to `⊤`.

## References

* H. Whitney, *Congruent graphs and the connectivity of graphs*, Amer. J. Math. 54 (1932),
  150--168.
* H. E. Robbins, *A theorem on graphs, with an application to a problem of traffic control*,
  Amer. Math. Monthly 46 (1939), 281--283.
* R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer, 2017,
  Section 3.1.
-/

public section

open Set
open scoped Graph Sym2

universe u

/-! ### Equivalence of ear kinds -/

namespace SimpleGraph.EarKind

/-- Convert a simple-graph ear kind to the corresponding multigraph ear kind. -/
def toGraph : SimpleGraph.EarKind → Graph.EarKind
  | .«open» => .open
  | .closed => .closed

@[simp] theorem toGraph_open : (EarKind.«open»).toGraph = .open := (rfl)
@[simp] theorem toGraph_closed : (EarKind.closed).toGraph = .closed := (rfl)

end SimpleGraph.EarKind

namespace Graph.EarKind

/-- Convert a multigraph ear kind (`open` or `closed`) to the corresponding
`SimpleGraph.EarKind`. -/
def toSimpleGraph : Graph.EarKind → SimpleGraph.EarKind
  | .open => .open
  | .closed => .closed

@[simp] theorem toSimpleGraph_open : toSimpleGraph .open = .open := (rfl)
@[simp] theorem toSimpleGraph_closed : toSimpleGraph .closed = .closed := (rfl)

@[simp] theorem toGraph_toSimpleGraph (k : Graph.EarKind) : k.toSimpleGraph.toGraph = k := by
  cases k <;> simp

@[simp]
theorem toSimpleGraph_eq_open_iff {k : Graph.EarKind} : k.toSimpleGraph = .open ↔ k = .open := by
  cases k <;> simp

@[simp]
theorem toSimpleGraph_eq_closed_iff {k : Graph.EarKind} :
    k.toSimpleGraph = .closed ↔ k = .closed := by
  cases k <;> simp

theorem toSimpleGraph_injective : Function.Injective toSimpleGraph := by
  intro k l h
  cases k <;> cases l <;> simp_all

@[simp]
theorem toSimpleGraph_inj {k l : Graph.EarKind} :
    k.toSimpleGraph = l.toSimpleGraph ↔ k = l :=
  toSimpleGraph_injective.eq_iff

end Graph.EarKind

namespace SimpleGraph

@[simp] theorem EarKind.toSimpleGraph_toGraph (k : SimpleGraph.EarKind) :
    k.toGraph.toSimpleGraph = k := by cases k <;> simp

@[simp] theorem EarKind.toGraph_eq_open_iff {k : SimpleGraph.EarKind} :
    k.toGraph = .open ↔ k = .«open» := by cases k <;> simp

@[simp] theorem EarKind.toGraph_eq_closed_iff {k : SimpleGraph.EarKind} :
    k.toGraph = .closed ↔ k = .closed := by cases k <;> simp

/-- Equivalence between `SimpleGraph.EarKind` and `Graph.EarKind`. -/
def earKindEquivGraph : SimpleGraph.EarKind ≃ Graph.EarKind where
  toFun := EarKind.toGraph
  invFun := Graph.EarKind.toSimpleGraph
  left_inv := EarKind.toSimpleGraph_toGraph
  right_inv := Graph.EarKind.toGraph_toSimpleGraph

@[simp] theorem earKindEquivGraph_apply (k : SimpleGraph.EarKind) :
    earKindEquivGraph k = k.toGraph := (rfl)

@[simp] theorem earKindEquivGraph_symm_apply (k : Graph.EarKind) :
    earKindEquivGraph.symm k = k.toSimpleGraph := (rfl)

end SimpleGraph

/-! ### Unused-edge implication for closed ears on `Graph.ofSimpleGraph` -/

namespace Graph

variable {α : Type u} {H : SimpleGraph α} {K : Graph α (Sym2 α)}

/-- In `Graph.ofSimpleGraph H`, any closed walk meeting a subgraph `K ≤ Graph.ofSimpleGraph H` only
at its base vertex uses no edge of `K`, because every link in `Graph.ofSimpleGraph H` has distinct
endpoints and therefore has at least one endpoint outside `V(K)`. -/
theorem Walk.edges_notMem_edgeSet_of_le_ofSimpleGraph (hK : K ≤ Graph.ofSimpleGraph H) {s : α}
    {c : (Graph.ofSimpleGraph H).Walk s s} (hint : ∀ x ∈ c.support, x ≠ s → x ∉ V(K))
    {e : Sym2 α} (he : e ∈ c.edges) : e ∉ E(K) := by
  rw [← K.edgeSet_toSimpleGraphSubgraph hK]
  exact SimpleGraph.Ear.closed_edges_notMem_edgeSet (H := K.toSimpleGraphSubgraph hK)
    (c := c.toSimpleGraph)
    (fun w hw hws ↦ by
      rw [K.verts_toSimpleGraphSubgraph hK]
      exact hint w ((Walk.support_toSimpleGraph c) ▸ hw) hws)
    ((Walk.edges_toSimpleGraph c).symm ▸ he)

/-- Construct a closed ear of `Graph.ofSimpleGraph H` over `K ≤ Graph.ofSimpleGraph H` from the
cycle and vertex-intersection conditions alone; the unused-edge obligation is discharged
automatically by `Walk.edges_notMem_edgeSet_of_le_ofSimpleGraph`. -/
def Ear.closedOfSimpleGraph (hK : K ≤ Graph.ofSimpleGraph H) {s : α}
    (walk : (Graph.ofSimpleGraph H).Walk s s) (isCycle : walk.IsCycle) (base_mem : s ∈ V(K))
    (internal_new : ∀ x ∈ walk.support, x ≠ s → x ∉ V(K)) : (Graph.ofSimpleGraph H).Ear K :=
  .closed hK walk isCycle base_mem internal_new fun _ he ↦
    walk.edges_notMem_edgeSet_of_le_ofSimpleGraph hK internal_new he

@[simp] theorem Ear.kind_closedOfSimpleGraph (hK : K ≤ Graph.ofSimpleGraph H) {s : α}
    (walk : (Graph.ofSimpleGraph H).Walk s s) (isCycle : walk.IsCycle) (base_mem : s ∈ V(K))
    (internal_new : ∀ x ∈ walk.support, x ≠ s → x ∉ V(K)) :
    (Ear.closedOfSimpleGraph hK walk isCycle base_mem internal_new).kind = .closed := by
  rw [Ear.closedOfSimpleGraph, Ear.kind_closed]

@[simp] theorem Ear.toWalk_closedOfSimpleGraph (hK : K ≤ Graph.ofSimpleGraph H) {s : α}
    (walk : (Graph.ofSimpleGraph H).Walk s s) (isCycle : walk.IsCycle) (base_mem : s ∈ V(K))
    (internal_new : ∀ x ∈ walk.support, x ≠ s → x ∉ V(K)) :
    (Ear.closedOfSimpleGraph hK walk isCycle base_mem internal_new).toWalk = ⟨s, s, walk⟩ := by
  rw [Ear.closedOfSimpleGraph, Ear.toWalk_closed]

@[simp] theorem Ear.toGraph_closedOfSimpleGraph (hK : K ≤ Graph.ofSimpleGraph H) {s : α}
    (walk : (Graph.ofSimpleGraph H).Walk s s) (isCycle : walk.IsCycle) (base_mem : s ∈ V(K))
    (internal_new : ∀ x ∈ walk.support, x ≠ s → x ∉ V(K)) :
    (Ear.closedOfSimpleGraph hK walk isCycle base_mem internal_new).toGraph =
      (Graph.ofSimpleGraph H).walkGraph walk := by
  rw [Ear.closedOfSimpleGraph, Ear.toGraph_closed]

end Graph

/-! ### Equivalence of individual ears -/

namespace SimpleGraph.Ear

variable {α : Type u} {H : SimpleGraph α} {S : H.Subgraph}

/-- Regard a simple-graph ear `e : H.Ear S` as a multigraph ear of `Graph.ofSimpleGraph H` over
`S.toGraph`. -/
def toGraph : H.Ear S → (Graph.ofSimpleGraph H).Ear S.toGraph
  | .«open» p hp hu hv huv hint hedge =>
      .open S.toGraph_le_ofSimpleGraph p.toGraph ((SimpleGraph.Walk.isPath_toGraph_iff p).mpr hp)
        (S.vertexSet_toGraph.symm ▸ hu) (S.vertexSet_toGraph.symm ▸ hv) huv
        (fun x hx hxu hxv ↦ S.vertexSet_toGraph.symm ▸
          hint x ((SimpleGraph.Walk.support_toGraph p) ▸ hx) hxu hxv)
        (fun f hf ↦ S.edgeSet_toGraph.symm ▸ hedge f ((SimpleGraph.Walk.edges_toGraph p) ▸ hf))
  | .closed c hc hu hint =>
      Graph.Ear.closedOfSimpleGraph S.toGraph_le_ofSimpleGraph c.toGraph
        ((SimpleGraph.Walk.isCycle_toGraph_iff c).mpr hc) (S.vertexSet_toGraph.symm ▸ hu)
        (fun x hx hxu ↦ S.vertexSet_toGraph.symm ▸
          hint x ((SimpleGraph.Walk.support_toGraph c) ▸ hx) hxu)

@[simp] theorem kind_toGraph (e : H.Ear S) : e.toGraph.kind = e.kind.toGraph := by
  cases e <;> simp [toGraph]

@[simp] theorem toWalk_toGraph (e : H.Ear S) :
    e.toGraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toGraph⟩ := by
  cases e with
  | «open» => rw [toWalk_open]; simp [toGraph]
  | closed => rw [toWalk_closed]; simp [toGraph]

@[simp] theorem toGraph_toGraph (e : H.Ear S) :
    Graph.Ear.toGraph e.toGraph = e.toSubgraph.toGraph := by
  cases e <;> simp [toGraph, SimpleGraph.Walk.toGraph_toSubgraph]

@[simp] theorem add_toGraph (e : H.Ear S) : e.toGraph.add = e.adjoin.toGraph :=
  Graph.ext (by simp [toGraph_toGraph]) fun _ _ _ ↦ by simp [toGraph_toGraph, and_or_left]

end SimpleGraph.Ear

namespace Graph.Ear

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Transport an ear of `Graph.ofSimpleGraph G` to an ear over the corresponding simple
subgraph. -/
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
theorem toSimpleGraph_open {x y : V} (hKG : K ≤ Graph.ofSimpleGraph G)
    (p : (Graph.ofSimpleGraph G).Walk x y) (hp : p.IsPath) (hx : x ∈ K.vertexSet)
    (hy : y ∈ K.vertexSet) (hxy : x ≠ y)
    (hinter : ∀ z ∈ p.support, z ≠ x → z ≠ y → z ∉ K.vertexSet)
    (hedge : ∀ f ∈ p.edges, f ∉ K.edgeSet) :
    (Graph.Ear.open hKG p hp hx hy hxy hinter hedge).toSimpleGraph =
      SimpleGraph.Ear.open p.toSimpleGraph (p.isPath_toSimpleGraph_iff.mpr hp)
        (by simpa using hx) (by simpa using hy) hxy
        (by simpa using hinter) (by simpa using hedge) := (rfl)

@[simp]
theorem toSimpleGraph_closed {x : V} (hKG : K ≤ Graph.ofSimpleGraph G)
    (p : (Graph.ofSimpleGraph G).Walk x x) (hp : p.IsCycle) (hx : x ∈ K.vertexSet)
    (hinter : ∀ z ∈ p.support, z ≠ x → z ∉ K.vertexSet)
    (hedge : ∀ f ∈ p.edges, f ∉ K.edgeSet) :
    (Graph.Ear.closed hKG p hp hx hinter hedge).toSimpleGraph =
      SimpleGraph.Ear.closed p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)
        (by simpa using hx) (by simpa using hinter) := (rfl)

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

/-- Transport identifies the graph traced by an ear with the simple subgraph traced by the
transported ear. -/
@[simp]
theorem toSimpleGraphSubgraph_toGraph (e : (Graph.ofSimpleGraph G).Ear K)
    (h : e.toGraph ≤ Graph.ofSimpleGraph G) :
    e.toGraph.toSimpleGraphSubgraph h = e.toSimpleGraph.toSubgraph := by
  cases e with
  | «open» hKG p hp hs ht hst hinter hedge => simp
  | closed hKG p hp hs hinter hedge => simp

/-- Transport commutes with adjoining an ear to its base graph. -/
@[simp]
theorem toSimpleGraphSubgraph_add (e : (Graph.ofSimpleGraph G).Ear K)
    (hAdd : e.add ≤ Graph.ofSimpleGraph G) :
    e.add.toSimpleGraphSubgraph hAdd = e.toSimpleGraph.adjoin := by
  ext x y
  · simp only [Graph.verts_toSimpleGraphSubgraph, Graph.Ear.vertexSet_add,
      SimpleGraph.Ear.verts_adjoin, Set.mem_union]
    rw [← Graph.verts_toSimpleGraphSubgraph e.toGraph e.toGraph_le,
      e.toSimpleGraphSubgraph_toGraph]
  · rw [← SimpleGraph.Subgraph.mem_edgeSet, ← SimpleGraph.Subgraph.mem_edgeSet]
    simp only [Graph.edgeSet_toSimpleGraphSubgraph, Graph.Ear.edgeSet_add,
      SimpleGraph.Ear.edgeSet_adjoin, Set.mem_union]
    rw [← Graph.edgeSet_toSimpleGraphSubgraph e.toGraph e.toGraph_le,
      e.toSimpleGraphSubgraph_toGraph]

end Graph.Ear

namespace SimpleGraph

variable {α : Type u}

/-- Ears of `H` over `S : H.Subgraph` correspond bijectively to multigraph ears of
`Graph.ofSimpleGraph H` over `S.toGraph`. -/
def earEquivOfSimpleGraph (H : SimpleGraph α) (S : H.Subgraph) :
    H.Ear S ≃ (Graph.ofSimpleGraph H).Ear S.toGraph where
  toFun e := e.toGraph
  invFun e := e.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph e.base_le)
  left_inv e := SimpleGraph.Ear.ext <| by
    rw [SimpleGraph.Ear.toWalk_copy, Graph.Ear.toWalk_toSimpleGraph,
      SimpleGraph.Ear.toWalk_toGraph]
    rcases e.toWalk with ⟨_, _, _⟩; simp
  right_inv e := Graph.Ear.ext _ _ <| by
    rw [SimpleGraph.Ear.toWalk_toGraph, SimpleGraph.Ear.toWalk_copy,
      Graph.Ear.toWalk_toSimpleGraph]
    rcases e.toWalk with ⟨_, _, _⟩; simp

@[simp] theorem earEquivOfSimpleGraph_apply (H : SimpleGraph α) (S : H.Subgraph) (e : H.Ear S) :
    H.earEquivOfSimpleGraph S e = e.toGraph := (rfl)

@[simp] theorem earEquivOfSimpleGraph_symm_apply (H : SimpleGraph α) (S : H.Subgraph)
    (e : (Graph.ofSimpleGraph H).Ear S.toGraph) :
    (H.earEquivOfSimpleGraph S).symm e =
      e.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph e.base_le) := (rfl)

end SimpleGraph

/-! ### Equivalence of initial stages -/

namespace SimpleGraph.EarStart

variable {α : Type u} {H : SimpleGraph α} {S : H.Subgraph}

/-- Whether an initial witness `s : H.EarStart S` is a cycle is decidable by case analysis. -/
instance instDecidableIsCycle : (s : H.EarStart S) → Decidable s.IsCycle
  | .vertex v => isFalse (isCycle_vertex v).mp
  | .cycle c hc => isTrue ((isCycle_cycle c hc).mpr trivial)

/-- Convert a simple-graph initial witness `H.EarStart S` to a multigraph initial witness
`(Graph.ofSimpleGraph H).EarStart S.toGraph`. -/
def toGraph : H.EarStart S → (Graph.ofSimpleGraph H).EarStart S.toGraph
  | .vertex v => (Subgraph.toGraph_singletonSubgraph (G := H) v).symm ▸ .vertex ⟨v, mem_univ v⟩
  | .cycle c hc =>
      c.toGraph_toSubgraph.symm ▸ .cycle c.toGraph ((SimpleGraph.Walk.isCycle_toGraph_iff c).mpr hc)

theorem heq_toGraph_vertex (v : α) :
    HEq (EarStart.vertex (G := H) v).toGraph
      (Graph.EarStart.vertex (G := Graph.ofSimpleGraph H) ⟨v, mem_univ v⟩) := by
  rw [toGraph]; exact eqRec_heq _ _

theorem heq_toGraph_cycle {u : α} (c : H.Walk u u) (hc : c.IsCycle) :
    HEq (EarStart.cycle c hc).toGraph
      (Graph.EarStart.cycle c.toGraph ((SimpleGraph.Walk.isCycle_toGraph_iff c).mpr hc)) := by
  rw [toGraph]; exact eqRec_heq _ _

@[simp] theorem isCycle_toGraph (s : H.EarStart S) : s.toGraph.IsCycle ↔ s.IsCycle := by
  cases s with
  | vertex v =>
      exact (Graph.EarStart.isCycle_iff_of_heq (Subgraph.toGraph_singletonSubgraph v)
        (heq_toGraph_vertex v)).trans (by simp)
  | cycle c hc =>
      exact (Graph.EarStart.isCycle_iff_of_heq c.toGraph_toSubgraph
        (heq_toGraph_cycle c hc)).trans (by simp)

end SimpleGraph.EarStart

namespace Graph.EarStart

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Transport the initial vertex or cycle of a multigraph ear decomposition to the corresponding
simple subgraph. -/
def toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    G.EarStart (K.toSimpleGraphSubgraph s.le) := by
  cases s with
  | vertex v =>
      exact (Graph.toSimpleGraphSubgraph_noEdge_singleton v.1
        (Graph.EarStart.vertex v).le).symm ▸ .vertex v.1
  | cycle p hp =>
      exact (Graph.Walk.toSimpleGraphSubgraph_walkGraph p
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

namespace SimpleGraph

variable {α : Type u}

private theorem earStart_toSimpleGraph_heq_of_heq {H : SimpleGraph α}
    {K₁ K₂ : Graph α (Sym2 α)} {s₁ : (Graph.ofSimpleGraph H).EarStart K₁}
    {s₂ : (Graph.ofSimpleGraph H).EarStart K₂} (hK : K₁ = K₂) (hs : HEq s₁ s₂) :
    HEq s₁.toSimpleGraph s₂.toSimpleGraph := by subst hK; cases eq_of_heq hs; rfl

private theorem earStart_toGraph_heq_of_heq {H : SimpleGraph α}
    {S₁ S₂ : H.Subgraph} {s₁ : H.EarStart S₁} {s₂ : H.EarStart S₂}
    (hS : S₁ = S₂) (hs : HEq s₁ s₂) :
    HEq s₁.toGraph s₂.toGraph := by subst hS; cases eq_of_heq hs; rfl

private theorem simpleGraph_earStart_cycle_heq {H : SimpleGraph α} {u : α}
    {c₁ c₂ : H.Walk u u} (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle) (h : c₁ = c₂) :
    HEq (SimpleGraph.EarStart.cycle c₁ hc₁) (SimpleGraph.EarStart.cycle c₂ hc₂) := by subst h; rfl

private theorem graph_earStart_cycle_heq {G : Graph α (Sym2 α)} {u : α}
    {c₁ c₂ : G.Walk u u} (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle) (h : c₁ = c₂) :
    HEq (Graph.EarStart.cycle c₁ hc₁) (Graph.EarStart.cycle c₂ hc₂) := by subst h; rfl

private theorem toSimpleGraph_toGraph_earStart_heq {H : SimpleGraph α}
    {S : H.Subgraph} (s : H.EarStart S) : HEq s.toGraph.toSimpleGraph s := by
  cases s with
  | vertex v =>
      exact (earStart_toSimpleGraph_heq_of_heq (Subgraph.toGraph_singletonSubgraph v)
        (EarStart.heq_toGraph_vertex v)).trans (Graph.EarStart.heq_toSimpleGraph_vertex _)
  | cycle c hc =>
      exact (earStart_toSimpleGraph_heq_of_heq c.toGraph_toSubgraph
        (EarStart.heq_toGraph_cycle c hc)).trans
        ((Graph.EarStart.heq_toSimpleGraph_cycle _ _).trans
          (simpleGraph_earStart_cycle_heq _ _ (SimpleGraph.Walk.toSimpleGraph_toGraph c)))

private theorem toGraph_toSimpleGraph_earStart_heq {H : SimpleGraph α}
    {K : Graph α (Sym2 α)} (s : (Graph.ofSimpleGraph H).EarStart K) :
    HEq s.toSimpleGraph.toGraph s := by
  cases s with
  | vertex v =>
      refine (earStart_toGraph_heq_of_heq
        (Graph.toSimpleGraphSubgraph_noEdge_singleton v.1 _)
        (Graph.EarStart.heq_toSimpleGraph_vertex v)).trans ?_
      exact (EarStart.heq_toGraph_vertex v.1).trans
        (by rw [show (⟨v.1, mem_univ v.1⟩ : V(Graph.ofSimpleGraph H)) = v from Subtype.ext rfl])
  | cycle walk isCycle =>
      exact (earStart_toGraph_heq_of_heq (walk.toSimpleGraphSubgraph_walkGraph _)
        (Graph.EarStart.heq_toSimpleGraph_cycle walk isCycle)).trans
        ((EarStart.heq_toGraph_cycle _ _).trans
          (graph_earStart_cycle_heq _ _ (Graph.Walk.toGraph_toSimpleGraph walk)))

/-- Initial witnesses `H.EarStart S` correspond bijectively to multigraph initial witnesses
`(Graph.ofSimpleGraph H).EarStart S.toGraph`. -/
def earStartEquivOfSimpleGraph (H : SimpleGraph α) (S : H.Subgraph) :
    H.EarStart S ≃ (Graph.ofSimpleGraph H).EarStart S.toGraph where
  toFun s := s.toGraph
  invFun s := (S.toSimpleGraphSubgraph_toGraph s.le) ▸ s.toSimpleGraph
  left_inv s := eq_of_heq ((eqRec_heq _ _).trans (toSimpleGraph_toGraph_earStart_heq s))
  right_inv s := eq_of_heq ((earStart_toGraph_heq_of_heq
    (S.toSimpleGraphSubgraph_toGraph s.le).symm (eqRec_heq _ _)).trans
    (toGraph_toSimpleGraph_earStart_heq s))

@[simp] theorem earStartEquivOfSimpleGraph_apply (H : SimpleGraph α) (S : H.Subgraph)
    (s : H.EarStart S) : H.earStartEquivOfSimpleGraph S s = s.toGraph := (rfl)

@[simp] theorem earStartEquivOfSimpleGraph_symm_apply (H : SimpleGraph α) (S : H.Subgraph)
    (s : (Graph.ofSimpleGraph H).EarStart S.toGraph) :
    (H.earStartEquivOfSimpleGraph S).symm s =
      (S.toSimpleGraphSubgraph_toGraph s.le) ▸ s.toSimpleGraph := (rfl)

end SimpleGraph

/-! ### Equivalence of ear decompositions and prefix API preservation -/

namespace SimpleGraph.EarDecomposition

variable {α : Type u} {H : SimpleGraph α} {S : H.Subgraph}

/-- An ear decomposition of a simple-graph subgraph starts from a single vertex when its initial
subgraph is a singleton subgraph `H.singletonSubgraph v`. -/
def IsVertexStart (d : H.EarDecomposition S) : Prop := ∃ v : α, d.initial = H.singletonSubgraph v

theorem isVertexStart_iff (d : H.EarDecomposition S) :
    d.IsVertexStart ↔ ∃ v : α, d.initial = H.singletonSubgraph v := (Iff.rfl)

/-- Transport a simple-graph ear decomposition `d : H.EarDecomposition S` to an ear decomposition of
`S.toGraph` in `Graph.ofSimpleGraph H`. -/
def toGraph (d : H.EarDecomposition S) : (Graph.ofSimpleGraph H).EarDecomposition S.toGraph where
  length := d.length
  graphAfter k := (d.subgraphAfter k).toGraph
  start := d.start.toGraph
  earAt i := ⟨(d.subgraphAfter i.castSucc).toGraph, (d.earAt i).toGraph⟩
  earAt_fst _ := rfl
  graphAfter_succ i :=
    (congrArg Subgraph.toGraph (d.subgraphAfter_succ i)).trans (d.earAt i).add_toGraph.symm
  graphAfter_last := congrArg Subgraph.toGraph d.subgraphAfter_last

@[simp] theorem length_toGraph (d : H.EarDecomposition S) : d.toGraph.length = d.length := (rfl)

@[simp] theorem graphAfter_toGraph (d : H.EarDecomposition S) (k : Fin (d.toGraph.length + 1)) :
    d.toGraph.graphAfter k =
      (d.subgraphAfter (Fin.cast (congrArg (· + 1) (length_toGraph d)) k)).toGraph := (rfl)

theorem initial_toGraph (d : H.EarDecomposition S) : d.toGraph.initial = d.initial.toGraph := by
  rw [Graph.EarDecomposition.initial_eq_graphAfter, graphAfter_toGraph]
  exact congrArg Subgraph.toGraph d.subgraphAfter_zero

theorem heq_start_toGraph (d : H.EarDecomposition S) : HEq d.toGraph.start d.start.toGraph :=
  HEq.rfl

@[simp] theorem start_isCycle_toGraph (d : H.EarDecomposition S) :
    d.toGraph.start.IsCycle ↔ d.start.IsCycle := by
  refine (Graph.EarStart.isCycle_iff_of_heq ?_ d.heq_start_toGraph).trans d.start.isCycle_toGraph
  rw [graphAfter_toGraph]; rfl

@[simp] theorem isVertexStart_toGraph_iff (d : H.EarDecomposition S) :
    d.toGraph.IsVertexStart ↔ d.IsVertexStart := by
  rw [Graph.EarDecomposition.isVertexStart_iff, isVertexStart_iff, initial_toGraph]
  exact ⟨fun ⟨v, hv⟩ ↦
      ⟨v.1, Subgraph.toGraph_injective (hv.trans (Subgraph.toGraph_singletonSubgraph v.1).symm)⟩,
    fun ⟨v, hv⟩ ↦ ⟨⟨v, mem_univ v⟩, by rw [hv, Subgraph.toGraph_singletonSubgraph]⟩⟩

theorem isVertexStart_iff_not_start_isCycle (d : H.EarDecomposition S) :
    d.IsVertexStart ↔ ¬ d.start.IsCycle := by
  rw [← isVertexStart_toGraph_iff, Graph.EarDecomposition.isVertexStart_iff_not_start_isCycle,
    start_isCycle_toGraph]

@[simp] theorem isVertexStart_vertex (v : α) : (vertex H v).IsVertexStart := ⟨v, initial_vertex v⟩

@[simp] theorem not_isVertexStart_cycle {u : α} (c : H.Walk u u) (hc : c.IsCycle) :
    ¬ (cycle c hc).IsVertexStart := by
  rw [isVertexStart_iff_not_start_isCycle]; exact not_not_intro (isOpen_cycle c hc).start_isCycle

@[simp] theorem isVertexStart_copy {S' : H.Subgraph} (d : H.EarDecomposition S) (h : S = S') :
    (d.copy h).IsVertexStart ↔ d.IsVertexStart := by simp [isVertexStart_iff]

@[simp] theorem isVertexStart_snoc (d : H.EarDecomposition S) (e : H.Ear S) :
    (d.snoc e).IsVertexStart ↔ d.IsVertexStart := by simp [isVertexStart_iff]

@[simp] theorem isVertexStart_prefix (d : H.EarDecomposition S) (k : Fin (d.length + 1)) :
    (d.prefix k).IsVertexStart ↔ d.IsVertexStart := by simp [isVertexStart_iff]

@[simp] theorem earAt_toGraph (d : H.EarDecomposition S) (i : Fin d.toGraph.length) :
    d.toGraph.earAt i =
      ⟨(d.subgraphAfter (Fin.cast (length_toGraph d) i).castSucc).toGraph,
        (d.earAt (Fin.cast (length_toGraph d) i)).toGraph⟩ := (rfl)

theorem kindAt_toGraph (d : H.EarDecomposition S) (i : Fin d.toGraph.length) :
    d.toGraph.kindAt i = (d.kindAt (Fin.cast (length_toGraph d) i)).toGraph := by
  rw [Graph.EarDecomposition.kindAt_eq, earAt_toGraph, Ear.kind_toGraph, ← kindAt_def]

theorem walkAt_toGraph (d : H.EarDecomposition S) (i : Fin d.toGraph.length) :
    d.toGraph.walkAt i =
      ⟨(d.walkAt (Fin.cast (length_toGraph d) i)).1,
        (d.walkAt (Fin.cast (length_toGraph d) i)).2.1,
        (d.walkAt (Fin.cast (length_toGraph d) i)).2.2.toGraph⟩ := by
  rw [Graph.EarDecomposition.walkAt_eq, earAt_toGraph, Ear.toWalk_toGraph, ← walkAt_def]

@[simp] theorem isOpen_toGraph_iff (d : H.EarDecomposition S) : d.toGraph.IsOpen ↔ d.IsOpen := by
  rw [Graph.EarDecomposition.isOpen_iff, isOpen_iff, start_isCycle_toGraph]
  refine and_congr_right fun _ ↦ ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩
  · have hi := h (Fin.cast d.length_toGraph.symm i)
    rw [kindAt_toGraph] at hi; simpa using hi
  · rw [kindAt_toGraph, EarKind.toGraph_eq_open_iff]; exact h _

end SimpleGraph.EarDecomposition

namespace Graph.EarDecomposition

section CopyEquiv

variable {α : Type u}

@[simp] theorem copy_rfl {β : Type*} {G K : Graph α β} (d : G.EarDecomposition K) :
    d.copy rfl = d :=
  ext _ _ (d.length_copy rfl) (d.heq_start_copy rfl)
    ((Fin.heq_fun_iff (d.length_copy rfl)).mpr fun i ↦
      (d.earAt_copy rfl i).trans (congrArg d.earAt (Fin.ext rfl)))

/-- Reindexing the final graph along an equality `K₁ = K₂` is an equivalence of multigraph ear
decompositions. -/
def copyEquiv {β : Type*} {G K₁ K₂ : Graph α β} (h : K₁ = K₂) :
    G.EarDecomposition K₁ ≃ G.EarDecomposition K₂ where
  toFun d := d.copy h
  invFun d := d.copy h.symm
  left_inv d := by subst h; dsimp only; rw [copy_rfl, copy_rfl]
  right_inv d := by subst h; dsimp only; rw [copy_rfl, copy_rfl]

@[simp] theorem copyEquiv_apply {β : Type*} {G K₁ K₂ : Graph α β} (h : K₁ = K₂)
    (d : G.EarDecomposition K₁) : copyEquiv h d = d.copy h := (rfl)

@[simp] theorem copyEquiv_symm_apply {β : Type*} {G K₁ K₂ : Graph α β} (h : K₁ = K₂)
    (d : G.EarDecomposition K₂) : (copyEquiv h).symm d = d.copy h.symm := (rfl)

end CopyEquiv

section OfSimpleGraph

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
    calc
      (d.graphAfter i.succ).toSimpleGraphSubgraph (d.graphAfter_le i.succ) =
          e.add.toSimpleGraphSubgraph e.add_le :=
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

theorem toGraph_initial_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.initial.toGraph = d.initial := by
  rw [initial_toSimpleGraph, Graph.toGraph_toSimpleGraphSubgraph, initial_eq_graphAfter]

/-- The transported decomposition retains the transported initial-stage witness. -/
@[simp]
theorem start_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.start = d.start.toSimpleGraph := (rfl)

@[simp]
theorem isVertexStart_toSimpleGraph_iff (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.IsVertexStart ↔ d.IsVertexStart := by
  rw [SimpleGraph.EarDecomposition.isVertexStart_iff_not_start_isCycle,
    isVertexStart_iff_not_start_isCycle, start_toSimpleGraph]
  exact not_congr d.start.isCycle_toSimpleGraph

/-- The transported decomposition displays the transported ear at each step, copied only across
the equality identifying its stored base with the corresponding prefix. -/
@[simp]
theorem earAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) :
    d.toSimpleGraph.earAt i =
      (d.earAt i).2.toSimpleGraph.copy
        (Graph.toSimpleGraphSubgraph_congr (d.earAt_fst i) (d.earAt i).2.base_le
          (d.graphAfter_le i.castSucc)) := (rfl)

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
  rw [SimpleGraph.EarDecomposition.isOpen_iff, Graph.EarDecomposition.isOpen_iff,
    start_toSimpleGraph]
  refine and_congr d.start.isCycle_toSimpleGraph ?_
  simpa only [length_toSimpleGraph] using
    (forall_congr' fun i : Fin d.length ↦ by simp)

end OfSimpleGraph

end Graph.EarDecomposition

namespace SimpleGraph

variable {α : Type u}

private theorem sigma_ear_eq {β : Type*} {G : Graph α β} {p q : Σ K, G.Ear K}
    (h1 : p.1 = q.1) (hw : p.2.toWalk = q.2.toWalk) : p = q := by
  rcases p with ⟨K, e₁⟩
  rcases q with ⟨_, e₂⟩
  dsimp only at h1 hw
  subst h1
  exact congrArg (Sigma.mk K) (Graph.Ear.ext e₁ e₂ hw)

/-- `toGraph` commutes with `copy`. -/
theorem EarDecomposition.toGraph_copy {H : SimpleGraph α} {S S' : H.Subgraph}
    (d : H.EarDecomposition S) (h : S = S') :
    (d.copy h).toGraph = d.toGraph.copy (congrArg Subgraph.toGraph h) := by
  subst h
  exact (Graph.EarDecomposition.copy_rfl _).symm

/-- Converting a simple-graph ear decomposition to `Graph.ofSimpleGraph H` and back recovers the
original ear decomposition. -/
@[simp] theorem EarDecomposition.toSimpleGraph_toGraph {H : SimpleGraph α} {S : H.Subgraph}
    (d : H.EarDecomposition S) :
    d.toGraph.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph d.toGraph.final_le) = d := by
  have hlen : (d.toGraph.toSimpleGraph.copy
      (S.toSimpleGraphSubgraph_toGraph d.toGraph.final_le)).length = d.length := by simp
  refine EarDecomposition.ext hlen ?_ ?_ fun i ↦ ?_
  · apply Subgraph.toGraph_injective
    rw [EarDecomposition.initial_copy, Graph.EarDecomposition.toGraph_initial_toSimpleGraph,
      EarDecomposition.initial_toGraph]
  · rw [EarDecomposition.start_copy, Graph.EarDecomposition.start_toSimpleGraph]
    exact (earStart_toSimpleGraph_heq_of_heq (d.graphAfter_toGraph 0) d.heq_start_toGraph).trans
      (toSimpleGraph_toGraph_earStart_heq d.start)
  · let i₀ : Fin d.toGraph.length := i
    rw [d.toGraph.toSimpleGraph.walkAt_copy _ i₀,
      Graph.EarDecomposition.walkAt_toSimpleGraph d.toGraph i₀, EarDecomposition.walkAt_toGraph,
      show Fin.cast (EarDecomposition.length_toGraph d) i₀ = Fin.cast hlen i from Fin.ext rfl]
    rcases d.walkAt (Fin.cast hlen i) with ⟨_, _, _⟩; simp

/-- Converting a multigraph ear decomposition in `Graph.ofSimpleGraph H` to `SimpleGraph` and back
recovers the original ear decomposition. -/
@[simp]
theorem _root_.Graph.EarDecomposition.toGraph_toSimpleGraph {H : SimpleGraph α} {S : H.Subgraph}
    (d : (Graph.ofSimpleGraph H).EarDecomposition S.toGraph) :
    (d.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph d.final_le)).toGraph = d := by
  rw [EarDecomposition.toGraph_copy]
  have hlen : (d.toSimpleGraph.toGraph.copy
      (congrArg Subgraph.toGraph (S.toSimpleGraphSubgraph_toGraph d.final_le))).length =
      d.length := by simp
  refine Graph.EarDecomposition.ext _ _ hlen ?_
    ((Fin.heq_fun_iff hlen).mpr fun i ↦ ?_)
  · exact (Graph.EarDecomposition.heq_start_copy _ _).trans
      ((EarDecomposition.heq_start_toGraph _).trans
        ((earStart_toGraph_heq_of_heq rfl (heq_of_eq d.start_toSimpleGraph)).trans
          (toGraph_toSimpleGraph_earStart_heq d.start)))
  · rw [Graph.EarDecomposition.earAt_copy, EarDecomposition.earAt_toGraph]
    let m : Fin d.length := ⟨i.1, hlen ▸ i.2⟩
    refine sigma_ear_eq ?_ ?_
    · change ((d.graphAfter m.castSucc).toSimpleGraphSubgraph
          (d.graphAfter_le m.castSucc)).toGraph = (d.earAt m).1
      rw [Graph.toGraph_toSimpleGraphSubgraph, d.earAt_fst]
    · change (((d.earAt m).2.toSimpleGraph.copy
          (Graph.toSimpleGraphSubgraph_congr (d.earAt_fst m) (d.earAt m).2.base_le
            (d.graphAfter_le m.castSucc))).toGraph).toWalk = (d.earAt m).2.toWalk
      rw [Ear.toWalk_toGraph, Ear.toWalk_copy, Graph.Ear.toWalk_toSimpleGraph]
      rcases (d.earAt m).2.toWalk with ⟨_, _, _⟩; simp

/-- Ear decompositions of `S : H.Subgraph` in `H` correspond bijectively to multigraph ear
decompositions of `S.toGraph` in `Graph.ofSimpleGraph H`. -/
def earDecompositionEquivOfSimpleGraph (H : SimpleGraph α) (S : H.Subgraph) :
    H.EarDecomposition S ≃ (Graph.ofSimpleGraph H).EarDecomposition S.toGraph where
  toFun d := d.toGraph
  invFun d := d.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph d.final_le)
  left_inv := EarDecomposition.toSimpleGraph_toGraph
  right_inv := Graph.EarDecomposition.toGraph_toSimpleGraph

@[simp] theorem earDecompositionEquivOfSimpleGraph_apply (H : SimpleGraph α) (S : H.Subgraph)
    (d : H.EarDecomposition S) : H.earDecompositionEquivOfSimpleGraph S d = d.toGraph := (rfl)

@[simp] theorem earDecompositionEquivOfSimpleGraph_symm_apply (H : SimpleGraph α) (S : H.Subgraph)
    (d : (Graph.ofSimpleGraph H).EarDecomposition S.toGraph) :
    (H.earDecompositionEquivOfSimpleGraph S).symm d =
      d.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph d.final_le) := (rfl)

/-- Ear decompositions of `⊤ : H.Subgraph` in `H` correspond bijectively to multigraph ear
decompositions of `Graph.ofSimpleGraph H`. -/
def earDecompositionTopEquivOfSimpleGraph (H : SimpleGraph α) :
    H.EarDecomposition ⊤ ≃ (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H) :=
  (H.earDecompositionEquivOfSimpleGraph ⊤).trans
    (Graph.EarDecomposition.copyEquiv Subgraph.toGraph_top)

@[simp] theorem earDecompositionTopEquivOfSimpleGraph_apply (H : SimpleGraph α)
    (d : H.EarDecomposition ⊤) :
    H.earDecompositionTopEquivOfSimpleGraph d = d.toGraph.copy Subgraph.toGraph_top := (rfl)

@[simp] theorem earDecompositionTopEquivOfSimpleGraph_symm_apply (H : SimpleGraph α)
    (d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)) :
    H.earDecompositionTopEquivOfSimpleGraph.symm d =
      (d.copy Subgraph.toGraph_top.symm).toSimpleGraph.copy
        ((⊤ : H.Subgraph).toSimpleGraphSubgraph_toGraph _) := (rfl)

namespace EarDecomposition

private theorem ext_of_length_eq_zero {β : Type*} {G K : Graph α β} {d₁ d₂ : G.EarDecomposition K}
    (h₁ : d₁.length = 0) (h₂ : d₂.length = 0) (hs : HEq d₁.start d₂.start) : d₁ = d₂ :=
  Graph.EarDecomposition.ext _ _ (h₁.trans h₂.symm) hs
    ((Fin.heq_fun_iff (h₁.trans h₂.symm)).mpr fun i ↦ (Fin.cast h₁ i).elim0)

variable {H : SimpleGraph α} {S : H.Subgraph}

/-- Converting `EarDecomposition.vertex` to `Graph.ofSimpleGraph H` yields
`Graph.EarDecomposition.vertex`, reindexed along `toGraph_singletonSubgraph`. -/
theorem toGraph_vertex (v : α) :
    (vertex H v).toGraph =
      (Graph.EarDecomposition.vertex (G := Graph.ofSimpleGraph H) ⟨v, mem_univ v⟩).copy
        (Subgraph.toGraph_singletonSubgraph (G := H) v).symm := by
  refine ext_of_length_eq_zero (by simp) (by simp) ?_
  refine (heq_start_toGraph _).trans ?_
  rw [start_vertex]
  exact (earStart_toGraph_heq_of_heq (subgraphAfter_vertex v 0) (eqRec_heq _ _)).trans
    ((EarStart.heq_toGraph_vertex v).trans
      ((Graph.EarDecomposition.heq_start_vertex _).symm.trans
        (Graph.EarDecomposition.heq_start_copy _ _).symm))

/-- Converting `EarDecomposition.cycle` to `Graph.ofSimpleGraph H` yields
`Graph.EarDecomposition.cycle`, reindexed along `Walk.toGraph_toSubgraph`. -/
theorem toGraph_cycle {u : α} (c : H.Walk u u) (hc : c.IsCycle) :
    (cycle c hc).toGraph =
      (Graph.EarDecomposition.cycle c.toGraph
        ((SimpleGraph.Walk.isCycle_toGraph_iff c).mpr hc)).copy
        c.toGraph_toSubgraph.symm := by
  refine ext_of_length_eq_zero (by simp) (by simp) ?_
  refine (heq_start_toGraph _).trans ?_
  rw [start_cycle]
  exact (earStart_toGraph_heq_of_heq (subgraphAfter_cycle c hc 0) (eqRec_heq _ _)).trans
    ((EarStart.heq_toGraph_cycle c hc).trans
      ((Graph.EarDecomposition.heq_start_cycle _ _).symm.trans
        (Graph.EarDecomposition.heq_start_copy _ _).symm))

private theorem toGraph_snoc_earAt_last (d : H.EarDecomposition S) (e : H.Ear S)
    {i : Fin (d.snoc e).toGraph.length} (hi : i.1 = d.length) :
    (d.snoc e).toGraph.earAt i = ⟨S.toGraph, e.toGraph⟩ := by
  have hcast : Fin.cast (length_toGraph (d.snoc e)) i = Fin.last d.length := Fin.ext hi
  refine sigma_ear_eq ?_ ?_
  · rw [earAt_toGraph]; dsimp only
    rw [show (Fin.cast (length_toGraph (d.snoc e)) i).castSucc = (Fin.last d.length).castSucc from
      Fin.ext hi, subgraphAfter_snoc_castSucc, d.subgraphAfter_last]
  · rw [← Graph.EarDecomposition.walkAt_eq, walkAt_toGraph, hcast, walkAt_snoc_last,
      Ear.toWalk_toGraph]

private theorem toGraph_snoc_earAt_lt (d : H.EarDecomposition S) (e : H.Ear S)
    {i : Fin (d.snoc e).toGraph.length} (j : Fin d.length) (hij : i.1 = j.1) :
    (d.snoc e).toGraph.earAt i =
      ⟨(d.subgraphAfter j.castSucc).toGraph, (d.earAt j).toGraph⟩ := by
  have hcast : Fin.cast (length_toGraph (d.snoc e)) i = j.castSucc := Fin.ext hij
  refine sigma_ear_eq ?_ ?_
  · rw [earAt_toGraph]; dsimp only
    rw [show (Fin.cast (length_toGraph (d.snoc e)) i).castSucc = j.castSucc.castSucc from
      Fin.ext hij, subgraphAfter_snoc_castSucc]
  · rw [← Graph.EarDecomposition.walkAt_eq, walkAt_toGraph, hcast, walkAt_snoc_castSucc,
      walkAt_def, Ear.toWalk_toGraph]

/-- `toGraph` commutes with `snoc`. -/
theorem toGraph_snoc (d : H.EarDecomposition S) (e : H.Ear S) :
    (d.snoc e).toGraph = (d.toGraph.snoc e.toGraph).copy e.add_toGraph := by
  have hlen : (d.snoc e).toGraph.length =
      ((d.toGraph.snoc e.toGraph).copy e.add_toGraph).length := by simp
  refine Graph.EarDecomposition.ext _ _ hlen ?_
    ((Fin.heq_fun_iff hlen).mpr fun i ↦ ?_)
  · refine (heq_start_toGraph _).trans ?_
    rw [start_snoc]
    exact (earStart_toGraph_heq_of_heq (by simp) (eqRec_heq _ _)).trans
      ((heq_start_toGraph d).symm.trans
        ((d.toGraph.heq_start_snoc e.toGraph).symm.trans
          (Graph.EarDecomposition.heq_start_copy _ _).symm))
  · suffices ∀ m : Fin _, m.1 = i.1 →
        (d.snoc e).toGraph.earAt i = ((d.toGraph.snoc e.toGraph).copy e.add_toGraph).earAt m from
      this _ rfl
    intro m hm
    by_cases hi : i.1 = d.length
    · rw [toGraph_snoc_earAt_last d e hi, Graph.EarDecomposition.earAt_copy,
        show Fin.cast (Graph.EarDecomposition.length_copy _ _) m =
          Fin.cast (d.toGraph.length_snoc e.toGraph).symm (Fin.last d.toGraph.length) from
          Fin.ext (by simp [hm, hi]),
        Graph.EarDecomposition.earAt_snoc_last]
    · let j : Fin d.length := ⟨i.1, by have := i.2; simp at this; omega⟩
      let j' : Fin d.toGraph.length := Fin.cast d.length_toGraph.symm j
      rw [toGraph_snoc_earAt_lt d e j rfl, Graph.EarDecomposition.earAt_copy,
        show Fin.cast (Graph.EarDecomposition.length_copy _ _) m =
          Fin.cast (d.toGraph.length_snoc e.toGraph).symm j'.castSucc from Fin.ext hm,
        Graph.EarDecomposition.earAt_snoc_castSucc, earAt_toGraph,
        show Fin.cast (length_toGraph d) j' = j from Fin.ext rfl]

private theorem toGraph_prefix_earAt (d : H.EarDecomposition S) (k : Fin (d.length + 1))
    (j : Fin (d.prefix k).toGraph.length)
    (m : Fin ((d.toGraph.prefix (Fin.cast (congrArg (· + 1) d.length_toGraph.symm) k)).copy
      (d.graphAfter_toGraph _)).length) (hm : m.1 = j.1) :
    (d.prefix k).toGraph.earAt j =
      ((d.toGraph.prefix (Fin.cast (congrArg (· + 1) d.length_toGraph.symm) k)).copy
        (d.graphAfter_toGraph _)).earAt m := by
  let k' : Fin (d.toGraph.length + 1) := Fin.cast (congrArg (· + 1) d.length_toGraph.symm) k
  let j₀ : Fin k'.val := ⟨j.1, by have := j.2; simp [k'] at this ⊢; omega⟩
  let j₁ : Fin k := ⟨j.1, by have := j.2; simp at this; omega⟩
  rw [earAt_toGraph, Graph.EarDecomposition.earAt_copy,
    show Fin.cast (Graph.EarDecomposition.length_copy _ _) m =
      Fin.cast (d.toGraph.length_prefix k').symm j₀ from Fin.ext hm,
    Graph.EarDecomposition.earAt_prefix, earAt_toGraph]
  have hj1 : ((d.prefix k).subgraphAfter
      (Fin.cast (length_toGraph (d.prefix k)) j).castSucc).toGraph =
      (d.subgraphAfter (j₁.castLE k.is_le).castSucc).toGraph := by
    rw [show (Fin.cast (length_toGraph (d.prefix k)) j).castSucc = j₁.castSucc from Fin.ext rfl,
      subgraphAfter_prefix]
    exact congrArg (fun x ↦ (d.subgraphAfter x).toGraph) (Fin.ext rfl)
  have hj2 : Fin.cast (length_toGraph d)
      (Fin.castLE (Nat.le_of_lt_succ k'.isLt) j₀) = j₁.castLE k.is_le := Fin.ext rfl
  refine sigma_ear_eq hj1 ?_
  dsimp only
  rw [hj2, Ear.toWalk_toGraph, Ear.toWalk_toGraph, ← (d.prefix k).walkAt_def, ← d.walkAt_def,
    show Fin.cast (length_toGraph (d.prefix k)) j = j₁ from Fin.ext rfl, walkAt_prefix]

/-- `toGraph` commutes with `prefix`. -/
theorem toGraph_prefix (d : H.EarDecomposition S) (k : Fin (d.length + 1)) :
    (d.prefix k).toGraph =
      (d.toGraph.prefix (Fin.cast (congrArg (· + 1) d.length_toGraph.symm) k)).copy
        (d.graphAfter_toGraph _) := by
  let k' : Fin (d.toGraph.length + 1) := Fin.cast (congrArg (· + 1) d.length_toGraph.symm) k
  have hlen : (d.prefix k).toGraph.length =
      ((d.toGraph.prefix k').copy (d.graphAfter_toGraph k')).length := by simp [k']
  refine Graph.EarDecomposition.ext _ _ hlen ?_
    ((Fin.heq_fun_iff hlen).mpr fun j ↦ toGraph_prefix_earAt d k j _ rfl)
  exact (heq_start_toGraph _).trans
    ((heq_start_toGraph d).symm.trans
      ((d.toGraph.heq_start_prefix k').symm.trans
        (Graph.EarDecomposition.heq_start_copy _ _).symm))

/-! ### Initial-stage replacement and vertex-start normalization via transport -/

/-- Replay the displayed ears of `d : H.EarDecomposition S` on top of an ear decomposition
`d₀ : H.EarDecomposition d.initial` of its initial subgraph. -/
def replaceInitial (d : H.EarDecomposition S) (d₀ : H.EarDecomposition d.initial) :
    H.EarDecomposition S :=
  (H.earDecompositionEquivOfSimpleGraph S).symm
    (d.toGraph.replaceInitial (d₀.toGraph.copy d.initial_toGraph.symm))

@[simp] theorem toGraph_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).toGraph =
      d.toGraph.replaceInitial (d₀.toGraph.copy d.initial_toGraph.symm) :=
  (H.earDecompositionEquivOfSimpleGraph S).apply_symm_apply _

@[simp] theorem length_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).length = d₀.length + d.length := by
  rw [← length_toGraph, toGraph_replaceInitial, Graph.EarDecomposition.length_replaceInitial,
    Graph.EarDecomposition.length_copy, length_toGraph, length_toGraph]

@[simp] theorem initial_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) : (d.replaceInitial d₀).initial = d₀.initial := by
  apply Subgraph.toGraph_injective
  rw [← initial_toGraph, toGraph_replaceInitial, Graph.EarDecomposition.initial_replaceInitial,
    Graph.EarDecomposition.initial_copy, initial_toGraph]

@[simp] theorem start_isCycle_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).start.IsCycle ↔ d₀.start.IsCycle := by
  rw [← start_isCycle_toGraph, toGraph_replaceInitial,
    Graph.EarDecomposition.start_isCycle_replaceInitial,
    Graph.EarDecomposition.start_isCycle_copy, start_isCycle_toGraph]

@[simp] theorem isVertexStart_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).IsVertexStart ↔ d₀.IsVertexStart := by
  simp only [isVertexStart_iff, initial_replaceInitial]

@[simp] theorem isOpen_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).IsOpen ↔ d₀.IsOpen ∧ ∀ i, d.kindAt i = .«open» := by
  rw [← isOpen_toGraph_iff, toGraph_replaceInitial, Graph.EarDecomposition.isOpen_replaceInitial,
    Graph.EarDecomposition.isOpen_copy, isOpen_toGraph_iff]
  refine and_congr_right fun _ ↦ ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩
  · have hi := h (Fin.cast d.length_toGraph.symm i)
    rw [kindAt_toGraph] at hi; simpa using hi
  · rw [kindAt_toGraph, EarKind.toGraph_eq_open_iff]; exact h _

/-- Normalize any ear decomposition `d : H.EarDecomposition S` to start at a single vertex, turning
an initial cycle into a single-vertex start followed by one closed ear. -/
def toVertexStart (d : H.EarDecomposition S) : H.EarDecomposition S :=
  (H.earDecompositionEquivOfSimpleGraph S).symm d.toGraph.toVertexStart

@[simp] theorem toGraph_toVertexStart (d : H.EarDecomposition S) :
    d.toVertexStart.toGraph = d.toGraph.toVertexStart :=
  (H.earDecompositionEquivOfSimpleGraph S).apply_symm_apply _

@[simp] theorem isVertexStart_toVertexStart (d : H.EarDecomposition S) :
    d.toVertexStart.IsVertexStart := by
  rw [← isVertexStart_toGraph_iff, toGraph_toVertexStart]
  exact d.toGraph.isVertexStart_toVertexStart

@[simp] theorem not_start_isCycle_toVertexStart (d : H.EarDecomposition S) :
    ¬ d.toVertexStart.start.IsCycle :=
  (isVertexStart_iff_not_start_isCycle _).mp d.isVertexStart_toVertexStart

/-- Normalizing to a vertex start adds one closed ear when `d` starts at a cycle and leaves the
length unchanged otherwise. -/
theorem length_toVertexStart (d : H.EarDecomposition S) :
    d.toVertexStart.length = (if d.start.IsCycle then 1 else 0) + d.length := by
  have h := d.toGraph.length_toVertexStart
  rw [← length_toGraph, toGraph_toVertexStart]
  simpa only [start_isCycle_toGraph, length_toGraph] using h

/-- Normalizing an already vertex-started ear decomposition returns it unchanged. -/
theorem toVertexStart_eq_self {d : H.EarDecomposition S} (h : d.IsVertexStart) :
    d.toVertexStart = d := by
  apply (H.earDecompositionEquivOfSimpleGraph S).injective
  rw [earDecompositionEquivOfSimpleGraph_apply, toGraph_toVertexStart,
    earDecompositionEquivOfSimpleGraph_apply]
  exact Graph.EarDecomposition.toVertexStart_eq_self (d.isVertexStart_toGraph_iff.mpr h)

end EarDecomposition

/-- A subgraph of `H` admits an ear decomposition if and only if it admits one starting from a
single vertex. No finiteness assumption is needed. -/
theorem nonempty_earDecomposition_iff_exists_isVertexStart {H : SimpleGraph α} {S : H.Subgraph} :
    Nonempty (H.EarDecomposition S) ↔ ∃ d : H.EarDecomposition S, d.IsVertexStart :=
  ⟨fun ⟨d⟩ ↦ ⟨d.toVertexStart, d.isVertexStart_toVertexStart⟩, fun ⟨d, _⟩ ↦ ⟨d⟩⟩

/-! ### Data-level extension and `[Finite H.edgeSet]` ear characterizations -/

namespace EarDecomposition

private theorem graphAfter_eq_of_eq {β : Type*} {G K : Graph α β}
    {d₁ d₂ : G.EarDecomposition K} (h : d₁ = d₂) (m : ℕ)
    (hm₁ : m < d₁.length + 1) (hm₂ : m < d₂.length + 1) :
    d₁.graphAfter ⟨m, hm₁⟩ = d₂.graphAfter ⟨m, hm₂⟩ := by subst h; rfl

private theorem earAt_eq_of_eq {β : Type*} {G K : Graph α β}
    {d₁ d₂ : G.EarDecomposition K} (h : d₁ = d₂) (m : ℕ)
    (hm₁ : m < d₁.length) (hm₂ : m < d₂.length) :
    d₁.earAt ⟨m, hm₁⟩ = d₂.earAt ⟨m, hm₂⟩ := by subst h; rfl

private theorem heq_start_of_eq {β : Type*} {G K : Graph α β}
    {d₁ d₂ : G.EarDecomposition K} (h : d₁ = d₂) : HEq d₁.start d₂.start := by subst h; rfl

variable {H : SimpleGraph α} {S : H.Subgraph}

/-- Complete any partial ear decomposition `d : H.EarDecomposition S` in a `2`-edge-connected simple
graph with finitely many edges to an ear decomposition of `⊤ : H.Subgraph`. Unlike well-founded
induction on `H.Subgraph`, this requires only `[Finite H.edgeSet]` rather than `[Finite α]`. -/
noncomputable def extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2)
    (d : H.EarDecomposition S) : H.EarDecomposition ⊤ :=
  H.earDecompositionTopEquivOfSimpleGraph.symm
    (d.toGraph.extend ((Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH))

theorem toGraph_extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2)
    (d : H.EarDecomposition S) :
    (d.extend hH).toGraph.copy Subgraph.toGraph_top =
      d.toGraph.extend ((Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH) :=
  H.earDecompositionTopEquivOfSimpleGraph.apply_symm_apply _

theorem length_le_length_extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2)
    (d : H.EarDecomposition S) : d.length ≤ (d.extend hH).length := by
  have h := d.toGraph.length_le_length_extend ((Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH)
  rwa [← d.toGraph_extend hH, Graph.EarDecomposition.length_copy, length_toGraph,
    length_toGraph] at h

@[simp] theorem subgraphAfter_extend_castLE [Finite H.edgeSet] (hH : H.IsEdgeConnected 2)
    (d : H.EarDecomposition S) (k : Fin (d.length + 1)) :
    (d.extend hH).subgraphAfter
      (Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hH)) k) = d.subgraphAfter k := by
  apply Subgraph.toGraph_injective
  let hH' := (Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH
  have hm₁ : k.1 < ((d.extend hH).toGraph.copy Subgraph.toGraph_top).length + 1 := by
    simpa using (Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hH)) k).2
  have hm₂ : k.1 < (d.toGraph.extend hH').length + 1 :=
    (Fin.castLE (Nat.succ_le_succ (d.toGraph.length_le_length_extend hH'))
      (Fin.cast (congrArg (· + 1) d.length_toGraph.symm) k)).2
  have heq := graphAfter_eq_of_eq (d.toGraph_extend hH) k.1 hm₁ hm₂
  rw [Graph.EarDecomposition.graphAfter_copy, graphAfter_toGraph] at heq
  have hspec := d.toGraph.graphAfter_extend_castLE hH'
    (Fin.cast (congrArg (· + 1) d.length_toGraph.symm) k)
  rw [graphAfter_toGraph] at hspec
  exact (congrArg (fun x ↦ ((d.extend hH).subgraphAfter x).toGraph) (Fin.ext rfl)).trans
    ((heq.trans hspec).trans (congrArg (fun x ↦ (d.subgraphAfter x).toGraph) (Fin.ext rfl)))

@[simp] theorem initial_extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2)
    (d : H.EarDecomposition S) : (d.extend hH).initial = d.initial := by
  simpa only [← subgraphAfter_zero, Fin.castLE_zero] using d.subgraphAfter_extend_castLE hH 0

@[simp] theorem start_isCycle_extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2)
    (d : H.EarDecomposition S) : (d.extend hH).start.IsCycle ↔ d.start.IsCycle := by
  have h := d.toGraph.start_isCycle_extend ((Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH)
  rwa [← d.toGraph_extend hH, Graph.EarDecomposition.start_isCycle_copy,
    start_isCycle_toGraph, start_isCycle_toGraph] at h

@[simp] theorem isVertexStart_extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2)
    (d : H.EarDecomposition S) : (d.extend hH).IsVertexStart ↔ d.IsVertexStart := by
  simp only [isVertexStart_iff, initial_extend]

private theorem earAt_toGraph_extend_eq [Finite H.edgeSet] (hH : H.IsEdgeConnected 2)
    (d : H.EarDecomposition S) (i : Fin d.length) :
    (⟨((d.extend hH).subgraphAfter (Fin.castLE (d.length_le_length_extend hH) i).castSucc).toGraph,
      ((d.extend hH).earAt (Fin.castLE (d.length_le_length_extend hH) i)).toGraph⟩ :
        Σ K, (Graph.ofSimpleGraph H).Ear K) =
      ⟨(d.subgraphAfter i.castSucc).toGraph, (d.earAt i).toGraph⟩ := by
  let hH' := (Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH
  have hm₁ : i.1 < ((d.extend hH).toGraph.copy Subgraph.toGraph_top).length := by
    simpa using (Fin.castLE (d.length_le_length_extend hH) i).2
  have hm₂ : i.1 < (d.toGraph.extend hH').length :=
    (Fin.castLE (d.toGraph.length_le_length_extend hH') (Fin.cast d.length_toGraph.symm i)).2
  have h := (earAt_eq_of_eq (d.toGraph_extend hH) i.1 hm₁ hm₂).trans
    (d.toGraph.earAt_extend_castLE hH' (Fin.cast d.length_toGraph.symm i))
  rw [Graph.EarDecomposition.earAt_copy, earAt_toGraph, earAt_toGraph,
    show Fin.cast (length_toGraph (d.extend hH))
      (Fin.cast (Graph.EarDecomposition.length_copy _ _) ⟨i.1, hm₁⟩) =
      Fin.castLE (d.length_le_length_extend hH) i from Fin.ext rfl,
    show Fin.cast (length_toGraph d) (Fin.cast d.length_toGraph.symm i) = i from Fin.ext rfl] at h
  exact h

@[simp] theorem walkAt_extend_castLE [Finite H.edgeSet] (hH : H.IsEdgeConnected 2)
    (d : H.EarDecomposition S) (i : Fin d.length) :
    (d.extend hH).walkAt (Fin.castLE (d.length_le_length_extend hH) i) = d.walkAt i := by
  have h := congrArg (fun p : Σ K, (Graph.ofSimpleGraph H).Ear K ↦ p.2.toWalk)
    (d.earAt_toGraph_extend_eq hH i)
  dsimp only at h
  rw [Ear.toWalk_toGraph, Ear.toWalk_toGraph, ← walkAt_def, ← walkAt_def] at h
  rcases hw1 : (d.extend hH).walkAt (Fin.castLE (d.length_le_length_extend hH) i) with ⟨u₁, v₁, p₁⟩
  rcases hw2 : d.walkAt i with ⟨u₂, v₂, p₂⟩
  rw [hw1, hw2] at h
  injection h with hu h'; subst hu
  injection h' with hv hp; subst hv
  exact congrArg (fun q ↦ (⟨u₁, v₁, q⟩ : Σ u v : α, H.Walk u v))
    (by simpa using congrArg Graph.Walk.toSimpleGraph (eq_of_heq hp))

@[simp] theorem kindAt_extend_castLE [Finite H.edgeSet] (hH : H.IsEdgeConnected 2)
    (d : H.EarDecomposition S) (i : Fin d.length) :
    (d.extend hH).kindAt (Fin.castLE (d.length_le_length_extend hH) i) = d.kindAt i := by
  have h := congrArg (fun p : Σ K, (Graph.ofSimpleGraph H).Ear K ↦ p.2.kind)
    (d.earAt_toGraph_extend_eq hH i)
  dsimp only at h
  rw [Ear.kind_toGraph, Ear.kind_toGraph, ← kindAt_def, ← kindAt_def] at h
  exact earKindEquivGraph.injective h

/-- Taking the prefix of `d.extend hH` of length `d.length` recovers `d`. -/
theorem prefix_extend [Finite H.edgeSet] (hH : H.IsEdgeConnected 2)
    (d : H.EarDecomposition S) :
    ((d.extend hH).prefix
      (Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hH)) (Fin.last d.length))).copy
      ((d.subgraphAfter_extend_castLE hH (Fin.last d.length)).trans d.subgraphAfter_last) = d := by
  let k : Fin ((d.extend hH).length + 1) :=
    Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hH)) (Fin.last d.length)
  let hsub := (d.subgraphAfter_extend_castLE hH (Fin.last d.length)).trans d.subgraphAfter_last
  have hlen : (((d.extend hH).prefix k).copy hsub).length = d.length := by simp [k]
  refine ext hlen (by simp) ?_ fun j ↦ ?_
  · rw [start_copy, start_prefix]
    let hH' := (Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH
    have hstart_graph : HEq (d.extend hH).start.toGraph d.start.toGraph :=
      ((d.extend hH).heq_start_toGraph).symm.trans
        ((((d.extend hH).toGraph.heq_start_copy Subgraph.toGraph_top).symm.trans
          (heq_start_of_eq (d.toGraph_extend hH))).trans
          ((d.toGraph.heq_start_extend hH').trans d.heq_start_toGraph))
    have h0 : (d.extend hH).subgraphAfter 0 = d.subgraphAfter 0 :=
      (d.extend hH).subgraphAfter_zero.trans ((d.initial_extend hH).trans d.subgraphAfter_zero.symm)
    exact (toSimpleGraph_toGraph_earStart_heq (d.extend hH).start).symm.trans
      ((earStart_toSimpleGraph_heq_of_heq (congrArg Subgraph.toGraph h0) hstart_graph).trans
        (toSimpleGraph_toGraph_earStart_heq d.start))
  · let j₀ : Fin k := j
    rw [(((d.extend hH).prefix k).walkAt_copy hsub j₀).trans ((d.extend hH).walkAt_prefix k j₀),
      show j₀.castLE k.is_le = Fin.castLE (d.length_le_length_extend hH) (Fin.cast hlen j) from
        Fin.ext rfl,
      walkAt_extend_castLE]

end EarDecomposition

/-- Construct an ear decomposition of `⊤` in a `2`-edge-connected simple graph with finitely many
edges starting at a prescribed vertex `v`. -/
noncomputable def IsEdgeConnected.earDecompositionOfVertex {H : SimpleGraph α} [Finite H.edgeSet]
    (hH : H.IsEdgeConnected 2) (v : α) : H.EarDecomposition ⊤ :=
  (EarDecomposition.vertex H v).extend hH

@[simp] theorem IsEdgeConnected.initial_earDecompositionOfVertex {H : SimpleGraph α}
    [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) (v : α) :
    (hH.earDecompositionOfVertex v).initial = H.singletonSubgraph v := by
  rw [earDecompositionOfVertex, EarDecomposition.initial_extend, EarDecomposition.initial_vertex]

@[simp] theorem IsEdgeConnected.isVertexStart_earDecompositionOfVertex {H : SimpleGraph α}
    [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) (v : α) :
    (hH.earDecompositionOfVertex v).IsVertexStart := by
  rw [earDecompositionOfVertex, EarDecomposition.isVertexStart_extend]
  exact EarDecomposition.isVertexStart_vertex v

/-- Construct an ear decomposition of `⊤` in a `2`-edge-connected simple graph with finitely many
edges starting at a prescribed cycle `c`. -/
noncomputable def IsEdgeConnected.earDecompositionOfCycle {H : SimpleGraph α} [Finite H.edgeSet]
    (hH : H.IsEdgeConnected 2) {u : α} (c : H.Walk u u) (hc : c.IsCycle) :
    H.EarDecomposition ⊤ :=
  (EarDecomposition.cycle c hc).extend hH

@[simp] theorem IsEdgeConnected.initial_earDecompositionOfCycle {H : SimpleGraph α}
    [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) {u : α} (c : H.Walk u u) (hc : c.IsCycle) :
    (hH.earDecompositionOfCycle c hc).initial = c.toSubgraph := by
  rw [earDecompositionOfCycle, EarDecomposition.initial_extend, EarDecomposition.initial_cycle]

@[simp] theorem IsEdgeConnected.start_isCycle_earDecompositionOfCycle {H : SimpleGraph α}
    [Finite H.edgeSet] (hH : H.IsEdgeConnected 2) {u : α} (c : H.Walk u u) (hc : c.IsCycle) :
    (hH.earDecompositionOfCycle c hc).start.IsCycle := by
  rw [earDecompositionOfCycle, EarDecomposition.start_isCycle_extend]
  exact (EarDecomposition.isOpen_cycle c hc).start_isCycle

/-- A simple graph with finitely many edges is connected and has no bridge among its actual edges if
and only if `⊤ : H.Subgraph` admits an ear decomposition. No separate `[Nonempty α]` or `[Finite α]`
assumption is needed, since both sides imply `Nonempty α`. -/
theorem connected_and_forall_not_isBridge_iff_nonempty_earDecomposition {H : SimpleGraph α}
    [Finite H.edgeSet] :
    (H.Connected ∧ ∀ e ∈ H.edgeSet, ¬ H.IsBridge e) ↔ Nonempty (H.EarDecomposition ⊤) := by
  rw [← H.earDecompositionTopEquivOfSimpleGraph.nonempty_congr.symm,
    ← Graph.connected_and_forall_not_isBridge_iff_nonempty_earDecomposition,
    Graph.connected_ofSimpleGraph_iff]
  refine and_congr_right fun _ ↦
    ⟨fun h e he ↦ ?_, fun h e he hb ↦ h e (Graph.isBridge_ofSimpleGraph_iff.mpr ⟨he, hb⟩)⟩
  obtain ⟨heH, hb⟩ := Graph.isBridge_ofSimpleGraph_iff.mp he
  exact h e heH hb

/-- **Whitney's open ear characterization on `Graph.ofSimpleGraph H`.** A simple graph with finitely
many edges is `2`-vertex-connected if and only if `Graph.ofSimpleGraph H` admits an open ear
decomposition. Neither `[Finite α]` nor `[Nonempty α]` is required. -/
theorem isVertexConnected_two_iff_exists_isOpen_earDecomposition_ofSimpleGraph
    (H : SimpleGraph α) [Finite H.edgeSet] :
    H.IsVertexConnected 2 ↔
      ∃ d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H), d.IsOpen := by
  refine ⟨fun hH ↦ ?_, fun ⟨d, hd⟩ ↦ ?_⟩
  · have : Finite α := (hH.preconnected (by simp)).finite_of_finite_edgeSet
    obtain ⟨d, hd⟩ := (isVertexConnected_two_iff_exists_isOpen_earDecomposition (G := H)).mp hH
    refine ⟨H.earDecompositionTopEquivOfSimpleGraph d, ?_⟩
    rwa [earDecompositionTopEquivOfSimpleGraph_apply, Graph.EarDecomposition.isOpen_copy,
      EarDecomposition.isOpen_toGraph_iff]
  · have hd' : (H.earDecompositionTopEquivOfSimpleGraph.symm d).IsOpen := by
      rwa [earDecompositionTopEquivOfSimpleGraph_symm_apply, EarDecomposition.isOpen_copy,
        Graph.EarDecomposition.isOpen_toSimpleGraph, Graph.EarDecomposition.isOpen_copy]
    exact hd'.isVertexConnected_two

end SimpleGraph
