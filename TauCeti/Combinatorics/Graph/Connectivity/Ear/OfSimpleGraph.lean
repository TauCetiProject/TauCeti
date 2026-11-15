/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.OfSimpleGraph
public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Characterization
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
only `[Finite H.edgeSet]` without separate `[Finite α]` or `[Nonempty α]` typeclass hypotheses—
data-level completion of any partial ear decomposition (`SimpleGraph.EarDecomposition.extend`),
prescribed-vertex and prescribed-cycle ear decompositions of `2`-edge-connected simple graphs, the
bridgeless connected ear characterization
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
* `SimpleGraph.EarDecomposition.replaceInitial`, `SimpleGraph.EarDecomposition.toVertexStart`:
  initial-stage replacement and vertex-start normalization on `SimpleGraph.EarDecomposition`.
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

theorem toGraph_injective : Function.Injective toGraph := fun k l h ↦ by
  cases k <;> cases l <;> simp_all
@[simp] theorem toGraph_inj {k l : SimpleGraph.EarKind} : k.toGraph = l.toGraph ↔ k = l :=
  toGraph_injective.eq_iff

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

@[simp] theorem toSimpleGraph_eq_open_iff {k : Graph.EarKind} :
    k.toSimpleGraph = .open ↔ k = .open := by cases k <;> simp
@[simp] theorem toSimpleGraph_eq_closed_iff {k : Graph.EarKind} :
    k.toSimpleGraph = .closed ↔ k = .closed := by cases k <;> simp

theorem toSimpleGraph_injective : Function.Injective toSimpleGraph := fun k l h ↦ by
  cases k <;> cases l <;> simp_all
@[simp] theorem toSimpleGraph_inj {k l : Graph.EarKind} :
    k.toSimpleGraph = l.toSimpleGraph ↔ k = l := toSimpleGraph_injective.eq_iff

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
    (fun w hw hws ↦ by rw [K.verts_toSimpleGraphSubgraph hK]; exact hint w (by simpa using hw) hws)
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
    (Ear.closedOfSimpleGraph hK walk isCycle base_mem internal_new).kind = .closed :=
  Ear.kind_closed ..

@[simp] theorem Ear.toWalk_closedOfSimpleGraph (hK : K ≤ Graph.ofSimpleGraph H) {s : α}
    (walk : (Graph.ofSimpleGraph H).Walk s s) (isCycle : walk.IsCycle) (base_mem : s ∈ V(K))
    (internal_new : ∀ x ∈ walk.support, x ≠ s → x ∉ V(K)) :
    (Ear.closedOfSimpleGraph hK walk isCycle base_mem internal_new).toWalk = ⟨s, s, walk⟩ :=
  Ear.toWalk_closed ..

@[simp] theorem Ear.toGraph_closedOfSimpleGraph (hK : K ≤ Graph.ofSimpleGraph H) {s : α}
    (walk : (Graph.ofSimpleGraph H).Walk s s) (isCycle : walk.IsCycle) (base_mem : s ∈ V(K))
    (internal_new : ∀ x ∈ walk.support, x ≠ s → x ∉ V(K)) :
    (Ear.closedOfSimpleGraph hK walk isCycle base_mem internal_new).toGraph =
      (Graph.ofSimpleGraph H).walkGraph walk :=
  Ear.toGraph_closed ..

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

@[simp] theorem toGraph_open {u v : α} (p : H.Walk u v) (hp : p.IsPath)
    (hu : u ∈ S.verts) (hv : v ∈ S.verts) (huv : u ≠ v)
    (hint : ∀ w ∈ p.support, w ≠ u → w ≠ v → w ∉ S.verts) (hedge : ∀ e ∈ p.edges, e ∉ S.edgeSet) :
    (Ear.«open» p hp hu hv huv hint hedge).toGraph =
      .open S.toGraph_le_ofSimpleGraph p.toGraph ((SimpleGraph.Walk.isPath_toGraph_iff p).mpr hp)
        (S.vertexSet_toGraph.symm ▸ hu) (S.vertexSet_toGraph.symm ▸ hv) huv
        (fun x hx hxu hxv ↦ S.vertexSet_toGraph.symm ▸
          hint x ((SimpleGraph.Walk.support_toGraph p) ▸ hx) hxu hxv)
        (fun f hf ↦ S.edgeSet_toGraph.symm ▸
          hedge f ((SimpleGraph.Walk.edges_toGraph p) ▸ hf)) := (rfl)

@[simp] theorem toGraph_closed {u : α} (c : H.Walk u u) (hc : c.IsCycle)
    (hu : u ∈ S.verts) (hint : ∀ w ∈ c.support, w ≠ u → w ∉ S.verts) :
    (Ear.closed c hc hu hint).toGraph =
      Graph.Ear.closedOfSimpleGraph S.toGraph_le_ofSimpleGraph c.toGraph
        ((SimpleGraph.Walk.isCycle_toGraph_iff c).mpr hc) (S.vertexSet_toGraph.symm ▸ hu)
        (fun x hx hxu ↦ S.vertexSet_toGraph.symm ▸
          hint x ((SimpleGraph.Walk.support_toGraph c) ▸ hx) hxu) := (rfl)

@[simp] theorem toGraph_copy {S' : H.Subgraph} (e : H.Ear S) (h : S = S') :
    (e.copy h).toGraph = congrArg Subgraph.toGraph h ▸ e.toGraph := by subst h; simp

@[simp] theorem kind_toGraph (e : H.Ear S) : e.toGraph.kind = e.kind.toGraph := by cases e <;> simp

@[simp] theorem toWalk_toGraph (e : H.Ear S) :
    e.toGraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toGraph⟩ := by
  cases e with | «open» => rw [toWalk_open]; simp | closed => rw [toWalk_closed]; simp

@[simp] theorem toGraph_toGraph (e : H.Ear S) :
    Graph.Ear.toGraph e.toGraph = e.toSubgraph.toGraph := by
  cases e <;> simp [SimpleGraph.Walk.toGraph_toSubgraph]

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
        (by simpa using ht) hst (by simpa using hinter) (by simpa using hedge)
  | .closed _ p hp hs hinter _ =>
      .closed p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp) (by simpa using hs)
        (by simpa using hinter)

@[simp] theorem toSimpleGraph_open {x y : V} (hKG : K ≤ Graph.ofSimpleGraph G)
    (p : (Graph.ofSimpleGraph G).Walk x y) (hp : p.IsPath) (hx : x ∈ K.vertexSet)
    (hy : y ∈ K.vertexSet) (hxy : x ≠ y)
    (hinter : ∀ z ∈ p.support, z ≠ x → z ≠ y → z ∉ K.vertexSet)
    (hedge : ∀ f ∈ p.edges, f ∉ K.edgeSet) :
    (Graph.Ear.open hKG p hp hx hy hxy hinter hedge).toSimpleGraph =
      SimpleGraph.Ear.open p.toSimpleGraph (p.isPath_toSimpleGraph_iff.mpr hp)
        (by simpa using hx) (by simpa using hy) hxy
        (by simpa using hinter) (by simpa using hedge) := (rfl)

@[simp] theorem toSimpleGraph_closed {x : V} (hKG : K ≤ Graph.ofSimpleGraph G)
    (p : (Graph.ofSimpleGraph G).Walk x x) (hp : p.IsCycle) (hx : x ∈ K.vertexSet)
    (hinter : ∀ z ∈ p.support, z ≠ x → z ∉ K.vertexSet) (hedge : ∀ f ∈ p.edges, f ∉ K.edgeSet) :
    (Graph.Ear.closed hKG p hp hx hinter hedge).toSimpleGraph =
      SimpleGraph.Ear.closed p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)
        (by simpa using hx) (by simpa using hinter) := (rfl)

@[simp] theorem toSimpleGraph_closedOfSimpleGraph {x : V} (hKG : K ≤ Graph.ofSimpleGraph G)
    (p : (Graph.ofSimpleGraph G).Walk x x) (hp : p.IsCycle) (hx : x ∈ K.vertexSet)
    (hinter : ∀ z ∈ p.support, z ≠ x → z ∉ K.vertexSet) :
    (Graph.Ear.closedOfSimpleGraph hKG p hp hx hinter).toSimpleGraph =
      SimpleGraph.Ear.closed p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)
        (by simpa using hx) (by simpa using hinter) := (rfl)

@[simp] theorem kind_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.kind = e.kind.toSimpleGraph := by
  cases e <;> simp [toSimpleGraph, Graph.EarKind.toSimpleGraph]

@[simp] theorem toWalk_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toSimpleGraph⟩ := by
  cases e with
  | «open» => unfold toSimpleGraph; rw [SimpleGraph.Ear.toWalk_open, Graph.Ear.toWalk_open]
  | closed => unfold toSimpleGraph; rw [SimpleGraph.Ear.toWalk_closed, Graph.Ear.toWalk_closed]

/-- Transport identifies the graph traced by an ear with the simple subgraph traced by the
transported ear. -/
@[simp] theorem toSimpleGraphSubgraph_toGraph (e : (Graph.ofSimpleGraph G).Ear K)
    (h : e.toGraph ≤ Graph.ofSimpleGraph G) :
    e.toGraph.toSimpleGraphSubgraph h = e.toSimpleGraph.toSubgraph := by cases e <;> simp

/-- Transport commutes with adjoining an ear to its base graph. -/
@[simp] theorem toSimpleGraphSubgraph_add (e : (Graph.ofSimpleGraph G).Ear K)
    (hAdd : e.add ≤ Graph.ofSimpleGraph G) :
    e.add.toSimpleGraphSubgraph hAdd = e.toSimpleGraph.adjoin := by
  ext x y
  · simp only [Graph.verts_toSimpleGraphSubgraph, Graph.Ear.vertexSet_add,
      SimpleGraph.Ear.verts_adjoin, Set.mem_union]
    rw [← Graph.verts_toSimpleGraphSubgraph e.toGraph e.toGraph_le, e.toSimpleGraphSubgraph_toGraph]
  · simp only [← SimpleGraph.Subgraph.mem_edgeSet, Graph.edgeSet_toSimpleGraphSubgraph,
      Graph.Ear.edgeSet_add, SimpleGraph.Ear.edgeSet_adjoin, Set.mem_union]
    rw [← Graph.edgeSet_toSimpleGraphSubgraph e.toGraph e.toGraph_le,
      e.toSimpleGraphSubgraph_toGraph]

/-- Converting a multigraph ear over `K ≤ Graph.ofSimpleGraph G` to `SimpleGraph` and back recovers
the original ear. -/
@[simp] theorem toGraph_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    (K.toGraph_toSimpleGraphSubgraph e.base_le) ▸ e.toSimpleGraph.toGraph = e := by
  have hsig : (⟨_, e.toSimpleGraph.toGraph⟩ : Σ L, (Graph.ofSimpleGraph G).Ear L) = ⟨K, e⟩ :=
    Graph.Ear.sigma_ext (K.toGraph_toSimpleGraphSubgraph e.base_le) <| by
      rw [SimpleGraph.Ear.toWalk_toGraph, Graph.Ear.toWalk_toSimpleGraph]
      rcases e.toWalk with ⟨_, _, _⟩; simp
  exact eq_of_heq ((eqRec_heq _ _).trans (Sigma.ext_iff.mp hsig).2)

end Graph.Ear

namespace SimpleGraph

variable {α : Type u}

/-- Converting a simple-graph ear to `Graph.ofSimpleGraph H` and back recovers the original ear. -/
@[simp] theorem Ear.toSimpleGraph_toGraph {H : SimpleGraph α} {S : H.Subgraph} (e : H.Ear S) :
    e.toGraph.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph e.toGraph.base_le) = e :=
  SimpleGraph.Ear.ext <| by
    rw [SimpleGraph.Ear.toWalk_copy, Graph.Ear.toWalk_toSimpleGraph, SimpleGraph.Ear.toWalk_toGraph]
    rcases e.toWalk with ⟨_, _, _⟩; simp

/-- Ears of `H` over `S : H.Subgraph` correspond bijectively to multigraph ears of
`Graph.ofSimpleGraph H` over `S.toGraph`. -/
def earEquivOfSimpleGraph (H : SimpleGraph α) (S : H.Subgraph) :
    H.Ear S ≃ (Graph.ofSimpleGraph H).Ear S.toGraph where
  toFun e := e.toGraph
  invFun e := e.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph e.base_le)
  left_inv := Ear.toSimpleGraph_toGraph
  right_inv e := by dsimp only; rw [Ear.toGraph_copy]; exact e.toGraph_toSimpleGraph

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
  | vertex v => simp [Graph.EarStart.isCycle_iff_of_heq _ (heq_toGraph_vertex v)]
  | cycle c hc => simp [Graph.EarStart.isCycle_iff_of_heq _ (heq_toGraph_cycle c hc)]

end SimpleGraph.EarStart

namespace Graph.EarStart

variable {V : Type u} {G : SimpleGraph V} {K : Graph V (Sym2 V)}

/-- Transport the initial vertex or cycle of a multigraph ear decomposition to the corresponding
simple subgraph. -/
def toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    G.EarStart (K.toSimpleGraphSubgraph s.le) :=
  match s with
  | .vertex v => (Graph.toSimpleGraphSubgraph_noEdge_singleton v.1
      (Graph.EarStart.vertex v).le).symm ▸ .vertex v.1
  | .cycle p hp => (Graph.Walk.toSimpleGraphSubgraph_walkGraph p
      (Graph.EarStart.cycle p hp).le).symm ▸
        .cycle p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)

/-- Transporting a vertex initial stage selects the corresponding simple-graph vertex stage. -/
theorem heq_toSimpleGraph_vertex (v : V(Graph.ofSimpleGraph G)) :
    HEq (Graph.EarStart.vertex v).toSimpleGraph (SimpleGraph.EarStart.vertex (G := G) v.1) := by
  unfold toSimpleGraph; exact eqRec_heq _ _

/-- Transporting a cycle initial stage selects the corresponding simple-graph cycle stage. -/
theorem heq_toSimpleGraph_cycle {x : V} (p : (Graph.ofSimpleGraph G).Walk x x) (hp : p.IsCycle) :
    HEq (Graph.EarStart.cycle p hp).toSimpleGraph
      (SimpleGraph.EarStart.cycle p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)) := by
  unfold toSimpleGraph; exact eqRec_heq _ _

@[simp] theorem isCycle_toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    s.toSimpleGraph.IsCycle ↔ s.IsCycle := by
  cases s <;> exact (SimpleGraph.EarStart.isCycle_eqRec _ _).trans (by simp)

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

/-- Converting a simple-graph initial witness to `Graph.ofSimpleGraph H` and back recovers it
heterogeneously. -/
theorem EarStart.heq_toSimpleGraph_toGraph {H : SimpleGraph α}
    {S : H.Subgraph} (s : H.EarStart S) : HEq s.toGraph.toSimpleGraph s := by
  cases s with
  | vertex v =>
      exact (earStart_toSimpleGraph_heq_of_heq (Subgraph.toGraph_singletonSubgraph v)
        (EarStart.heq_toGraph_vertex v)).trans (Graph.EarStart.heq_toSimpleGraph_vertex _)
  | cycle c hc =>
      exact (earStart_toSimpleGraph_heq_of_heq c.toGraph_toSubgraph
        (EarStart.heq_toGraph_cycle c hc)).trans
        ((Graph.EarStart.heq_toSimpleGraph_cycle _ _).trans
          (EarStart.heq_cycle_of_eq _ _ (SimpleGraph.Walk.toSimpleGraph_toGraph c)))

/-- Converting a simple-graph initial witness to `Graph.ofSimpleGraph H` and back recovers it. -/
@[simp] theorem EarStart.toSimpleGraph_toGraph {H : SimpleGraph α}
    {S : H.Subgraph} (s : H.EarStart S) :
    (S.toSimpleGraphSubgraph_toGraph s.toGraph.le) ▸ s.toGraph.toSimpleGraph = s :=
  eq_of_heq ((eqRec_heq _ _).trans s.heq_toSimpleGraph_toGraph)

/-- Converting a multigraph initial witness in `Graph.ofSimpleGraph H` to `SimpleGraph` and back
recovers it heterogeneously. -/
theorem _root_.Graph.EarStart.heq_toGraph_toSimpleGraph {H : SimpleGraph α}
    {K : Graph α (Sym2 α)} (s : (Graph.ofSimpleGraph H).EarStart K) :
    HEq s.toSimpleGraph.toGraph s := by
  cases s with
  | vertex v =>
      exact (earStart_toGraph_heq_of_heq (Graph.toSimpleGraphSubgraph_noEdge_singleton v.1 _)
        (Graph.EarStart.heq_toSimpleGraph_vertex v)).trans ((EarStart.heq_toGraph_vertex v.1).trans
        (by rw [show (⟨v.1, mem_univ v.1⟩ : V(Graph.ofSimpleGraph H)) = v from Subtype.ext rfl]))
  | cycle walk isCycle =>
      exact (earStart_toGraph_heq_of_heq (walk.toSimpleGraphSubgraph_walkGraph _)
        (Graph.EarStart.heq_toSimpleGraph_cycle walk isCycle)).trans
        ((EarStart.heq_toGraph_cycle _ _).trans
          (Graph.EarStart.heq_cycle_of_eq _ _ (Graph.Walk.toGraph_toSimpleGraph walk)))

/-- Converting a multigraph initial witness in `Graph.ofSimpleGraph H` to `SimpleGraph` and back
recovers it. -/
@[simp] theorem _root_.Graph.EarStart.toGraph_toSimpleGraph {H : SimpleGraph α}
    {K : Graph α (Sym2 α)} (s : (Graph.ofSimpleGraph H).EarStart K) :
    (K.toGraph_toSimpleGraphSubgraph s.le) ▸ s.toSimpleGraph.toGraph = s :=
  eq_of_heq ((eqRec_heq _ _).trans s.heq_toGraph_toSimpleGraph)

/-- Initial witnesses `H.EarStart S` correspond bijectively to multigraph initial witnesses
`(Graph.ofSimpleGraph H).EarStart S.toGraph`. -/
def earStartEquivOfSimpleGraph (H : SimpleGraph α) (S : H.Subgraph) :
    H.EarStart S ≃ (Graph.ofSimpleGraph H).EarStart S.toGraph where
  toFun s := s.toGraph
  invFun s := (S.toSimpleGraphSubgraph_toGraph s.le) ▸ s.toSimpleGraph
  left_inv := EarStart.toSimpleGraph_toGraph
  right_inv s := eq_of_heq ((earStart_toGraph_heq_of_heq
    (S.toSimpleGraphSubgraph_toGraph s.le).symm (eqRec_heq _ _)).trans
    s.heq_toGraph_toSimpleGraph)

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

theorem heq_start_toGraph (d : H.EarDecomposition S) : HEq d.toGraph.start d.start.toGraph := .rfl

@[simp] theorem start_isCycle_toGraph (d : H.EarDecomposition S) :
    d.toGraph.start.IsCycle ↔ d.start.IsCycle :=
  (Graph.EarStart.isCycle_iff_of_heq (d.graphAfter_toGraph 0) d.heq_start_toGraph).trans
    d.start.isCycle_toGraph

@[simp] theorem isVertexStart_toGraph (d : H.EarDecomposition S) :
    d.toGraph.IsVertexStart ↔ d.IsVertexStart := by
  rw [Graph.EarDecomposition.isVertexStart_iff_not_start_isCycle,
    isVertexStart_iff_not_start_isCycle, start_isCycle_toGraph]

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

@[simp] theorem isOpen_toGraph (d : H.EarDecomposition S) : d.toGraph.IsOpen ↔ d.IsOpen := by
  rw [Graph.EarDecomposition.isOpen_iff, isOpen_iff, start_isCycle_toGraph]
  exact and_congr_right fun _ ↦
    ⟨fun h i ↦ by
      have hi := h (Fin.cast d.length_toGraph.symm i); rw [kindAt_toGraph] at hi; simpa using hi,
     fun h i ↦ by rw [kindAt_toGraph, EarKind.toGraph_eq_open_iff]; exact h _⟩

end SimpleGraph.EarDecomposition

namespace Graph.EarDecomposition

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
    exact ((Graph.toSimpleGraphSubgraph_congr (d.graphAfter_succ i) _ e.add_le).trans
      ((e.toSimpleGraphSubgraph_add e.add_le).trans
        ((SimpleGraph.Ear.adjoin_def _).trans
          (congrArg (· ⊔ e.toSimpleGraph.toSubgraph) hbase)))).trans
      (SimpleGraph.Ear.adjoin_copy _ _).symm
  subgraphAfter_last :=
    Graph.toSimpleGraphSubgraph_congr d.graphAfter_last
      (d.graphAfter_le (Fin.last d.length)) d.final_le

@[simp] theorem length_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.length = d.length := rfl

@[simp] theorem subgraphAfter_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin (d.length + 1)) :
    d.toSimpleGraph.subgraphAfter i =
      (d.graphAfter i).toSimpleGraphSubgraph (d.graphAfter_le i) := rfl

@[simp] theorem initial_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.initial =
      (d.graphAfter 0).toSimpleGraphSubgraph (d.graphAfter_le 0) :=
  (SimpleGraph.EarDecomposition.subgraphAfter_zero d.toSimpleGraph).symm

theorem toGraph_initial_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.initial.toGraph = d.initial := by
  rw [initial_toSimpleGraph, Graph.toGraph_toSimpleGraphSubgraph, initial_eq_graphAfter]

/-- The transported decomposition retains the transported initial-stage witness. -/
@[simp] theorem start_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.start = d.start.toSimpleGraph := (rfl)

@[simp] theorem isVertexStart_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.IsVertexStart ↔ d.IsVertexStart := by
  rw [SimpleGraph.EarDecomposition.isVertexStart_iff_not_start_isCycle,
    isVertexStart_iff_not_start_isCycle, start_toSimpleGraph]
  exact not_congr d.start.isCycle_toSimpleGraph

/-- The transported decomposition displays the transported ear at each step, copied only across
the equality identifying its stored base with the corresponding prefix. -/
@[simp] theorem earAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) :
    d.toSimpleGraph.earAt i =
      (d.earAt i).2.toSimpleGraph.copy
        (Graph.toSimpleGraphSubgraph_congr (d.earAt_fst i) (d.earAt i).2.base_le
          (d.graphAfter_le i.castSucc)) := (rfl)

@[simp] theorem kindAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) : d.toSimpleGraph.kindAt i = (d.kindAt i).toSimpleGraph := by
  simp [SimpleGraph.EarDecomposition.kindAt_def, Graph.EarDecomposition.kindAt_eq, toSimpleGraph]

@[simp] theorem walkAt_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (i : Fin d.length) :
    d.toSimpleGraph.walkAt i =
      ⟨(d.walkAt i).1, (d.walkAt i).2.1, (d.walkAt i).2.2.toSimpleGraph⟩ := by
  rw [Graph.EarDecomposition.walkAt_eq]
  simp [SimpleGraph.EarDecomposition.walkAt_def, toSimpleGraph]

/-- Transport preserves the open-ear-decomposition predicate. -/
@[simp] theorem isOpen_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.IsOpen ↔ d.IsOpen := by
  rw [SimpleGraph.EarDecomposition.isOpen_iff, Graph.EarDecomposition.isOpen_iff,
    start_toSimpleGraph]
  exact and_congr d.start.isCycle_toSimpleGraph
    (by simpa only [length_toSimpleGraph] using (forall_congr' fun i : Fin d.length ↦ by simp))

/-- `toSimpleGraph` commutes with `copy`. -/
theorem toSimpleGraph_copy {K' : Graph V (Sym2 V)}
    (d : (Graph.ofSimpleGraph G).EarDecomposition K) (h : K = K') :
    (d.copy h).toSimpleGraph =
      d.toSimpleGraph.copy
        (Graph.toSimpleGraphSubgraph_congr h d.final_le (d.copy h).final_le) := by
  subst h; rw [copy_rfl]; rfl

/-- Converting `Graph.EarDecomposition.vertex` to `SimpleGraph` yields
`SimpleGraph.EarDecomposition.vertex`, reindexed along `toSimpleGraphSubgraph_noEdge_singleton`. -/
theorem toSimpleGraph_vertex (v : V(Graph.ofSimpleGraph G)) :
    (vertex v).toSimpleGraph =
      (SimpleGraph.EarDecomposition.vertex G v.1).copy
        (Graph.toSimpleGraphSubgraph_noEdge_singleton v.1 (vertex v).final_le).symm :=
  SimpleGraph.EarDecomposition.ext (by simp) (SimpleGraph.Subgraph.toGraph_injective <| by
    rw [toGraph_initial_toSimpleGraph, initial_vertex, SimpleGraph.EarDecomposition.initial_copy,
      SimpleGraph.EarDecomposition.initial_vertex, SimpleGraph.Subgraph.toGraph_singletonSubgraph])
    (by
      rw [start_toSimpleGraph, SimpleGraph.EarDecomposition.start_copy,
        SimpleGraph.EarDecomposition.start_vertex]
      exact (SimpleGraph.earStart_toSimpleGraph_heq_of_heq (graphAfter_vertex_zero v)
        (heq_start_vertex v)).trans
        ((Graph.EarStart.heq_toSimpleGraph_vertex v).trans (eqRec_heq _ _).symm))
    fun i ↦ (Fin.cast (by simp) i).elim0

/-- Converting `Graph.EarDecomposition.cycle` to `SimpleGraph` yields
`SimpleGraph.EarDecomposition.cycle`, reindexed along `Walk.toSimpleGraphSubgraph_walkGraph`. -/
theorem toSimpleGraph_cycle {u : V} (p : (Graph.ofSimpleGraph G).Walk u u) (hp : p.IsCycle) :
    (cycle p hp).toSimpleGraph =
      (SimpleGraph.EarDecomposition.cycle p.toSimpleGraph
        (p.isCycle_toSimpleGraph_iff.mpr hp)).copy
        (Graph.Walk.toSimpleGraphSubgraph_walkGraph p (cycle p hp).final_le).symm :=
  SimpleGraph.EarDecomposition.ext (by simp) (SimpleGraph.Subgraph.toGraph_injective <| by
    rw [toGraph_initial_toSimpleGraph, initial_cycle, SimpleGraph.EarDecomposition.initial_copy,
      SimpleGraph.EarDecomposition.initial_cycle, SimpleGraph.Walk.toGraph_toSubgraph,
      Graph.Walk.toGraph_toSimpleGraph])
    (by
      rw [start_toSimpleGraph, SimpleGraph.EarDecomposition.start_copy,
        SimpleGraph.EarDecomposition.start_cycle]
      exact (SimpleGraph.earStart_toSimpleGraph_heq_of_heq (graphAfter_cycle_zero p hp)
        (heq_start_cycle p hp)).trans
        ((Graph.EarStart.heq_toSimpleGraph_cycle p hp).trans (eqRec_heq _ _).symm))
    fun i ↦ (Fin.cast (by simp) i).elim0

/-- `toSimpleGraph` commutes with `snoc`. -/
theorem toSimpleGraph_snoc (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (e : (Graph.ofSimpleGraph G).Ear K) :
    (d.snoc e).toSimpleGraph =
      (d.toSimpleGraph.snoc e.toSimpleGraph).copy
        (e.toSimpleGraphSubgraph_add (d.snoc e).final_le).symm := by
  have hlen : (d.snoc e).toSimpleGraph.length =
      ((d.toSimpleGraph.snoc e.toSimpleGraph).copy
        (e.toSimpleGraphSubgraph_add (d.snoc e).final_le).symm).length := by simp
  refine SimpleGraph.EarDecomposition.ext hlen (SimpleGraph.Subgraph.toGraph_injective <| by
    rw [toGraph_initial_toSimpleGraph, initial_snoc, SimpleGraph.EarDecomposition.initial_copy,
      SimpleGraph.EarDecomposition.initial_snoc, toGraph_initial_toSimpleGraph]) ?_ fun i ↦ ?_
  · rw [start_toSimpleGraph, SimpleGraph.EarDecomposition.start_copy,
      SimpleGraph.EarDecomposition.start_snoc]
    refine (SimpleGraph.earStart_toSimpleGraph_heq_of_heq ?_ (d.heq_start_snoc e)).trans
      (eqRec_heq _ _).symm
    rw [show (0 : Fin ((d.snoc e).length + 1)) =
      (Fin.cast (d.length_snoc e).symm (0 : Fin (d.length + 1))).castSucc from Fin.ext rfl,
      graphAfter_snoc_castSucc]
  · let i₀ : Fin (d.snoc e).length := i
    let m : Fin (d.toSimpleGraph.snoc e.toSimpleGraph).length := Fin.cast hlen i
    refine ((walkAt_toSimpleGraph (d.snoc e) i₀).trans ?_).trans
      (SimpleGraph.EarDecomposition.walkAt_copy _ _ m).symm
    by_cases hi : i.1 = d.length
    · have hm : m = Fin.last d.toSimpleGraph.length := Fin.ext hi
      have hi' : i₀ = Fin.cast (d.length_snoc e).symm (Fin.last d.length) := Fin.ext hi
      rw [hm, SimpleGraph.EarDecomposition.walkAt_snoc_last, Graph.Ear.toWalk_toSimpleGraph, hi',
        walkAt_eq, earAt_snoc_last]
    · let j : Fin d.length := ⟨i.1, by have := i.2; simp at this; omega⟩
      let j' : Fin d.toSimpleGraph.length := j
      have hm : m = j'.castSucc := Fin.ext rfl
      have hi' : i₀ = Fin.cast (d.length_snoc e).symm j.castSucc := Fin.ext rfl
      rw [hm, SimpleGraph.EarDecomposition.walkAt_snoc_castSucc]
      exact (by rw [hi', walkAt_eq, earAt_snoc_castSucc, ← walkAt_eq] : _ = _).trans
        (d.walkAt_toSimpleGraph j).symm

/-- `toSimpleGraph` commutes with `prefix`. -/
theorem toSimpleGraph_prefix (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (k : Fin (d.length + 1)) :
    (d.prefix k).toSimpleGraph = d.toSimpleGraph.prefix k := by
  have hlen : (d.prefix k).toSimpleGraph.length = (d.toSimpleGraph.prefix k).length :=
    (d.length_prefix k).trans (d.toSimpleGraph.length_prefix k).symm
  refine SimpleGraph.EarDecomposition.ext hlen ?_ ?_ fun i ↦ ?_
  · exact SimpleGraph.Subgraph.toGraph_injective <|
      ((d.prefix k).toGraph_initial_toSimpleGraph.trans (d.initial_prefix k)).trans
        (d.toGraph_initial_toSimpleGraph.symm.trans
          (congrArg SimpleGraph.Subgraph.toGraph (d.toSimpleGraph.initial_prefix k).symm))
  · refine SimpleGraph.earStart_toSimpleGraph_heq_of_heq ?_ (d.heq_start_prefix k)
    rw [show (0 : Fin ((d.prefix k).length + 1)) =
      Fin.cast (congrArg (· + 1) (d.length_prefix k).symm) 0 from Fin.ext rfl,
      graphAfter_prefix, Fin.castLE_zero]
  · let j : Fin k := Fin.cast hlen i
    have h1 : (d.prefix k).toSimpleGraph.walkAt i =
        ⟨(d.walkAt (j.castLE k.is_le)).1, (d.walkAt (j.castLE k.is_le)).2.1,
          (d.walkAt (j.castLE k.is_le)).2.2.toSimpleGraph⟩ := by
      rw [walkAt_toSimpleGraph (d.prefix k) i,
        show (i : Fin (d.prefix k).length) = Fin.cast (d.length_prefix k).symm j from Fin.ext rfl,
        walkAt_eq, earAt_prefix, ← walkAt_eq]
    exact h1.trans ((d.walkAt_toSimpleGraph (j.castLE k.is_le)).symm.trans
      (d.toSimpleGraph.walkAt_prefix k j).symm)

end OfSimpleGraph

end Graph.EarDecomposition

namespace SimpleGraph

variable {α : Type u}

/-- `toGraph` commutes with `copy`. -/
theorem EarDecomposition.toGraph_copy {H : SimpleGraph α} {S S' : H.Subgraph}
    (d : H.EarDecomposition S) (h : S = S') :
    (d.copy h).toGraph = d.toGraph.copy (congrArg Subgraph.toGraph h) := by
  subst h; exact (Graph.EarDecomposition.copy_rfl _).symm

/-- Converting a simple-graph ear decomposition to `Graph.ofSimpleGraph H` and back recovers the
original ear decomposition. -/
@[simp] theorem EarDecomposition.toSimpleGraph_toGraph {H : SimpleGraph α} {S : H.Subgraph}
    (d : H.EarDecomposition S) :
    d.toGraph.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph d.toGraph.final_le) = d := by
  have hlen : (d.toGraph.toSimpleGraph.copy
      (S.toSimpleGraphSubgraph_toGraph d.toGraph.final_le)).length = d.length := by simp
  refine EarDecomposition.ext hlen (Subgraph.toGraph_injective <| by
    rw [EarDecomposition.initial_copy, Graph.EarDecomposition.toGraph_initial_toSimpleGraph,
      EarDecomposition.initial_toGraph]) ?_ fun i ↦ ?_
  · rw [EarDecomposition.start_copy, Graph.EarDecomposition.start_toSimpleGraph]
    exact (earStart_toSimpleGraph_heq_of_heq (d.graphAfter_toGraph 0) d.heq_start_toGraph).trans
      d.start.heq_toSimpleGraph_toGraph
  · let i₀ : Fin d.toGraph.length := i
    rw [d.toGraph.toSimpleGraph.walkAt_copy _ i₀,
      Graph.EarDecomposition.walkAt_toSimpleGraph d.toGraph i₀, EarDecomposition.walkAt_toGraph,
      show Fin.cast (EarDecomposition.length_toGraph d) i₀ = Fin.cast hlen i from Fin.ext rfl]
    rcases d.walkAt (Fin.cast hlen i) with ⟨_, _, _⟩; simp

/-- Converting a multigraph ear decomposition in `Graph.ofSimpleGraph H` to `SimpleGraph` and back
recovers the original ear decomposition. -/
@[simp] theorem _root_.Graph.EarDecomposition.toGraph_toSimpleGraph {H : SimpleGraph α}
    {K : Graph α (Sym2 α)} (d : (Graph.ofSimpleGraph H).EarDecomposition K) :
    d.toSimpleGraph.toGraph.copy (K.toGraph_toSimpleGraphSubgraph d.final_le) = d := by
  have hlen : (d.toSimpleGraph.toGraph.copy
      (K.toGraph_toSimpleGraphSubgraph d.final_le)).length = d.length := by simp
  refine Graph.EarDecomposition.ext _ _ hlen ?_ ((Fin.heq_fun_iff hlen).mpr fun i ↦ ?_)
  · exact (Graph.EarDecomposition.heq_start_copy _ _).trans
      ((EarDecomposition.heq_start_toGraph _).trans
        ((earStart_toGraph_heq_of_heq rfl (heq_of_eq d.start_toSimpleGraph)).trans
          d.start.heq_toGraph_toSimpleGraph))
  · rw [Graph.EarDecomposition.earAt_copy, EarDecomposition.earAt_toGraph]
    let m : Fin d.length := ⟨i.1, hlen ▸ i.2⟩
    have hm : Fin.cast (EarDecomposition.length_toGraph d.toSimpleGraph)
        (Fin.cast (Graph.EarDecomposition.length_copy _ _) i) = m := Fin.ext rfl
    refine Graph.Ear.sigma_ext ?_ ?_
    · dsimp only; rw [hm]
      exact (congrArg Subgraph.toGraph (d.subgraphAfter_toSimpleGraph m.castSucc)).trans
        ((Graph.toGraph_toSimpleGraphSubgraph _ _).trans (d.earAt_fst m).symm)
    · dsimp only
      rw [Ear.toWalk_toGraph, ← EarDecomposition.walkAt_def, hm, d.walkAt_toSimpleGraph,
        Graph.EarDecomposition.walkAt_eq]
      rcases (d.earAt m).2.toWalk with ⟨_, _, _⟩; simp

/-- Ear decompositions of `S : H.Subgraph` in `H` correspond bijectively to multigraph ear
decompositions of `S.toGraph` in `Graph.ofSimpleGraph H`. -/
def earDecompositionEquivOfSimpleGraph (H : SimpleGraph α) (S : H.Subgraph) :
    H.EarDecomposition S ≃ (Graph.ofSimpleGraph H).EarDecomposition S.toGraph where
  toFun d := d.toGraph
  invFun d := d.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph d.final_le)
  left_inv := EarDecomposition.toSimpleGraph_toGraph
  right_inv d := (d.toSimpleGraph.toGraph_copy _).trans d.toGraph_toSimpleGraph

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
    H.earDecompositionTopEquivOfSimpleGraph d = d.toGraph.copy Subgraph.toGraph_top := by
  simp [earDecompositionTopEquivOfSimpleGraph]
@[simp] theorem earDecompositionTopEquivOfSimpleGraph_symm_apply (H : SimpleGraph α)
    (d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)) :
    H.earDecompositionTopEquivOfSimpleGraph.symm d =
      (d.copy Subgraph.toGraph_top.symm).toSimpleGraph.copy
        ((⊤ : H.Subgraph).toSimpleGraphSubgraph_toGraph _) := by
  simp [earDecompositionTopEquivOfSimpleGraph]

namespace EarDecomposition

variable {H : SimpleGraph α} {S : H.Subgraph}

private theorem sigma_walk_toGraph_injective :
    Function.Injective (fun w : Σ u v : α, H.Walk u v ↦
      (⟨w.1, w.2.1, w.2.2.toGraph⟩ : Σ u v : α, (Graph.ofSimpleGraph H).Walk u v)) := by
  rintro ⟨u₁, v₁, p₁⟩ ⟨u₂, v₂, p₂⟩ h
  injection h with hu h'; subst hu
  injection h' with hv hp; subst hv
  exact congrArg (fun q ↦ (⟨u₁, v₁, q⟩ : Σ u v : α, H.Walk u v))
    (by simpa using congrArg Graph.Walk.toSimpleGraph (eq_of_heq hp))

private theorem earStart_heq_of_toGraph_heq {S₁ S₂ : H.Subgraph}
    {s₁ : H.EarStart S₁} {s₂ : H.EarStart S₂}
    (hS : S₁ = S₂) (hs : HEq s₁.toGraph s₂.toGraph) : HEq s₁ s₂ :=
  s₁.heq_toSimpleGraph_toGraph.symm.trans
    ((earStart_toSimpleGraph_heq_of_heq (congrArg Subgraph.toGraph hS) hs).trans
      s₂.heq_toSimpleGraph_toGraph)

/-- Converting `EarDecomposition.vertex` to `Graph.ofSimpleGraph H` yields
`Graph.EarDecomposition.vertex`, reindexed along `toGraph_singletonSubgraph`. -/
theorem toGraph_vertex (v : α) :
    (vertex H v).toGraph =
      (Graph.EarDecomposition.vertex (G := Graph.ofSimpleGraph H) ⟨v, mem_univ v⟩).copy
        (Subgraph.toGraph_singletonSubgraph (G := H) v).symm := by
  refine Graph.EarDecomposition.ext_of_length_eq_zero (by simp) (by simp) <|
    (heq_start_toGraph _).trans ?_
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
  refine Graph.EarDecomposition.ext_of_length_eq_zero (by simp) (by simp) <|
    (heq_start_toGraph _).trans ?_
  rw [start_cycle]
  exact (earStart_toGraph_heq_of_heq (subgraphAfter_cycle c hc 0) (eqRec_heq _ _)).trans
    ((EarStart.heq_toGraph_cycle c hc).trans
      ((Graph.EarDecomposition.heq_start_cycle _ _).symm.trans
        (Graph.EarDecomposition.heq_start_copy _ _).symm))

/-- `toGraph` commutes with `snoc`. -/
theorem toGraph_snoc (d : H.EarDecomposition S) (e : H.Ear S) :
    (d.snoc e).toGraph = (d.toGraph.snoc e.toGraph).copy e.add_toGraph := by
  have hlen : (d.snoc e).toGraph.length =
      ((d.toGraph.snoc e.toGraph).copy e.add_toGraph).length := by simp
  refine Graph.EarDecomposition.ext _ _ hlen ?_ ((Fin.heq_fun_iff hlen).mpr fun i ↦ ?_)
  · refine (heq_start_toGraph _).trans ?_; rw [start_snoc]
    exact (earStart_toGraph_heq_of_heq (by simp) (eqRec_heq _ _)).trans
      ((heq_start_toGraph d).symm.trans ((d.toGraph.heq_start_snoc e.toGraph).symm.trans
        (Graph.EarDecomposition.heq_start_copy _ _).symm))
  · suffices ∀ m : Fin _, m.1 = i.1 →
        (d.snoc e).toGraph.earAt i = ((d.toGraph.snoc e.toGraph).copy e.add_toGraph).earAt m from
      this _ rfl
    intro m hm
    by_cases hi : i.1 = d.length
    · rw [Graph.EarDecomposition.earAt_copy,
        show Fin.cast (Graph.EarDecomposition.length_copy _ _) m =
          Fin.cast (d.toGraph.length_snoc e.toGraph).symm (Fin.last d.toGraph.length) from
          Fin.ext (by simp [hm, hi]), Graph.EarDecomposition.earAt_snoc_last]
      refine Graph.Ear.sigma_ext ?_ ?_
      · rw [earAt_toGraph]; dsimp only
        rw [show (Fin.cast (length_toGraph (d.snoc e)) i).castSucc =
            (Fin.last d.length).castSucc from Fin.ext hi,
          subgraphAfter_snoc_castSucc, d.subgraphAfter_last]
      · rw [← Graph.EarDecomposition.walkAt_eq, walkAt_toGraph,
          show Fin.cast (length_toGraph (d.snoc e)) i = Fin.last d.length from Fin.ext hi,
          walkAt_snoc_last, Ear.toWalk_toGraph]
    · let j : Fin d.length := ⟨i.1, by have := i.2; simp at this; omega⟩
      let j' : Fin d.toGraph.length := Fin.cast d.length_toGraph.symm j
      rw [Graph.EarDecomposition.earAt_copy,
        show Fin.cast (Graph.EarDecomposition.length_copy _ _) m =
          Fin.cast (d.toGraph.length_snoc e.toGraph).symm j'.castSucc from Fin.ext hm,
        Graph.EarDecomposition.earAt_snoc_castSucc, d.earAt_toGraph j',
        show Fin.cast (length_toGraph d) j' = j from Fin.ext rfl]
      refine Graph.Ear.sigma_ext ?_ ?_
      · rw [earAt_toGraph]; dsimp only
        rw [show (Fin.cast (length_toGraph (d.snoc e)) i).castSucc = j.castSucc.castSucc from
          Fin.ext rfl, subgraphAfter_snoc_castSucc]
      · rw [← Graph.EarDecomposition.walkAt_eq, walkAt_toGraph,
          show Fin.cast (length_toGraph (d.snoc e)) i = j.castSucc from Fin.ext rfl,
          walkAt_snoc_castSucc, walkAt_def, Ear.toWalk_toGraph]

/-- `toGraph` commutes with `prefix`. -/
theorem toGraph_prefix (d : H.EarDecomposition S) (k : Fin (d.length + 1)) :
    (d.prefix k).toGraph =
      (d.toGraph.prefix (Fin.cast (congrArg (· + 1) d.length_toGraph.symm) k)).copy
        (d.graphAfter_toGraph _) := by
  let k' : Fin (d.toGraph.length + 1) := Fin.cast (congrArg (· + 1) d.length_toGraph.symm) k
  have hlen : (d.prefix k).toGraph.length =
      ((d.toGraph.prefix k').copy (d.graphAfter_toGraph k')).length := by simp [k']
  refine Graph.EarDecomposition.ext _ _ hlen
    ((heq_start_toGraph _).trans ((heq_start_toGraph d).symm.trans
      ((d.toGraph.heq_start_prefix k').symm.trans
        (Graph.EarDecomposition.heq_start_copy _ _).symm)))
    ((Fin.heq_fun_iff hlen).mpr fun j ↦ ?_)
  suffices ∀ m : Fin _, m.1 = j.1 →
      (d.prefix k).toGraph.earAt j =
        ((d.toGraph.prefix k').copy (d.graphAfter_toGraph k')).earAt m from this _ rfl
  intro m hm
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
  refine Graph.Ear.sigma_ext hj1 ?_; dsimp only
  rw [hj2, Ear.toWalk_toGraph, Ear.toWalk_toGraph, ← (d.prefix k).walkAt_def, ← d.walkAt_def,
    show Fin.cast (length_toGraph (d.prefix k)) j = j₁ from Fin.ext rfl, walkAt_prefix]

/-! ### Initial-stage replacement and vertex-start normalization via transport -/

private theorem subgraphAfter_eq_of_toGraph_copy_eq {K : Graph α (Sym2 α)} {hS : S.toGraph = K}
    {d : H.EarDecomposition S} {d' : (Graph.ofSimpleGraph H).EarDecomposition K}
    (h : d.toGraph.copy hS = d') (i : Fin (d.length + 1)) (j : Fin (d'.length + 1))
    (hij : i.1 = j.1) {T : H.Subgraph} (hT : d'.graphAfter j = T.toGraph) :
    d.subgraphAfter i = T := by
  apply Subgraph.toGraph_injective
  have heq := Graph.EarDecomposition.graphAfter_eq_of_eq h i.1 (by simpa using i.2) (hij ▸ j.2)
  rw [Graph.EarDecomposition.graphAfter_copy, graphAfter_toGraph] at heq
  exact (congrArg (fun x ↦ (d.subgraphAfter x).toGraph) (Fin.ext rfl)).trans
    (heq.trans ((congrArg d'.graphAfter (Fin.ext hij)).trans hT))

private theorem walkAt_eq_of_toGraph_copy_eq {K : Graph α (Sym2 α)} {hS : S.toGraph = K}
    {d : H.EarDecomposition S} {d' : (Graph.ofSimpleGraph H).EarDecomposition K}
    (h : d.toGraph.copy hS = d') (i : Fin d.length) (j : Fin d'.length) (hij : i.1 = j.1)
    {w : Σ u v : α, H.Walk u v}
    (hw : (d'.earAt j).2.toWalk = ⟨w.1, w.2.1, w.2.2.toGraph⟩) :
    d.walkAt i = w := by
  apply sigma_walk_toGraph_injective
  have heq := congrArg (fun p : Σ L, (Graph.ofSimpleGraph H).Ear L ↦ p.2.toWalk)
    ((Graph.EarDecomposition.earAt_eq_of_eq h i.1 (by simp) (hij ▸ j.2)).trans
      (congrArg d'.earAt (Fin.ext hij)))
  rw [Graph.EarDecomposition.earAt_copy, ← Graph.EarDecomposition.walkAt_eq, walkAt_toGraph] at heq
  exact (congrArg (fun x ↦ (⟨(d.walkAt x).1, (d.walkAt x).2.1, (d.walkAt x).2.2.toGraph⟩ :
    Σ u v : α, (Graph.ofSimpleGraph H).Walk u v)) (Fin.ext rfl)).trans (heq.trans hw)

private theorem kindAt_eq_of_toGraph_copy_eq {K : Graph α (Sym2 α)} {hS : S.toGraph = K}
    {d : H.EarDecomposition S} {d' : (Graph.ofSimpleGraph H).EarDecomposition K}
    (h : d.toGraph.copy hS = d') (i : Fin d.length) (j : Fin d'.length) (hij : i.1 = j.1)
    {k : EarKind} (hk : (d'.earAt j).2.kind = k.toGraph) :
    d.kindAt i = k := by
  apply EarKind.toGraph_injective
  have heq := congrArg (fun p : Σ L, (Graph.ofSimpleGraph H).Ear L ↦ p.2.kind)
    ((Graph.EarDecomposition.earAt_eq_of_eq h i.1 (by simp) (hij ▸ j.2)).trans
      (congrArg d'.earAt (Fin.ext hij)))
  rw [Graph.EarDecomposition.earAt_copy, ← Graph.EarDecomposition.kindAt_eq, kindAt_toGraph] at heq
  exact (congrArg (fun x ↦ (d.kindAt x).toGraph) (Fin.ext rfl)).trans (heq.trans hk)

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
  rw [← length_toGraph, toGraph_replaceInitial]; simp

@[simp] theorem initial_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) : (d.replaceInitial d₀).initial = d₀.initial :=
  Subgraph.toGraph_injective (by
    rw [← initial_toGraph, toGraph_replaceInitial, Graph.EarDecomposition.initial_replaceInitial,
      Graph.EarDecomposition.initial_copy, initial_toGraph])

/-- Replacing the initial stage sets the initial stage witness to that of `d₀`. -/
theorem heq_start_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) : HEq (d.replaceInitial d₀).start d₀.start :=
  earStart_heq_of_toGraph_heq ((d.replaceInitial d₀).subgraphAfter_zero.trans
      ((d.initial_replaceInitial d₀).trans d₀.subgraphAfter_zero.symm)) <|
    (d.replaceInitial d₀).heq_start_toGraph.symm.trans
      ((Graph.EarDecomposition.heq_start_of_eq (d.toGraph_replaceInitial d₀)).trans
        ((d.toGraph.heq_start_replaceInitial _).trans
          ((Graph.EarDecomposition.heq_start_copy _ _).trans d₀.heq_start_toGraph)))

@[simp] theorem start_isCycle_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).start.IsCycle ↔ d₀.start.IsCycle := by
  rw [← start_isCycle_toGraph, toGraph_replaceInitial]; simp

@[simp] theorem isVertexStart_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).IsVertexStart ↔ d₀.IsVertexStart := by simp [isVertexStart_iff]

/-- Replacing the initial stage retains every stage subgraph of `d₀`. -/
@[simp] theorem subgraphAfter_replaceInitial_castLE (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) (i : Fin (d₀.length + 1)) :
    (d.replaceInitial d₀).subgraphAfter
      (Fin.castLE (Nat.succ_le_succ ((Nat.le_add_right d₀.length d.length).trans_eq
        (d.length_replaceInitial d₀).symm)) i) = d₀.subgraphAfter i :=
  subgraphAfter_eq_of_toGraph_copy_eq (hS := rfl)
    ((d.replaceInitial d₀).toGraph.copy_rfl.trans (d.toGraph_replaceInitial d₀)) _
    (Fin.castLE (Nat.succ_le_succ ((Nat.le_add_right _ _).trans_eq
      (d.toGraph.length_replaceInitial _).symm)) (Fin.cast (by simp) i)) rfl <| by
    rw [Graph.EarDecomposition.graphAfter_replaceInitial_castLE,
      Graph.EarDecomposition.graphAfter_copy, graphAfter_toGraph]; rfl

/-- Replacing the initial stage shifts every stage subgraph of `d` by `d₀.length`. -/
@[simp] theorem subgraphAfter_replaceInitial_natAdd (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) (i : Fin (d.length + 1)) :
    (d.replaceInitial d₀).subgraphAfter
      (Fin.cast ((Nat.add_assoc d₀.length d.length 1).symm.trans
        (congrArg (· + 1) (d.length_replaceInitial d₀).symm)) (Fin.natAdd d₀.length i)) =
      d.subgraphAfter i :=
  subgraphAfter_eq_of_toGraph_copy_eq (hS := rfl)
    ((d.replaceInitial d₀).toGraph.copy_rfl.trans (d.toGraph_replaceInitial d₀)) _
    (Fin.cast ((Nat.add_assoc _ _ 1).symm.trans
      (congrArg (· + 1) (d.toGraph.length_replaceInitial _).symm))
      (Fin.natAdd _ (Fin.cast (congrArg (· + 1) d.length_toGraph.symm) i))) (by simp) <| by
    rw [Graph.EarDecomposition.graphAfter_replaceInitial_natAdd, graphAfter_toGraph]; rfl

/-- Replacing the initial stage retains the walk of every ear of `d₀`. -/
@[simp] theorem walkAt_replaceInitial_castAdd (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) (i : Fin d₀.length) :
    (d.replaceInitial d₀).walkAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.castAdd d.length i)) = d₀.walkAt i :=
  walkAt_eq_of_toGraph_copy_eq (hS := rfl)
    ((d.replaceInitial d₀).toGraph.copy_rfl.trans (d.toGraph_replaceInitial d₀)) _
    (Fin.cast (d.toGraph.length_replaceInitial _).symm
      (Fin.castAdd _ (Fin.cast (by simp) i))) rfl <| by
    rw [Graph.EarDecomposition.earAt_replaceInitial_castAdd, Graph.EarDecomposition.earAt_copy,
      ← Graph.EarDecomposition.walkAt_eq, walkAt_toGraph]; rfl

/-- Replacing the initial stage retains the walk of every shifted ear of `d`. -/
@[simp] theorem walkAt_replaceInitial_natAdd (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) (i : Fin d.length) :
    (d.replaceInitial d₀).walkAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.natAdd d₀.length i)) = d.walkAt i :=
  walkAt_eq_of_toGraph_copy_eq (hS := rfl)
    ((d.replaceInitial d₀).toGraph.copy_rfl.trans (d.toGraph_replaceInitial d₀)) _
    (Fin.cast (d.toGraph.length_replaceInitial _).symm
      (Fin.natAdd _ (Fin.cast d.length_toGraph.symm i))) (by simp) <| by
    rw [Graph.EarDecomposition.earAt_replaceInitial_natAdd, ← Graph.EarDecomposition.walkAt_eq,
      walkAt_toGraph]; rfl

/-- Replacing the initial stage retains the kind of every ear of `d₀`. -/
@[simp] theorem kindAt_replaceInitial_castAdd (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) (i : Fin d₀.length) :
    (d.replaceInitial d₀).kindAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.castAdd d.length i)) = d₀.kindAt i :=
  kindAt_eq_of_toGraph_copy_eq (hS := rfl)
    ((d.replaceInitial d₀).toGraph.copy_rfl.trans (d.toGraph_replaceInitial d₀)) _
    (Fin.cast (d.toGraph.length_replaceInitial _).symm
      (Fin.castAdd _ (Fin.cast (by simp) i))) rfl <| by
    rw [Graph.EarDecomposition.earAt_replaceInitial_castAdd, Graph.EarDecomposition.earAt_copy,
      ← Graph.EarDecomposition.kindAt_eq, kindAt_toGraph]; rfl

/-- Replacing the initial stage retains the kind of every shifted ear of `d`. -/
@[simp] theorem kindAt_replaceInitial_natAdd (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) (i : Fin d.length) :
    (d.replaceInitial d₀).kindAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.natAdd d₀.length i)) = d.kindAt i :=
  kindAt_eq_of_toGraph_copy_eq (hS := rfl)
    ((d.replaceInitial d₀).toGraph.copy_rfl.trans (d.toGraph_replaceInitial d₀)) _
    (Fin.cast (d.toGraph.length_replaceInitial _).symm
      (Fin.natAdd _ (Fin.cast d.length_toGraph.symm i))) (by simp) <| by
    rw [Graph.EarDecomposition.earAt_replaceInitial_natAdd, ← Graph.EarDecomposition.kindAt_eq,
      kindAt_toGraph]; rfl

/-- Replacing the initial stage retains every ear of `d₀` in the prefix positions. -/
@[simp] theorem earAt_replaceInitial_castAdd (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) (i : Fin d₀.length) :
    (d.replaceInitial d₀).earAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.castAdd d.length i)) =
      (d₀.earAt i).copy (d.subgraphAfter_replaceInitial_castLE d₀ i.castSucc).symm :=
  Ear.ext (by rw [Ear.toWalk_copy, ← walkAt_def, ← walkAt_def, walkAt_replaceInitial_castAdd])

/-- Replacing the initial stage shifts every ear of `d` by `d₀.length`. -/
@[simp] theorem earAt_replaceInitial_natAdd (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) (i : Fin d.length) :
    (d.replaceInitial d₀).earAt
      (Fin.cast (d.length_replaceInitial d₀).symm (Fin.natAdd d₀.length i)) =
      (d.earAt i).copy (d.subgraphAfter_replaceInitial_natAdd d₀ i.castSucc).symm :=
  Ear.ext (by rw [Ear.toWalk_copy, ← walkAt_def, ← walkAt_def, walkAt_replaceInitial_natAdd])

@[simp] theorem isOpen_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).IsOpen ↔ d₀.IsOpen ∧ ∀ i, d.kindAt i = .«open» := by
  rw [← isOpen_toGraph, toGraph_replaceInitial, Graph.EarDecomposition.isOpen_replaceInitial,
    Graph.EarDecomposition.isOpen_copy, isOpen_toGraph]
  exact and_congr_right fun _ ↦
    ⟨fun h i ↦ by
      have hi := h (Fin.cast d.length_toGraph.symm i); rw [kindAt_toGraph] at hi; simpa using hi,
     fun h i ↦ by rw [kindAt_toGraph, EarKind.toGraph_eq_open_iff]; exact h _⟩

/-- Normalize any ear decomposition `d : H.EarDecomposition S` to start at a single vertex, turning
an initial cycle into a single-vertex start followed by one closed ear. -/
def toVertexStart (d : H.EarDecomposition S) : H.EarDecomposition S :=
  (H.earDecompositionEquivOfSimpleGraph S).symm d.toGraph.toVertexStart

@[simp] theorem toGraph_toVertexStart (d : H.EarDecomposition S) :
    d.toVertexStart.toGraph = d.toGraph.toVertexStart :=
  (H.earDecompositionEquivOfSimpleGraph S).apply_symm_apply _

@[simp] theorem isVertexStart_toVertexStart (d : H.EarDecomposition S) :
    d.toVertexStart.IsVertexStart := by rw [← isVertexStart_toGraph]; simp

@[simp] theorem not_start_isCycle_toVertexStart (d : H.EarDecomposition S) :
    ¬ d.toVertexStart.start.IsCycle :=
  (isVertexStart_iff_not_start_isCycle _).mp d.isVertexStart_toVertexStart

/-- Normalizing to a vertex start adds one closed ear when `d` starts at a cycle and leaves the
length unchanged otherwise. -/
theorem length_toVertexStart (d : H.EarDecomposition S) :
    d.toVertexStart.length = (if d.start.IsCycle then 1 else 0) + d.length := by
  rw [← length_toGraph, toGraph_toVertexStart]
  simpa only [start_isCycle_toGraph, length_toGraph] using d.toGraph.length_toVertexStart

/-- Normalizing a vertex-started ear decomposition preserves its length. -/
theorem length_toVertexStart_of_isVertexStart {d : H.EarDecomposition S} (h : d.IsVertexStart) :
    d.toVertexStart.length = d.length := by
  simp [d.length_toVertexStart, (d.isVertexStart_iff_not_start_isCycle).mp h]

/-- Normalizing a cycle-started ear decomposition increases its length by one. -/
theorem length_toVertexStart_of_isCycle {d : H.EarDecomposition S} (h : d.start.IsCycle) :
    d.toVertexStart.length = 1 + d.length := by simp [d.length_toVertexStart, h]

/-- Every original stage subgraph of `d` appears at the corresponding shifted index in
`d.toVertexStart`. -/
theorem subgraphAfter_toVertexStart_natAdd (d : H.EarDecomposition S) (i : Fin (d.length + 1)) :
    d.toVertexStart.subgraphAfter
      (Fin.cast ((Nat.add_assoc _ d.length 1).symm.trans
        (congrArg (· + 1) d.length_toVertexStart.symm))
        (Fin.natAdd (if d.start.IsCycle then 1 else 0) i)) = d.subgraphAfter i :=
  subgraphAfter_eq_of_toGraph_copy_eq (hS := rfl)
    (d.toVertexStart.toGraph.copy_rfl.trans d.toGraph_toVertexStart) _
    (Fin.cast ((Nat.add_assoc _ d.toGraph.length 1).symm.trans
      (congrArg (· + 1) d.toGraph.length_toVertexStart.symm))
      (Fin.natAdd _ (Fin.cast (congrArg (· + 1) d.length_toGraph.symm) i))) (by simp) <|
    (d.toGraph.graphAfter_toVertexStart_natAdd _).trans (d.graphAfter_toGraph _)

/-- Every original ear walk of `d` appears at the corresponding shifted index in
`d.toVertexStart`. -/
theorem walkAt_toVertexStart_natAdd (d : H.EarDecomposition S) (i : Fin d.length) :
    d.toVertexStart.walkAt
      (Fin.cast d.length_toVertexStart.symm (Fin.natAdd (if d.start.IsCycle then 1 else 0) i)) =
      d.walkAt i :=
  walkAt_eq_of_toGraph_copy_eq (hS := rfl)
    (d.toVertexStart.toGraph.copy_rfl.trans d.toGraph_toVertexStart) _
    (Fin.cast d.toGraph.length_toVertexStart.symm
      (Fin.natAdd _ (Fin.cast d.length_toGraph.symm i))) (by simp) <| by
    rw [d.toGraph.earAt_toVertexStart_natAdd _, ← Graph.EarDecomposition.walkAt_eq, walkAt_toGraph]
    rfl

/-- Every original ear kind of `d` appears at the corresponding shifted index in
`d.toVertexStart`. -/
theorem kindAt_toVertexStart_natAdd (d : H.EarDecomposition S) (i : Fin d.length) :
    d.toVertexStart.kindAt
      (Fin.cast d.length_toVertexStart.symm (Fin.natAdd (if d.start.IsCycle then 1 else 0) i)) =
      d.kindAt i :=
  kindAt_eq_of_toGraph_copy_eq (hS := rfl)
    (d.toVertexStart.toGraph.copy_rfl.trans d.toGraph_toVertexStart) _
    (Fin.cast d.toGraph.length_toVertexStart.symm
      (Fin.natAdd _ (Fin.cast d.length_toGraph.symm i))) (by simp) <| by
    rw [d.toGraph.earAt_toVertexStart_natAdd _, ← Graph.EarDecomposition.kindAt_eq, kindAt_toGraph]
    rfl

/-- Every original ear of `d` appears at the corresponding shifted index in `d.toVertexStart`. -/
theorem earAt_toVertexStart_natAdd (d : H.EarDecomposition S) (i : Fin d.length) :
    d.toVertexStart.earAt
      (Fin.cast d.length_toVertexStart.symm (Fin.natAdd (if d.start.IsCycle then 1 else 0) i)) =
      (d.earAt i).copy (d.subgraphAfter_toVertexStart_natAdd i.castSucc).symm :=
  Ear.ext (by rw [Ear.toWalk_copy, ← walkAt_def, ← walkAt_def, walkAt_toVertexStart_natAdd])

/-- Normalizing an already vertex-started ear decomposition returns it unchanged. -/
theorem toVertexStart_eq_self {d : H.EarDecomposition S} (h : d.IsVertexStart) :
    d.toVertexStart = d :=
  (H.earDecompositionEquivOfSimpleGraph S).injective <| by
    simpa using Graph.EarDecomposition.toVertexStart_eq_self (d.isVertexStart_toGraph.mpr h)

/-- When `d` starts from a cycle, `d.toVertexStart` starts at the cycle's base vertex and its first
ear is the closed ear formed by that initial cycle. -/
theorem exists_cycle_toVertexStart {d : H.EarDecomposition S} (h : d.start.IsCycle) :
    ∃ (u : α) (c : H.Walk u u) (_ : c.IsCycle),
      d.initial = c.toSubgraph ∧ d.toVertexStart.initial = H.singletonSubgraph u ∧
      d.toVertexStart.walkAt
        (Fin.cast (d.length_toVertexStart_of_isCycle h).symm (Fin.castAdd d.length 0)) =
        ⟨u, u, c⟩ ∧
      d.toVertexStart.kindAt
        (Fin.cast (d.length_toVertexStart_of_isCycle h).symm (Fin.castAdd d.length 0)) =
        .closed := by
  have hc' : d.toGraph.start.IsCycle := d.start_isCycle_toGraph.mpr h
  obtain ⟨u, walk, hwalk, hinit, hinitV, hear⟩ :=
    d.toGraph.exists_cycle_earAt_toVertexStart_zero hc'
  refine ⟨u, walk.toSimpleGraph, walk.isCycle_toSimpleGraph_iff.mpr hwalk,
    Subgraph.toGraph_injective (by
      rw [← initial_toGraph, hinit, Walk.toGraph_toSubgraph, Graph.Walk.toGraph_toSimpleGraph]),
    Subgraph.toGraph_injective (by
      rw [← initial_toGraph, toGraph_toVertexStart, hinitV, Subgraph.toGraph_singletonSubgraph]),
    walkAt_eq_of_toGraph_copy_eq (hS := rfl)
      (d.toVertexStart.toGraph.copy_rfl.trans d.toGraph_toVertexStart) _
      (Fin.cast (d.toGraph.length_toVertexStart_of_isCycle hc').symm (Fin.castAdd _ 0)) rfl
      (by rw [hear, Graph.Ear.toWalk_ofIsCycle, Graph.Walk.toGraph_toSimpleGraph]),
    kindAt_eq_of_toGraph_copy_eq (hS := rfl)
      (d.toVertexStart.toGraph.copy_rfl.trans d.toGraph_toVertexStart) _
      (Fin.cast (d.toGraph.length_toVertexStart_of_isCycle hc').symm (Fin.castAdd _ 0)) rfl
      (by rw [hear, Graph.Ear.kind_ofIsCycle]; rfl)⟩

private theorem toGraph_toVertexStart_cycle {u : α} (c : H.Walk u u) (hc : c.IsCycle) :
    (cycle c hc).toVertexStart.toGraph =
      (Graph.EarDecomposition.cycle c.toGraph
        ((SimpleGraph.Walk.isCycle_toGraph_iff c).mpr hc)).toVertexStart.copy
        c.toGraph_toSubgraph.symm := by
  rw [toGraph_toVertexStart, toGraph_cycle]
  have hcopy : ∀ {K₁ K₂ : Graph α (Sym2 α)} (d : (Graph.ofSimpleGraph H).EarDecomposition K₁)
      (h : K₁ = K₂), (d.copy h).toVertexStart = d.toVertexStart.copy h := by
    rintro K _ d rfl; rw [Graph.EarDecomposition.copy_rfl, Graph.EarDecomposition.copy_rfl]
  exact hcopy _ c.toGraph_toSubgraph.symm

/-- Normalizing a single-cycle decomposition sets its initial subgraph to the cycle's base
vertex. -/
theorem initial_toVertexStart_cycle {u : α} (c : H.Walk u u) (hc : c.IsCycle) :
    (cycle c hc).toVertexStart.initial = H.singletonSubgraph u :=
  Subgraph.toGraph_injective <| by
    rw [← initial_toGraph, toGraph_toVertexStart_cycle, Graph.EarDecomposition.initial_copy,
      Graph.EarDecomposition.initial_toVertexStart_cycle, Subgraph.toGraph_singletonSubgraph]

@[simp] theorem length_toVertexStart_cycle {u : α} (c : H.Walk u u) (hc : c.IsCycle) :
    (cycle c hc).toVertexStart.length = 1 := by simp [length_toVertexStart]

/-- Normalizing a single-cycle decomposition yields `c` as the walk of its unique ear. -/
@[simp] theorem walkAt_toVertexStart_cycle {u : α} (c : H.Walk u u) (hc : c.IsCycle)
    (i : Fin (cycle c hc).toVertexStart.length) :
    (cycle c hc).toVertexStart.walkAt i = ⟨u, u, c⟩ :=
  walkAt_eq_of_toGraph_copy_eq (hS := rfl)
    ((cycle c hc).toVertexStart.toGraph.copy_rfl.trans (toGraph_toVertexStart_cycle c hc)) i
    ⟨i.1, by simp [i.2.trans_eq (length_toVertexStart_cycle c hc)]⟩ rfl <| by
    rw [Graph.EarDecomposition.earAt_copy, Graph.EarDecomposition.earAt_toVertexStart_cycle,
      Graph.Ear.toWalk_ofIsCycle]

/-- Normalizing a single-cycle decomposition yields a closed ear as its unique ear. -/
@[simp] theorem kindAt_toVertexStart_cycle {u : α} (c : H.Walk u u) (hc : c.IsCycle)
    (i : Fin (cycle c hc).toVertexStart.length) :
    (cycle c hc).toVertexStart.kindAt i = .closed :=
  kindAt_eq_of_toGraph_copy_eq (hS := rfl)
    ((cycle c hc).toVertexStart.toGraph.copy_rfl.trans (toGraph_toVertexStart_cycle c hc)) i
    ⟨i.1, by simp [i.2.trans_eq (length_toVertexStart_cycle c hc)]⟩ rfl <| by
    rw [Graph.EarDecomposition.earAt_copy, Graph.EarDecomposition.earAt_toVertexStart_cycle,
      Graph.Ear.kind_ofIsCycle]; rfl

end EarDecomposition

/-- A subgraph of `H` admits an ear decomposition if and only if it admits one starting from a
single vertex. No finiteness assumption is needed. -/
theorem nonempty_earDecomposition_iff_exists_isVertexStart {H : SimpleGraph α} {S : H.Subgraph} :
    Nonempty (H.EarDecomposition S) ↔ ∃ d : H.EarDecomposition S, d.IsVertexStart :=
  ⟨fun ⟨d⟩ ↦ ⟨d.toVertexStart, d.isVertexStart_toVertexStart⟩, fun ⟨d, _⟩ ↦ ⟨d⟩⟩

/-! ### Data-level extension and `[Finite H.edgeSet]` ear characterizations -/

namespace EarDecomposition

variable {H : SimpleGraph α} {S : H.Subgraph} [Finite H.edgeSet]

/-- Complete any partial ear decomposition `d : H.EarDecomposition S` in a `2`-edge-connected simple
graph with finitely many edges to an ear decomposition of `⊤ : H.Subgraph`. No separate `[Finite α]`
instance is required. -/
noncomputable def extend (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S) :
    H.EarDecomposition ⊤ :=
  H.earDecompositionTopEquivOfSimpleGraph.symm
    (d.toGraph.extend ((Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH))

theorem toGraph_extend (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S) :
    (d.extend hH).toGraph.copy Subgraph.toGraph_top =
      d.toGraph.extend ((Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH) := by
  rw [← earDecompositionTopEquivOfSimpleGraph_apply]
  exact H.earDecompositionTopEquivOfSimpleGraph.apply_symm_apply _

theorem length_le_length_extend (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S) :
    d.length ≤ (d.extend hH).length := by
  simpa [← d.toGraph_extend hH] using
    d.toGraph.length_le_length_extend ((Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH)

@[simp] theorem subgraphAfter_extend_castLE (hH : H.IsEdgeConnected 2)
    (d : H.EarDecomposition S) (k : Fin (d.length + 1)) :
    (d.extend hH).subgraphAfter
      (Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hH)) k) = d.subgraphAfter k :=
  subgraphAfter_eq_of_toGraph_copy_eq (d.toGraph_extend hH) _
    (Fin.castLE (Nat.succ_le_succ (d.toGraph.length_le_length_extend _))
      (Fin.cast (congrArg (· + 1) d.length_toGraph.symm) k)) rfl <| by
    rw [d.toGraph.graphAfter_extend_castLE _ _, graphAfter_toGraph]; rfl

@[simp] theorem initial_extend (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S) :
    (d.extend hH).initial = d.initial := by
  simpa only [← subgraphAfter_zero, Fin.castLE_zero] using d.subgraphAfter_extend_castLE hH 0

/-- Extending a partial ear decomposition preserves its initial-stage witness. -/
theorem heq_start_extend (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S) :
    HEq (d.extend hH).start d.start :=
  earStart_heq_of_toGraph_heq ((d.extend hH).subgraphAfter_zero.trans
      ((d.initial_extend hH).trans d.subgraphAfter_zero.symm)) <|
    ((d.extend hH).heq_start_toGraph).symm.trans
      ((((d.extend hH).toGraph.heq_start_copy Subgraph.toGraph_top).symm.trans
        (Graph.EarDecomposition.heq_start_of_eq (d.toGraph_extend hH))).trans
        ((d.toGraph.heq_start_extend _).trans d.heq_start_toGraph))

@[simp] theorem start_isCycle_extend (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S) :
    (d.extend hH).start.IsCycle ↔ d.start.IsCycle := by
  have h := d.toGraph.start_isCycle_extend ((Graph.isEdgeConnected_ofSimpleGraph_iff H 2).mpr hH)
  rwa [← d.toGraph_extend hH, Graph.EarDecomposition.start_isCycle_copy,
    start_isCycle_toGraph, start_isCycle_toGraph] at h

@[simp] theorem isVertexStart_extend (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S) :
    (d.extend hH).IsVertexStart ↔ d.IsVertexStart := by simp [isVertexStart_iff]

@[simp] theorem walkAt_extend_castLE (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S)
    (i : Fin d.length) :
    (d.extend hH).walkAt (Fin.castLE (d.length_le_length_extend hH) i) = d.walkAt i :=
  walkAt_eq_of_toGraph_copy_eq (d.toGraph_extend hH) _
    (Fin.castLE (d.toGraph.length_le_length_extend _) (Fin.cast d.length_toGraph.symm i)) rfl <| by
    rw [d.toGraph.earAt_extend_castLE _ _, ← Graph.EarDecomposition.walkAt_eq, walkAt_toGraph]; rfl

@[simp] theorem kindAt_extend_castLE (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S)
    (i : Fin d.length) :
    (d.extend hH).kindAt (Fin.castLE (d.length_le_length_extend hH) i) = d.kindAt i :=
  kindAt_eq_of_toGraph_copy_eq (d.toGraph_extend hH) _
    (Fin.castLE (d.toGraph.length_le_length_extend _) (Fin.cast d.length_toGraph.symm i)) rfl <| by
    rw [d.toGraph.earAt_extend_castLE _ _, ← Graph.EarDecomposition.kindAt_eq, kindAt_toGraph]; rfl

/-- Completing a partial ear decomposition preserves all of its displayed ears. -/
@[simp] theorem earAt_extend_castLE (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S)
    (i : Fin d.length) :
    (d.extend hH).earAt (Fin.castLE (d.length_le_length_extend hH) i) =
      (d.earAt i).copy (d.subgraphAfter_extend_castLE hH i.castSucc).symm :=
  Ear.ext (by rw [Ear.toWalk_copy, ← walkAt_def, ← walkAt_def, walkAt_extend_castLE])

/-- Taking the prefix of `d.extend hH` of length `d.length` recovers `d`. -/
theorem prefix_extend (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S) :
    ((d.extend hH).prefix
      (Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hH)) (Fin.last d.length))).copy
      ((d.subgraphAfter_extend_castLE hH (Fin.last d.length)).trans d.subgraphAfter_last) = d := by
  let k : Fin ((d.extend hH).length + 1) :=
    Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hH)) (Fin.last d.length)
  let hsub := (d.subgraphAfter_extend_castLE hH (Fin.last d.length)).trans d.subgraphAfter_last
  have hlen : (((d.extend hH).prefix k).copy hsub).length = d.length := by simp [k]
  refine ext hlen (by simp) (by rw [start_copy, start_prefix]; exact d.heq_start_extend hH)
    fun j ↦ ?_
  let j₀ : Fin k := j
  rw [(((d.extend hH).prefix k).walkAt_copy hsub j₀).trans ((d.extend hH).walkAt_prefix k j₀),
    show j₀.castLE k.is_le = Fin.castLE (d.length_le_length_extend hH) (Fin.cast hlen j) from
      Fin.ext rfl,
    walkAt_extend_castLE]

end EarDecomposition

namespace IsEdgeConnected

variable {H : SimpleGraph α} [Finite H.edgeSet]

/-- Construct an ear decomposition of `⊤` in a `2`-edge-connected simple graph with finitely many
edges starting at a prescribed vertex `v`. -/
noncomputable def earDecompositionOfVertex (hH : H.IsEdgeConnected 2) (v : α) :
    H.EarDecomposition ⊤ := (EarDecomposition.vertex H v).extend hH

@[simp] theorem initial_earDecompositionOfVertex (hH : H.IsEdgeConnected 2) (v : α) :
    (hH.earDecompositionOfVertex v).initial = H.singletonSubgraph v := by
  simp [earDecompositionOfVertex]

@[simp] theorem isVertexStart_earDecompositionOfVertex (hH : H.IsEdgeConnected 2) (v : α) :
    (hH.earDecompositionOfVertex v).IsVertexStart := by simp [earDecompositionOfVertex]

@[simp] theorem not_start_isCycle_earDecompositionOfVertex (hH : H.IsEdgeConnected 2) (v : α) :
    ¬ (hH.earDecompositionOfVertex v).start.IsCycle := by
  rw [← EarDecomposition.isVertexStart_iff_not_start_isCycle]; simp

/-- Construct an ear decomposition of `⊤` in a `2`-edge-connected simple graph with finitely many
edges starting at a prescribed cycle `c`. -/
noncomputable def earDecompositionOfCycle (hH : H.IsEdgeConnected 2) {u : α} (c : H.Walk u u)
    (hc : c.IsCycle) : H.EarDecomposition ⊤ := (EarDecomposition.cycle c hc).extend hH

@[simp] theorem initial_earDecompositionOfCycle (hH : H.IsEdgeConnected 2) {u : α} (c : H.Walk u u)
    (hc : c.IsCycle) : (hH.earDecompositionOfCycle c hc).initial = c.toSubgraph := by
  simp [earDecompositionOfCycle]

@[simp] theorem start_isCycle_earDecompositionOfCycle (hH : H.IsEdgeConnected 2) {u : α}
    (c : H.Walk u u) (hc : c.IsCycle) : (hH.earDecompositionOfCycle c hc).start.IsCycle := by
  rw [earDecompositionOfCycle, EarDecomposition.start_isCycle_extend]
  exact (EarDecomposition.isOpen_cycle c hc).start_isCycle

@[simp] theorem not_isVertexStart_earDecompositionOfCycle (hH : H.IsEdgeConnected 2) {u : α}
    (c : H.Walk u u) (hc : c.IsCycle) : ¬ (hH.earDecompositionOfCycle c hc).IsVertexStart := by
  simp [earDecompositionOfCycle]

end IsEdgeConnected

/-- A simple graph with finitely many edges is connected and has no bridge among its actual edges if
and only if `⊤ : H.Subgraph` admits an ear decomposition. No separate `[Nonempty α]` or `[Finite α]`
assumption is needed, since under `[Finite H.edgeSet]` both sides imply `Nonempty α` and
`Finite α`. -/
theorem connected_and_forall_not_isBridge_iff_nonempty_earDecomposition {H : SimpleGraph α}
    [Finite H.edgeSet] :
    (H.Connected ∧ ∀ e ∈ H.edgeSet, ¬ H.IsBridge e) ↔ Nonempty (H.EarDecomposition ⊤) := by
  rw [← H.earDecompositionTopEquivOfSimpleGraph.nonempty_congr.symm,
    ← Graph.connected_and_forall_not_isBridge_iff_nonempty_earDecomposition,
    Graph.connected_ofSimpleGraph_iff]
  exact and_congr_right fun _ ↦
    ⟨fun h e he ↦ by obtain ⟨heH, hb⟩ := Graph.isBridge_ofSimpleGraph_iff.mp he; exact h e heH hb,
     fun h e he hb ↦ h e (Graph.isBridge_ofSimpleGraph_iff.mpr ⟨he, hb⟩)⟩

/-- **Whitney's open ear characterization on `Graph.ofSimpleGraph H`.** A simple graph with finitely
many edges is `2`-vertex-connected if and only if `Graph.ofSimpleGraph H` admits an open ear
decomposition. Neither `[Finite α]` nor `[Nonempty α]` is required. -/
theorem isVertexConnected_two_iff_exists_isOpen_earDecomposition_ofSimpleGraph
    (H : SimpleGraph α) [Finite H.edgeSet] :
    H.IsVertexConnected 2 ↔
      ∃ d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H), d.IsOpen := by
  rw [isVertexConnected_two_iff_exists_isOpen_earDecomposition]
  exact H.earDecompositionTopEquivOfSimpleGraph.exists_congr fun d ↦ by
    rw [earDecompositionTopEquivOfSimpleGraph_apply, Graph.EarDecomposition.isOpen_copy,
      EarDecomposition.isOpen_toGraph]

end SimpleGraph
