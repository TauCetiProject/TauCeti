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
# Ear decompositions of graphs associated to simple graphs

A simple graph `G` has two ear-decomposition interfaces: `SimpleGraph.EarDecomposition`, whose
stages are subgraphs `H : G.Subgraph`, and `Graph.EarDecomposition` for the multigraph
`Graph.ofSimpleGraph G`. On a general multigraph, a closed ear must explicitly avoid edges of its
base graph `K` because a loop at the base vertex can meet `V(K)` only at that vertex while reusing
an edge of `K`. On `Graph.ofSimpleGraph G`, by contrast, every edge has two distinct endpoints
(there are no loops), so every edge of a closed walk meeting `V(K)` only at its base vertex has at
least one endpoint outside `V(K)` and therefore automatically avoids `E(K)`
(`Graph.Walk.edges_notMem_edgeSet_of_le_ofSimpleGraph`).

This file transports ear kinds, individual ears, initial stages, and ear decompositions in both
directions and packages them as equivalences. The direction from `Graph.ofSimpleGraph G` to `G`
drops the redundant `Sym2 V` edge identities via `Graph.toSimpleGraphSubgraph`; the direction from
`G` to `Graph.ofSimpleGraph G` adds them via `SimpleGraph.Subgraph.toGraph`. Both preserve lengths,
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

## Main declarations

* `SimpleGraph.earKindEquivGraph`: equivalence `SimpleGraph.EarKind ≃ Graph.EarKind`.
* `Graph.Ear.closedOfSimpleGraph`: construct a closed ear of `Graph.ofSimpleGraph H` from the cycle
  and vertex-intersection conditions alone, deriving edge disjointness automatically.
* `SimpleGraph.earEquivOfSimpleGraph`: equivalence
  `H.Ear S ≃ (Graph.ofSimpleGraph H).Ear S.toGraph`.
* `SimpleGraph.earStartEquivOfSimpleGraph`: equivalence
  `H.EarStart S ≃ (Graph.ofSimpleGraph H).EarStart S.toGraph`.
* `Graph.EarDecomposition.toSimpleGraph`, `SimpleGraph.EarDecomposition.toGraph`: the two
  transports of ear decompositions.
* `SimpleGraph.earDecompositionEquivOfSimpleGraph`,
  `SimpleGraph.earDecompositionTopEquivOfSimpleGraph`: equivalences between simple-graph and
  multigraph ear decompositions.
* `SimpleGraph.EarDecomposition.replaceInitial`, `SimpleGraph.EarDecomposition.toVertexStart`:
  initial-stage replacement and vertex-start normalization on `SimpleGraph.EarDecomposition`.
* `SimpleGraph.EarDecomposition.extend`, `SimpleGraph.IsEdgeConnected.earDecompositionOfVertex`,
  `SimpleGraph.IsEdgeConnected.earDecompositionOfCycle`: under `[Finite H.edgeSet]`, complete any
  partial ear decomposition of a `2`-edge-connected simple graph to `⊤`.

## Implementation notes

`SimpleGraph.EarDecomposition.toGraph` is reducible and exposed, so the length of a transported
decomposition unfolds to the original length at reducible transparency, and `rw` and `simp` accept
`Fin` indices over either length.

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

theorem toSimpleGraph_kind_toGraph (e : H.Ear S) : e.toGraph.kind.toSimpleGraph = e.kind := by
  simp

@[simp] theorem toWalk_toGraph (e : H.Ear S) :
    e.toGraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, e.toWalk.2.2.toGraph⟩ := by
  cases e with | «open» => rw [toWalk_open]; simp | closed => rw [toWalk_closed]; simp

/-- The graph traced by a transported ear is the graph of the subgraph traced by the ear. -/
@[simp] theorem toGraph_toGraph (e : H.Ear S) :
    Graph.Ear.toGraph e.toGraph = e.toSubgraph.toGraph := by
  cases e <;> simp [SimpleGraph.Walk.toGraph_toSubgraph]

/-- Adjoining a transported ear gives the graph of the subgraph obtained by adjoining the ear. -/
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

private theorem heq_of_toWalk_eq {L : Graph V (Sym2 V)} (hL : L = K)
    (f : (Graph.ofSimpleGraph G).Ear L) (e : (Graph.ofSimpleGraph G).Ear K)
    (h : f.toWalk = e.toWalk) : f ≍ e := by
  subst hL
  exact heq_of_eq (Ear.ext _ _ h)

/-- Converting a multigraph ear over `K ≤ Graph.ofSimpleGraph G` to `SimpleGraph` and back recovers
it heterogeneously. -/
theorem heq_toGraph_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    e.toSimpleGraph.toGraph ≍ e :=
  heq_of_toWalk_eq (K.toGraph_toSimpleGraphSubgraph e.base_le) _ _ <| by
    rw [SimpleGraph.Ear.toWalk_toGraph, toWalk_toSimpleGraph]
    dsimp only
    rw [Walk.toGraph_toSimpleGraph]

/-- Converting a multigraph ear over `K ≤ Graph.ofSimpleGraph G` to `SimpleGraph` and back recovers
the original ear. -/
@[simp] theorem toGraph_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K) :
    (K.toGraph_toSimpleGraphSubgraph e.base_le) ▸ e.toSimpleGraph.toGraph = e :=
  eq_of_heq ((eqRec_heq _ _).trans e.heq_toGraph_toSimpleGraph)

private theorem heq_toGraph_copy_toSimpleGraph (e : (Graph.ofSimpleGraph G).Ear K)
    {H : G.Subgraph} (h : K.toSimpleGraphSubgraph e.base_le = H) :
    (e.toSimpleGraph.copy h).toGraph ≍ e := by
  subst h
  rw [SimpleGraph.Ear.copy_rfl]
  exact e.heq_toGraph_toSimpleGraph

end Graph.Ear

namespace SimpleGraph

variable {α : Type u}

/-- Converting a simple-graph ear to `Graph.ofSimpleGraph H` and back recovers the original ear. -/
@[simp] theorem Ear.toSimpleGraph_toGraph {H : SimpleGraph α} {S : H.Subgraph} (e : H.Ear S) :
    e.toGraph.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph e.toGraph.base_le) = e :=
  SimpleGraph.Ear.ext <| by
    rw [SimpleGraph.Ear.toWalk_copy, Graph.Ear.toWalk_toSimpleGraph, SimpleGraph.Ear.toWalk_toGraph]
    dsimp only
    rw [Walk.toSimpleGraph_toGraph]

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
def toGraph : {S : H.Subgraph} → H.EarStart S → (Graph.ofSimpleGraph H).EarStart S.toGraph
  | _, .vertex v =>
      (Subgraph.toGraph_singletonSubgraph (G := H) v).symm ▸ .vertex ⟨v, mem_univ v⟩
  | _, .cycle c hc =>
      c.toGraph_toSubgraph.symm ▸ .cycle c.toGraph ((SimpleGraph.Walk.isCycle_toGraph_iff c).mpr hc)

theorem heq_toGraph_vertex (v : α) :
    HEq (EarStart.vertex (G := H) v).toGraph
      (Graph.EarStart.vertex (G := Graph.ofSimpleGraph H) ⟨v, mem_univ v⟩) := by
  unfold toGraph; exact eqRec_heq _ _

theorem heq_toGraph_cycle {u : α} (c : H.Walk u u) (hc : c.IsCycle) :
    HEq (EarStart.cycle c hc).toGraph
      (Graph.EarStart.cycle c.toGraph ((SimpleGraph.Walk.isCycle_toGraph_iff c).mpr hc)) := by
  unfold toGraph; exact eqRec_heq _ _

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
  | .vertex v => (Graph.toSimpleGraphSubgraph_noEdge_singleton v.val
      (Graph.EarStart.vertex v).le).symm ▸ .vertex v.val
  | .cycle p hp => (Graph.Walk.toSimpleGraphSubgraph_walkGraph p
      (Graph.EarStart.cycle p hp).le).symm ▸
        .cycle p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)

/-- Transporting a vertex initial stage selects the corresponding simple-graph vertex stage. -/
theorem heq_toSimpleGraph_vertex (v : V(Graph.ofSimpleGraph G)) :
    HEq (Graph.EarStart.vertex v).toSimpleGraph (SimpleGraph.EarStart.vertex (G := G) v.val) := by
  unfold toSimpleGraph; exact eqRec_heq _ _

/-- Transporting a cycle initial stage selects the corresponding simple-graph cycle stage. -/
theorem heq_toSimpleGraph_cycle {x : V} (p : (Graph.ofSimpleGraph G).Walk x x) (hp : p.IsCycle) :
    HEq (Graph.EarStart.cycle p hp).toSimpleGraph
      (SimpleGraph.EarStart.cycle p.toSimpleGraph (p.isCycle_toSimpleGraph_iff.mpr hp)) := by
  unfold toSimpleGraph; exact eqRec_heq _ _

@[simp] theorem isCycle_toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    s.toSimpleGraph.IsCycle ↔ s.IsCycle := by
  cases s <;> exact (SimpleGraph.EarStart.isCycle_eqRec _ _).trans (by simp)

/-- Heterogeneously equal initial stages over equal multigraphs transport to heterogeneously equal
simple-graph initial stages. -/
theorem toSimpleGraph_heq_of_heq {K₁ K₂ : Graph V (Sym2 V)}
    {s₁ : (Graph.ofSimpleGraph G).EarStart K₁} {s₂ : (Graph.ofSimpleGraph G).EarStart K₂}
    (hK : K₁ = K₂) (hs : s₁ ≍ s₂) : s₁.toSimpleGraph ≍ s₂.toSimpleGraph := by
  subst hK
  cases eq_of_heq hs
  rfl

private theorem toGraph_heq_of_heq {S₁ S₂ : G.Subgraph}
    {s₁ : G.EarStart S₁} {s₂ : G.EarStart S₂}
    (hS : S₁ = S₂) (hs : s₁ ≍ s₂) : s₁.toGraph ≍ s₂.toGraph := by
  subst hS
  cases eq_of_heq hs
  rfl

/-- Converting a multigraph initial witness in `Graph.ofSimpleGraph G` to `SimpleGraph` and back
recovers it heterogeneously. -/
theorem heq_toGraph_toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    s.toSimpleGraph.toGraph ≍ s := by
  cases s with
  | vertex v =>
      rcases v with ⟨v, hv⟩
      exact (toGraph_heq_of_heq (Graph.toSimpleGraphSubgraph_noEdge_singleton v _)
        (heq_toSimpleGraph_vertex ⟨v, hv⟩)).trans (SimpleGraph.EarStart.heq_toGraph_vertex v)
  | cycle walk isCycle =>
      exact (toGraph_heq_of_heq (walk.toSimpleGraphSubgraph_walkGraph _)
        (heq_toSimpleGraph_cycle walk isCycle)).trans
        ((SimpleGraph.EarStart.heq_toGraph_cycle _ _).trans
          (Graph.EarStart.heq_cycle_of_eq _ _ (Graph.Walk.toGraph_toSimpleGraph walk)))

/-- Converting a multigraph initial witness in `Graph.ofSimpleGraph G` to `SimpleGraph` and back
recovers it. -/
@[simp] theorem toGraph_toSimpleGraph (s : (Graph.ofSimpleGraph G).EarStart K) :
    (K.toGraph_toSimpleGraphSubgraph s.le) ▸ s.toSimpleGraph.toGraph = s :=
  eq_of_heq ((eqRec_heq _ _).trans s.heq_toGraph_toSimpleGraph)

end Graph.EarStart

namespace SimpleGraph

variable {α : Type u}

/-- Converting a simple-graph initial witness to `Graph.ofSimpleGraph H` and back recovers it
heterogeneously. -/
theorem EarStart.heq_toSimpleGraph_toGraph {H : SimpleGraph α}
    {S : H.Subgraph} (s : H.EarStart S) : HEq s.toGraph.toSimpleGraph s := by
  cases s with
  | vertex v =>
      exact (Graph.EarStart.toSimpleGraph_heq_of_heq (Subgraph.toGraph_singletonSubgraph v)
        (EarStart.heq_toGraph_vertex v)).trans (Graph.EarStart.heq_toSimpleGraph_vertex _)
  | cycle c hc =>
      exact (Graph.EarStart.toSimpleGraph_heq_of_heq c.toGraph_toSubgraph
        (EarStart.heq_toGraph_cycle c hc)).trans
        ((Graph.EarStart.heq_toSimpleGraph_cycle _ _).trans
          (EarStart.heq_cycle_of_eq _ _ (SimpleGraph.Walk.toSimpleGraph_toGraph c)))

/-- Converting a simple-graph initial witness to `Graph.ofSimpleGraph H` and back recovers it. -/
@[simp] theorem EarStart.toSimpleGraph_toGraph {H : SimpleGraph α}
    {S : H.Subgraph} (s : H.EarStart S) :
    (S.toSimpleGraphSubgraph_toGraph s.toGraph.le) ▸ s.toGraph.toSimpleGraph = s :=
  eq_of_heq ((eqRec_heq _ _).trans s.heq_toSimpleGraph_toGraph)

/-- Initial witnesses `H.EarStart S` correspond bijectively to multigraph initial witnesses
`(Graph.ofSimpleGraph H).EarStart S.toGraph`. -/
def earStartEquivOfSimpleGraph (H : SimpleGraph α) (S : H.Subgraph) :
    H.EarStart S ≃ (Graph.ofSimpleGraph H).EarStart S.toGraph where
  toFun s := s.toGraph
  invFun s := (S.toSimpleGraphSubgraph_toGraph s.le) ▸ s.toSimpleGraph
  left_inv := EarStart.toSimpleGraph_toGraph
  right_inv s := eq_of_heq ((Graph.EarStart.toGraph_heq_of_heq
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
`S.toGraph` in `Graph.ofSimpleGraph H`, retaining every prefix and displayed ear. -/
@[expose, reducible]
def toGraph (d : H.EarDecomposition S) : (Graph.ofSimpleGraph H).EarDecomposition S.toGraph where
  length := d.length
  graphAfter k := (d.subgraphAfter k).toGraph
  start := d.start.toGraph
  earAt i := ⟨_, (d.earAt i).toGraph⟩
  earAt_fst _ := rfl
  graphAfter_succ i := by rw [d.subgraphAfter_succ, Ear.add_toGraph]
  graphAfter_last := by rw [d.subgraphAfter_last]

@[simp] theorem length_toGraph (d : H.EarDecomposition S) : d.toGraph.length = d.length := rfl

@[simp] theorem graphAfter_toGraph (d : H.EarDecomposition S) (k : Fin (d.length + 1)) :
    d.toGraph.graphAfter k = (d.subgraphAfter k).toGraph := rfl

theorem initial_toGraph (d : H.EarDecomposition S) : d.toGraph.initial = d.initial.toGraph := by
  rw [Graph.EarDecomposition.initial_eq_graphAfter, ← subgraphAfter_zero]

theorem start_toGraph (d : H.EarDecomposition S) : d.toGraph.start = d.start.toGraph := rfl

theorem start_isCycle_toGraph (d : H.EarDecomposition S) :
    d.toGraph.start.IsCycle ↔ d.start.IsCycle :=
  d.start.isCycle_toGraph

/-- A transported decomposition starts from a single vertex exactly when the original one does. -/
@[simp] theorem isVertexStart_toGraph (d : H.EarDecomposition S) :
    d.toGraph.IsVertexStart ↔ d.IsVertexStart := by
  rw [Graph.EarDecomposition.isVertexStart_iff_not_start_isCycle,
    isVertexStart_iff_not_start_isCycle, start_isCycle_toGraph]

theorem earAt_toGraph (d : H.EarDecomposition S) (i : Fin d.length) :
    d.toGraph.earAt i = ⟨(d.subgraphAfter i.castSucc).toGraph, (d.earAt i).toGraph⟩ := rfl

theorem kindAt_toGraph (d : H.EarDecomposition S) (i : Fin d.length) :
    d.toGraph.kindAt i = (d.kindAt i).toGraph := by
  rw [Graph.EarDecomposition.kindAt_eq, earAt_toGraph, Ear.kind_toGraph, ← kindAt_def]

theorem toSimpleGraph_kindAt_toGraph (d : H.EarDecomposition S) (i : Fin d.length) :
    (d.toGraph.kindAt i).toSimpleGraph = d.kindAt i := by
  rw [kindAt_toGraph, EarKind.toSimpleGraph_toGraph]

theorem walkAt_toGraph (d : H.EarDecomposition S) (i : Fin d.length) :
    d.toGraph.walkAt i = ⟨(d.walkAt i).1, (d.walkAt i).2.1, (d.walkAt i).2.2.toGraph⟩ := by
  rw [walkAt_def]
  exact (Graph.EarDecomposition.walkAt_eq _ _).trans (d.earAt i).toWalk_toGraph

@[simp] theorem isOpen_toGraph (d : H.EarDecomposition S) : d.toGraph.IsOpen ↔ d.IsOpen := by
  rw [Graph.EarDecomposition.isOpen_iff, isOpen_iff]
  refine and_congr d.start.isCycle_toGraph (forall_congr' fun i ↦ ?_)
  rw [kindAt_toGraph, EarKind.toGraph_eq_open_iff]

/-- Transporting a prefix of an ear decomposition gives the corresponding prefix of the
transported decomposition. -/
theorem toGraph_prefix (d : H.EarDecomposition S) (k : Fin (d.length + 1)) :
    (d.prefix k).toGraph = d.toGraph.prefix k := by
  have hlen := d.toGraph.length_prefix k
  refine Graph.EarDecomposition.ext _ _ hlen.symm (d.toGraph.heq_start_prefix k).symm
    (Function.hfunext (congrArg Fin hlen.symm) fun j j' hj ↦ ?_)
  obtain rfl : j' = Fin.cast hlen.symm j := Fin.ext ((Fin.heq_ext_iff hlen.symm).mp hj).symm
  exact heq_of_eq (d.toGraph.earAt_prefix k j).symm

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
      (SimpleGraph.EarDecomposition.vertex G v.val).copy
        (Graph.toSimpleGraphSubgraph_noEdge_singleton v.val (vertex v).final_le).symm :=
  SimpleGraph.EarDecomposition.ext (by simp) (SimpleGraph.Subgraph.toGraph_injective <| by
    rw [toGraph_initial_toSimpleGraph, initial_vertex, SimpleGraph.EarDecomposition.initial_copy,
      SimpleGraph.EarDecomposition.initial_vertex, SimpleGraph.Subgraph.toGraph_singletonSubgraph])
    (by
      rw [start_toSimpleGraph, SimpleGraph.EarDecomposition.start_copy,
        SimpleGraph.EarDecomposition.start_vertex]
      exact (Graph.EarStart.toSimpleGraph_heq_of_heq (graphAfter_vertex_zero v)
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
      exact (Graph.EarStart.toSimpleGraph_heq_of_heq (graphAfter_cycle_zero p hp)
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
    exact (Graph.EarStart.toSimpleGraph_heq_of_heq (d.graphAfter_snoc_zero e)
      (d.heq_start_snoc e)).trans (eqRec_heq _ _).symm
  · let i₀ : Fin (d.snoc e).length := i
    let m : Fin (d.toSimpleGraph.snoc e.toSimpleGraph).length := Fin.cast hlen i
    refine ((walkAt_toSimpleGraph (d.snoc e) i₀).trans ?_).trans
      (SimpleGraph.EarDecomposition.walkAt_copy _ _ m).symm
    by_cases hi : i.val = d.length
    · have hm : m = Fin.last d.toSimpleGraph.length := Fin.ext hi
      have hi' : i₀ = Fin.cast (d.length_snoc e).symm (Fin.last d.length) := Fin.ext hi
      rw [hm, SimpleGraph.EarDecomposition.walkAt_snoc_last, Graph.Ear.toWalk_toSimpleGraph, hi',
        walkAt_eq, earAt_snoc_last]
    · let j : Fin d.length := ⟨i.val, by have := i.isLt; simp at this; omega⟩
      let j' : Fin d.toSimpleGraph.length := j
      have hm : m = j'.castSucc := Fin.ext rfl
      have hi' : i₀ = Fin.cast (d.length_snoc e).symm j.castSucc := Fin.ext rfl
      rw [hm, SimpleGraph.EarDecomposition.walkAt_snoc_castSucc]
      exact (by rw [hi', walkAt_eq, earAt_snoc_castSucc, ← walkAt_eq] : _ = _).trans
        (d.walkAt_toSimpleGraph j).symm

/-- Transporting a prefix of a decomposition of a subgraph of `Graph.ofSimpleGraph G` gives the
corresponding prefix of the transported decomposition. -/
theorem toSimpleGraph_prefix (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (k : Fin (d.length + 1)) : (d.prefix k).toSimpleGraph = d.toSimpleGraph.prefix k := by
  have hlen := d.length_prefix k
  have hzero : (d.prefix k).graphAfter 0 = d.graphAfter 0 := by
    simpa only [initial_eq_graphAfter] using d.initial_prefix k
  refine SimpleGraph.EarDecomposition.ext hlen ?_ ?_ fun i ↦ ?_
  · exact (initial_toSimpleGraph _).trans ((Graph.toSimpleGraphSubgraph_congr hzero _ _).trans
      ((initial_toSimpleGraph d).symm.trans
        (SimpleGraph.EarDecomposition.initial_prefix d.toSimpleGraph k).symm))
  · exact Graph.EarStart.toSimpleGraph_heq_of_heq hzero (d.heq_start_prefix k)
  · refine (walkAt_toSimpleGraph _ i).trans (Eq.trans ?_
      ((SimpleGraph.EarDecomposition.walkAt_prefix _ k _).trans (walkAt_toSimpleGraph d _)).symm)
    exact congrArg (fun w : Σ u v, (Graph.ofSimpleGraph G).Walk u v ↦
      (⟨w.1, w.2.1, w.2.2.toSimpleGraph⟩ : Σ u v, G.Walk u v)) (d.walkAt_prefix k (i.cast hlen))

/-- Transporting a decomposition of a subgraph of `Graph.ofSimpleGraph G` to `G` and back
recovers it, after both target graphs are reindexed along the identification of `H` with `K`. -/
@[simp] theorem toGraph_copy_toSimpleGraph {H : G.Subgraph}
    (d : (Graph.ofSimpleGraph G).EarDecomposition K)
    (hH : K.toSimpleGraphSubgraph d.final_le = H) (hK : H.toGraph = K) :
    (d.toSimpleGraph.copy hH).toGraph.copy hK = d := by
  subst hK
  rw [copy_rfl]
  refine Graph.EarDecomposition.ext _ _ rfl
    d.start.heq_toGraph_toSimpleGraph
    (heq_of_eq (funext fun i ↦ Sigma.ext ?_ ?_))
  · exact (Graph.toGraph_toSimpleGraphSubgraph _ _).trans (d.earAt_fst i).symm
  · exact Graph.Ear.heq_toGraph_copy_toSimpleGraph _ _

/-- Converting a multigraph ear decomposition in `Graph.ofSimpleGraph G` to `SimpleGraph` and back
recovers the original ear decomposition. -/
@[simp] theorem toGraph_toSimpleGraph (d : (Graph.ofSimpleGraph G).EarDecomposition K) :
    d.toSimpleGraph.toGraph.copy (K.toGraph_toSimpleGraphSubgraph d.final_le) = d :=
  d.toGraph_copy_toSimpleGraph rfl (K.toGraph_toSimpleGraphSubgraph d.final_le)

end OfSimpleGraph

end Graph.EarDecomposition

namespace SimpleGraph

variable {α : Type u}

private theorem sigma_toSimpleGraph_eq {H : SimpleGraph α}
    {w : Σ u v, (Graph.ofSimpleGraph H).Walk u v} {w' : Σ u v, H.Walk u v}
    (h : w = ⟨w'.1, w'.2.1, w'.2.2.toGraph⟩) :
    (⟨w.1, w.2.1, w.2.2.toSimpleGraph⟩ : Σ u v, H.Walk u v) = w' := by
  subst h
  dsimp only
  rw [Walk.toSimpleGraph_toGraph]

/-- `toGraph` commutes with `copy`. -/
theorem EarDecomposition.toGraph_copy {H : SimpleGraph α} {S S' : H.Subgraph}
    (d : H.EarDecomposition S) (h : S = S') :
    (d.copy h).toGraph = d.toGraph.copy (congrArg Subgraph.toGraph h) := by
  subst h; exact (Graph.EarDecomposition.copy_rfl _).symm

/-- Transporting a decomposition to `Graph.ofSimpleGraph H` and back recovers it, after both
target graphs are reindexed along the identification of `S` with `K`. -/
@[simp] theorem EarDecomposition.toSimpleGraph_copy_toGraph {H : SimpleGraph α} {S : H.Subgraph}
    {K : Graph α (Sym2 α)} (d : H.EarDecomposition S) (hK : S.toGraph = K)
    (hS : K.toSimpleGraphSubgraph (d.toGraph.copy hK).final_le = S) :
    (d.toGraph.copy hK).toSimpleGraph.copy hS = d := by
  subst hK
  generalize hx : d.toGraph.copy rfl = x at hS ⊢
  rw [Graph.EarDecomposition.copy_rfl] at hx
  subst hx
  refine SimpleGraph.EarDecomposition.ext rfl ?_ ?_ fun i ↦ ?_
  · rw [initial_copy, Graph.EarDecomposition.initial_toSimpleGraph]
    exact (Subgraph.toSimpleGraphSubgraph_toGraph _ _).trans (subgraphAfter_zero d)
  · rw [start_copy, Graph.EarDecomposition.start_toSimpleGraph]
    exact d.start.heq_toSimpleGraph_toGraph
  · refine (walkAt_copy _ _ _).trans ((Graph.EarDecomposition.walkAt_toSimpleGraph _ _).trans ?_)
    exact sigma_toSimpleGraph_eq (d.walkAt_toGraph i)

/-- Converting a simple-graph ear decomposition to `Graph.ofSimpleGraph H` and back recovers the
original ear decomposition. -/
@[simp] theorem EarDecomposition.toSimpleGraph_toGraph {H : SimpleGraph α} {S : H.Subgraph}
    (d : H.EarDecomposition S) :
    d.toGraph.toSimpleGraph.copy (S.toSimpleGraphSubgraph_toGraph d.toGraph.final_le) = d := by
  have h := d.toSimpleGraph_copy_toGraph rfl (S.toSimpleGraphSubgraph_toGraph _)
  generalize hx : d.toGraph.copy rfl = x at h
  rw [Graph.EarDecomposition.copy_rfl] at hx
  subst hx
  exact h

/-- Ear decompositions of a subgraph `S` of a simple graph `H` correspond to ear decompositions of
an equal target graph in `Graph.ofSimpleGraph H`. -/
def earDecompositionEquivOfSimpleGraph {H : SimpleGraph α} {S : H.Subgraph}
    {K : Graph α (Sym2 α)} (h : S.toGraph = K) :
    H.EarDecomposition S ≃ (Graph.ofSimpleGraph H).EarDecomposition K where
  toFun d := d.toGraph.copy h
  invFun d := d.toSimpleGraph.copy <|
    (Graph.toSimpleGraphSubgraph_congr h.symm _ S.toGraph_le_ofSimpleGraph).trans
      (S.toSimpleGraphSubgraph_toGraph _)
  left_inv d := d.toSimpleGraph_copy_toGraph h _
  right_inv d := d.toGraph_copy_toSimpleGraph _ h

@[simp] theorem earDecompositionEquivOfSimpleGraph_apply {H : SimpleGraph α} {S : H.Subgraph}
    {K : Graph α (Sym2 α)} (h : S.toGraph = K) (d : H.EarDecomposition S) :
    earDecompositionEquivOfSimpleGraph h d = d.toGraph.copy h := (rfl)

@[simp] theorem earDecompositionEquivOfSimpleGraph_symm_apply {H : SimpleGraph α}
    {S : H.Subgraph} {K : Graph α (Sym2 α)} (h : S.toGraph = K)
    (d : (Graph.ofSimpleGraph H).EarDecomposition K) :
    (earDecompositionEquivOfSimpleGraph h).symm d = d.toSimpleGraph.copy
      ((Graph.toSimpleGraphSubgraph_congr h.symm _ S.toGraph_le_ofSimpleGraph).trans
        (S.toSimpleGraphSubgraph_toGraph _)) := (rfl)

/-- Ear decompositions of `⊤ : H.Subgraph` in `H` correspond bijectively to multigraph ear
decompositions of `Graph.ofSimpleGraph H`. -/
def earDecompositionTopEquivOfSimpleGraph (H : SimpleGraph α) :
    H.EarDecomposition ⊤ ≃ (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H) :=
  earDecompositionEquivOfSimpleGraph Subgraph.toGraph_top

@[simp] theorem earDecompositionTopEquivOfSimpleGraph_apply (H : SimpleGraph α)
    (d : H.EarDecomposition ⊤) :
    H.earDecompositionTopEquivOfSimpleGraph d = d.toGraph.copy Subgraph.toGraph_top := (rfl)

@[simp] theorem earDecompositionTopEquivOfSimpleGraph_symm_apply (H : SimpleGraph α)
    (d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)) :
    H.earDecompositionTopEquivOfSimpleGraph.symm d = d.toSimpleGraph.copy
      ((Graph.toSimpleGraphSubgraph_congr Subgraph.toGraph_top.symm _
        (⊤ : H.Subgraph).toGraph_le_ofSimpleGraph).trans
          ((⊤ : H.Subgraph).toSimpleGraphSubgraph_toGraph _)) := (rfl)

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
    ((Graph.EarStart.toSimpleGraph_heq_of_heq (congrArg Subgraph.toGraph hS) hs).trans
      s₂.heq_toSimpleGraph_toGraph)

/-- Converting `EarDecomposition.vertex` to `Graph.ofSimpleGraph H` yields
`Graph.EarDecomposition.vertex`, reindexed along `toGraph_singletonSubgraph`. -/
theorem toGraph_vertex (v : α) :
    (vertex H v).toGraph =
      (Graph.EarDecomposition.vertex (G := Graph.ofSimpleGraph H) ⟨v, mem_univ v⟩).copy
        (Subgraph.toGraph_singletonSubgraph (G := H) v).symm := by
  refine Graph.EarDecomposition.ext_of_length_eq_zero (by simp) (by simp) ?_
  rw [start_toGraph, start_vertex]
  exact (Graph.EarStart.toGraph_heq_of_heq (subgraphAfter_vertex v 0) (eqRec_heq _ _)).trans
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
  refine Graph.EarDecomposition.ext_of_length_eq_zero (by simp) (by simp) ?_
  rw [start_toGraph, start_cycle]
  exact (Graph.EarStart.toGraph_heq_of_heq (subgraphAfter_cycle c hc 0) (eqRec_heq _ _)).trans
    ((EarStart.heq_toGraph_cycle c hc).trans
      ((Graph.EarDecomposition.heq_start_cycle _ _).symm.trans
        (Graph.EarDecomposition.heq_start_copy _ _).symm))

/-- `toGraph` commutes with `snoc`. -/
theorem toGraph_snoc (d : H.EarDecomposition S) (e : H.Ear S) :
    (d.snoc e).toGraph = (d.toGraph.snoc e.toGraph).copy e.add_toGraph := by
  have hlen : (d.snoc e).toGraph.length =
      ((d.toGraph.snoc e.toGraph).copy e.add_toGraph).length := by simp
  refine Graph.EarDecomposition.ext _ _ hlen ?_
    (Function.hfunext (congrArg Fin hlen) fun i m him ↦ ?_)
  · rw [start_toGraph, start_snoc]
    exact (Graph.EarStart.toGraph_heq_of_heq (by simp) (eqRec_heq _ _)).trans
      ((d.toGraph.heq_start_snoc e.toGraph).symm.trans
        (Graph.EarDecomposition.heq_start_copy _ _).symm)
  · obtain rfl : m = Fin.cast hlen i := Fin.ext ((Fin.heq_ext_iff hlen).mp him).symm
    refine heq_of_eq ?_
    rw [Graph.EarDecomposition.earAt_copy, Fin.cast_cast]
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · refine Eq.trans ?_ (Graph.EarDecomposition.earAt_snoc_last d.toGraph e.toGraph).symm
      refine Graph.Ear.sigma_ext
        (congrArg Subgraph.toGraph
          ((d.subgraphAfter_snoc_castSucc e (Fin.last d.length)).trans d.subgraphAfter_last)) ?_
      exact ((d.snoc e).toGraph.walkAt_eq (Fin.last d.length)).symm.trans
        (((d.snoc e).walkAt_toGraph (Fin.last d.length)).trans
          (by rw [walkAt_snoc_last, Ear.toWalk_toGraph]))
    · refine Eq.trans ?_
        ((Graph.EarDecomposition.earAt_snoc_castSucc d.toGraph e.toGraph j).trans
          (d.earAt_toGraph j)).symm
      refine Graph.Ear.sigma_ext
        (congrArg Subgraph.toGraph (d.subgraphAfter_snoc_castSucc e j.castSucc)) ?_
      exact ((d.snoc e).toGraph.walkAt_eq j.castSucc).symm.trans
        (((d.snoc e).walkAt_toGraph j.castSucc).trans
          (by rw [walkAt_snoc_castSucc, walkAt_def, Ear.toWalk_toGraph]))

/-! ### Initial-stage replacement and vertex-start normalization via transport -/

private theorem subgraphAfter_eq_of_toGraph_copy_eq {K : Graph α (Sym2 α)} {hS : S.toGraph = K}
    {d : H.EarDecomposition S} {d' : (Graph.ofSimpleGraph H).EarDecomposition K}
    (h : d.toGraph.copy hS = d') (i : Fin (d.length + 1)) (j : Fin (d'.length + 1))
    (hij : i.val = j.val) {T : H.Subgraph} (hT : d'.graphAfter j = T.toGraph) :
    d.subgraphAfter i = T := by
  apply Subgraph.toGraph_injective
  have heq := Graph.EarDecomposition.graphAfter_eq_of_eq h i.val (by simpa using i.isLt)
      (hij ▸ j.isLt)
  rw [Graph.EarDecomposition.graphAfter_copy, graphAfter_toGraph] at heq
  exact (congrArg (fun x ↦ (d.subgraphAfter x).toGraph) (Fin.ext rfl)).trans
    (heq.trans ((congrArg d'.graphAfter (Fin.ext hij)).trans hT))

private theorem walkAt_eq_of_toGraph_copy_eq {K : Graph α (Sym2 α)} {hS : S.toGraph = K}
    {d : H.EarDecomposition S} {d' : (Graph.ofSimpleGraph H).EarDecomposition K}
    (h : d.toGraph.copy hS = d') (i : Fin d.length) (j : Fin d'.length) (hij : i.val = j.val)
    {w : Σ u v : α, H.Walk u v}
    (hw : (d'.earAt j).2.toWalk = ⟨w.1, w.2.1, w.2.2.toGraph⟩) :
    d.walkAt i = w := by
  apply sigma_walk_toGraph_injective
  have heq := congrArg (fun p : Σ L, (Graph.ofSimpleGraph H).Ear L ↦ p.2.toWalk)
    ((Graph.EarDecomposition.earAt_eq_of_eq h i.val (by simp) (hij ▸ j.isLt)).trans
      (congrArg d'.earAt (Fin.ext hij)))
  rw [Graph.EarDecomposition.earAt_copy, ← Graph.EarDecomposition.walkAt_eq, walkAt_toGraph] at heq
  exact (congrArg (fun x ↦ (⟨(d.walkAt x).1, (d.walkAt x).2.1, (d.walkAt x).2.2.toGraph⟩ :
    Σ u v : α, (Graph.ofSimpleGraph H).Walk u v)) (Fin.ext rfl)).trans (heq.trans hw)

private theorem kindAt_eq_of_toGraph_copy_eq {K : Graph α (Sym2 α)} {hS : S.toGraph = K}
    {d : H.EarDecomposition S} {d' : (Graph.ofSimpleGraph H).EarDecomposition K}
    (h : d.toGraph.copy hS = d') (i : Fin d.length) (j : Fin d'.length) (hij : i.val = j.val)
    {k : EarKind} (hk : (d'.earAt j).2.kind = k.toGraph) :
    d.kindAt i = k := by
  apply EarKind.toGraph_injective
  have heq := congrArg (fun p : Σ L, (Graph.ofSimpleGraph H).Ear L ↦ p.2.kind)
    ((Graph.EarDecomposition.earAt_eq_of_eq h i.val (by simp) (hij ▸ j.isLt)).trans
      (congrArg d'.earAt (Fin.ext hij)))
  rw [Graph.EarDecomposition.earAt_copy, ← Graph.EarDecomposition.kindAt_eq, kindAt_toGraph] at heq
  exact (congrArg (fun x ↦ (d.kindAt x).toGraph) (Fin.ext rfl)).trans (heq.trans hk)

/-- Replay the displayed ears of `d : H.EarDecomposition S` on top of an ear decomposition
`d₀ : H.EarDecomposition d.initial` of its initial subgraph. -/
def replaceInitial (d : H.EarDecomposition S) (d₀ : H.EarDecomposition d.initial) :
    H.EarDecomposition S :=
  (earDecompositionEquivOfSimpleGraph (rfl : S.toGraph = S.toGraph)).symm
    (d.toGraph.replaceInitial (d₀.toGraph.copy d.initial_toGraph.symm))

@[simp] theorem toGraph_replaceInitial (d : H.EarDecomposition S)
    (d₀ : H.EarDecomposition d.initial) :
    (d.replaceInitial d₀).toGraph =
      d.toGraph.replaceInitial (d₀.toGraph.copy d.initial_toGraph.symm) := by
  rw [replaceInitial]
  simpa only [earDecompositionEquivOfSimpleGraph_apply, Graph.EarDecomposition.copy_rfl] using
    (earDecompositionEquivOfSimpleGraph (rfl : S.toGraph = S.toGraph)).apply_symm_apply
      (d.toGraph.replaceInitial (d₀.toGraph.copy d.initial_toGraph.symm))

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
    (Graph.EarDecomposition.heq_start_of_eq (d.toGraph_replaceInitial d₀)).trans
      ((d.toGraph.heq_start_replaceInitial _).trans (Graph.EarDecomposition.heq_start_copy _ _))

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
      (Fin.natAdd _ i)) (by simp) <| by
    rw [Graph.EarDecomposition.graphAfter_replaceInitial_natAdd, graphAfter_toGraph]

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
      (Fin.natAdd _ i)) (by simp) <| by
    rw [Graph.EarDecomposition.earAt_replaceInitial_natAdd, ← Graph.EarDecomposition.walkAt_eq,
      walkAt_toGraph]

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
      (Fin.natAdd _ i)) (by simp) <| by
    rw [Graph.EarDecomposition.earAt_replaceInitial_natAdd, ← Graph.EarDecomposition.kindAt_eq,
      kindAt_toGraph]

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
  exact and_congr_right fun _ ↦ forall_congr' fun i ↦ by
    rw [kindAt_toGraph, EarKind.toGraph_eq_open_iff]

/-- Normalize any ear decomposition `d : H.EarDecomposition S` to start at a single vertex, turning
an initial cycle into a single-vertex start followed by one closed ear. -/
def toVertexStart (d : H.EarDecomposition S) : H.EarDecomposition S :=
  (earDecompositionEquivOfSimpleGraph (rfl : S.toGraph = S.toGraph)).symm d.toGraph.toVertexStart

@[simp] theorem toGraph_toVertexStart (d : H.EarDecomposition S) :
    d.toVertexStart.toGraph = d.toGraph.toVertexStart := by
  rw [toVertexStart]
  simpa only [earDecompositionEquivOfSimpleGraph_apply, Graph.EarDecomposition.copy_rfl] using
    (earDecompositionEquivOfSimpleGraph (rfl : S.toGraph = S.toGraph)).apply_symm_apply
      d.toGraph.toVertexStart

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
  simpa only [EarStart.isCycle_toGraph, length_toGraph] using d.toGraph.length_toVertexStart

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
      (Fin.natAdd _ i)) (by simp) <|
    (d.toGraph.graphAfter_toVertexStart_natAdd i).trans (d.graphAfter_toGraph i)

/-- Every original ear walk of `d` appears at the corresponding shifted index in
`d.toVertexStart`. -/
theorem walkAt_toVertexStart_natAdd (d : H.EarDecomposition S) (i : Fin d.length) :
    d.toVertexStart.walkAt
      (Fin.cast d.length_toVertexStart.symm (Fin.natAdd (if d.start.IsCycle then 1 else 0) i)) =
      d.walkAt i :=
  walkAt_eq_of_toGraph_copy_eq (hS := rfl)
    (d.toVertexStart.toGraph.copy_rfl.trans d.toGraph_toVertexStart) _
    (Fin.cast d.toGraph.length_toVertexStart.symm (Fin.natAdd _ i)) (by simp) <| by
    rw [d.toGraph.earAt_toVertexStart_natAdd i, ← Graph.EarDecomposition.walkAt_eq, walkAt_toGraph]

/-- Every original ear kind of `d` appears at the corresponding shifted index in
`d.toVertexStart`. -/
theorem kindAt_toVertexStart_natAdd (d : H.EarDecomposition S) (i : Fin d.length) :
    d.toVertexStart.kindAt
      (Fin.cast d.length_toVertexStart.symm (Fin.natAdd (if d.start.IsCycle then 1 else 0) i)) =
      d.kindAt i :=
  kindAt_eq_of_toGraph_copy_eq (hS := rfl)
    (d.toVertexStart.toGraph.copy_rfl.trans d.toGraph_toVertexStart) _
    (Fin.cast d.toGraph.length_toVertexStart.symm (Fin.natAdd _ i)) (by simp) <| by
    rw [d.toGraph.earAt_toVertexStart_natAdd i, ← Graph.EarDecomposition.kindAt_eq, kindAt_toGraph]

/-- Every original ear of `d` appears at the corresponding shifted index in `d.toVertexStart`. -/
theorem earAt_toVertexStart_natAdd (d : H.EarDecomposition S) (i : Fin d.length) :
    d.toVertexStart.earAt
      (Fin.cast d.length_toVertexStart.symm (Fin.natAdd (if d.start.IsCycle then 1 else 0) i)) =
      (d.earAt i).copy (d.subgraphAfter_toVertexStart_natAdd i.castSucc).symm :=
  Ear.ext (by rw [Ear.toWalk_copy, ← walkAt_def, ← walkAt_def, walkAt_toVertexStart_natAdd])

/-- Normalizing an already vertex-started ear decomposition returns it unchanged. -/
theorem toVertexStart_eq_self {d : H.EarDecomposition S} (h : d.IsVertexStart) :
    d.toVertexStart = d :=
  (earDecompositionEquivOfSimpleGraph (rfl : S.toGraph = S.toGraph)).injective <| by
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
    ⟨i.val, by simp [i.isLt.trans_eq (length_toVertexStart_cycle c hc)]⟩ rfl <| by
    rw [Graph.EarDecomposition.earAt_copy, Graph.EarDecomposition.earAt_toVertexStart_cycle,
      Graph.Ear.toWalk_ofIsCycle]

/-- Normalizing a single-cycle decomposition yields a closed ear as its unique ear. -/
@[simp] theorem kindAt_toVertexStart_cycle {u : α} (c : H.Walk u u) (hc : c.IsCycle)
    (i : Fin (cycle c hc).toVertexStart.length) :
    (cycle c hc).toVertexStart.kindAt i = .closed :=
  kindAt_eq_of_toGraph_copy_eq (hS := rfl)
    ((cycle c hc).toVertexStart.toGraph.copy_rfl.trans (toGraph_toVertexStart_cycle c hc)) i
    ⟨i.val, by simp [i.isLt.trans_eq (length_toVertexStart_cycle c hc)]⟩ rfl <| by
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
    (Fin.castLE (Nat.succ_le_succ (d.toGraph.length_le_length_extend _)) k) rfl <| by
    rw [d.toGraph.graphAfter_extend_castLE _ k, graphAfter_toGraph]

@[simp] theorem initial_extend (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S) :
    (d.extend hH).initial = d.initial := by
  simpa only [← subgraphAfter_zero, Fin.castLE_zero] using d.subgraphAfter_extend_castLE hH 0

/-- Extending a partial ear decomposition preserves its initial-stage witness. -/
theorem heq_start_extend (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S) :
    HEq (d.extend hH).start d.start :=
  earStart_heq_of_toGraph_heq ((d.extend hH).subgraphAfter_zero.trans
      ((d.initial_extend hH).trans d.subgraphAfter_zero.symm)) <|
    (((d.extend hH).toGraph.heq_start_copy Subgraph.toGraph_top).symm.trans
      (Graph.EarDecomposition.heq_start_of_eq (d.toGraph_extend hH))).trans
      (d.toGraph.heq_start_extend _)

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
    (Fin.castLE (d.toGraph.length_le_length_extend _) i) rfl <| by
    rw [d.toGraph.earAt_extend_castLE _ i, ← Graph.EarDecomposition.walkAt_eq, walkAt_toGraph]

@[simp] theorem kindAt_extend_castLE (hH : H.IsEdgeConnected 2) (d : H.EarDecomposition S)
    (i : Fin d.length) :
    (d.extend hH).kindAt (Fin.castLE (d.length_le_length_extend hH) i) = d.kindAt i :=
  kindAt_eq_of_toGraph_copy_eq (d.toGraph_extend hH) _
    (Fin.castLE (d.toGraph.length_le_length_extend _) i) rfl <| by
    rw [d.toGraph.earAt_extend_castLE _ i, ← Graph.EarDecomposition.kindAt_eq, kindAt_toGraph]

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
  rw [← d.walkAt_extend_castLE hH (Fin.cast hlen j), ← Fin.castLE_of_eq hlen (h' := hlen.le),
    Fin.castLE_castLE]
  exact (((d.extend hH).prefix k).walkAt_copy hsub j).trans ((d.extend hH).walkAt_prefix k j)

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
