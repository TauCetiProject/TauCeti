/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Bidirected
public import TauCeti.Combinatorics.Network.Isomorphism.Connectivity
public import TauCeti.Combinatorics.Network.Isomorphism.Walk
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Flow
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Connected
import Mathlib.Algebra.Group.PUnit

/-!
# The bidirected network of a simple graph as its capacitated doubled quiver

In the weighted-multigraph flow and connectivity theory, an undirected simple graph `G` is studied
through the bidirected arrow family of `Graph.ofSimpleGraph G`, whose vertices lie in the full
vertex subtype `V(Graph.ofSimpleGraph G)` and whose arrows carry their underlying unordered-pair
edge identity. In quiver representation theory, the same directed graph already appears on the
type copy `TauCeti.DoubledQuiver G`, whose arrows are lifted adjacency proofs and whose total
arrows correspond to `G.Dart`.

This file identifies the two constructions, both structurally and with capacities:

* `TauCeti.DoubledQuiver.capacity` and `TauCeti.DoubledQuiver.network` equip `DoubledQuiver G` with
  capacities from a pair-capacity function `c : Sym2 V → K`, assigning to each arrow the capacity
  of its underlying undirected edge `TauCeti.DoubledQuiver.edge` and ignoring diagonal values.
* `TauCeti.DoubledQuiver.bidirectedNetworkIso` constructs the canonical bounded-network isomorphism
  between the bundled bidirected network `Graph.bidirectedNetwork` of `Graph.ofSimpleGraph G` and
  `DoubledQuiver.network G c hc`.

Through `TauCeti.Network.Iso`, this single isomorphism transports walks, paths, cycles, internal
disjointness, vertex- and edge-deletion reachability, arc and vertex strong connectivity, arrow
assignments, vertex excesses, circulations, acyclic normal forms, cut capacities, and ordinary
flows. In particular, `TauCeti.DoubledQuiver.exists_flow_val_eq_pairCutCapacity_mem` gives the
undirected max-flow/min-cut theorem with additive-subgroup integrality directly on
`DoubledQuiver G`.

## Main definitions

* `SimpleGraph.doubledVertexEquiv`, `SimpleGraph.doubledHomEquiv`,
  `SimpleGraph.bidirectedTotalHomEquivDart`: vertex, arrow, and dart identifications between the
  bidirected arrow family of `Graph.ofSimpleGraph G` and `DoubledQuiver G`.
* `TauCeti.DoubledQuiver.Hom`: the explicit arrow-family adapter for `DoubledQuiver G`.
* `TauCeti.DoubledQuiver.edge`: the underlying undirected edge in `Sym2 V` of a doubled-quiver
  arrow.
* `TauCeti.DoubledQuiver.capacity`, `TauCeti.DoubledQuiver.network`: capacities and the bundled
  ordinary network induced on `DoubledQuiver G` by pair capacities `c : Sym2 V → K`.
* `TauCeti.DoubledQuiver.bidirectedNetworkIso`: the canonical bounded-network isomorphism from the
  bidirected network of `Graph.ofSimpleGraph G` to `DoubledQuiver.network G c hc`.
* `TauCeti.DoubledQuiver.assignmentEquiv`, `TauCeti.DoubledQuiver.boundedFlowEquiv`,
  `TauCeti.DoubledQuiver.flowEquiv`: transport of assignments, bounded terminal assignments, and
  ordinary flows between `(Graph.ofSimpleGraph G).BidirectedHom` and `DoubledQuiver G`.

## Main results

* `TauCeti.DoubledQuiver.mapPath_bidirectedNetworkIso_toBidirected`: transporting the multigraph
  bidirected walk of `p : G.Walk u v` along `bidirectedNetworkIso` recovers
  `DoubledQuiver.walkToPath G p`.
* `TauCeti.DoubledQuiver.isCycle_iff_isCycle_walkToPath_and_nodup_edges`: an undirected cycle of
  `G` is a directed cycle of `DoubledQuiver G` whose arrows have distinct underlying undirected
  edges.
* `TauCeti.DoubledQuiver.isArcReachable_hom_iff`, `TauCeti.DoubledQuiver.arcConnectivity_hom`,
  `TauCeti.DoubledQuiver.vertexStrongConnectivity_hom`: the directed connectivity predicates and
  invariants of `DoubledQuiver G` agree with the undirected edge and vertex connectivity of `G`.
* `TauCeti.DoubledQuiver.arrowSum_capacity_eq_edgeCutCapacity` and
  `TauCeti.DoubledQuiver.arrowSum_capacity_eq_pairCutCapacity`: the directed cut capacity on
  `DoubledQuiver G` equals the multigraph cut capacity, and equals `TauCeti.pairCutCapacity` when
  off-diagonal capacities are supported on `G.edgeSet`.
* `TauCeti.DoubledQuiver.exists_flow_val_eq_pairCutCapacity_mem` and
  `TauCeti.DoubledQuiver.exists_flow_val_eq_pairCutCapacity`: undirected max-flow/min-cut on
  `DoubledQuiver G`, with and without additive-subgroup integrality.
-/

public section

open Finset TauCeti
open scoped Graph TauCeti.Network

universe u v w w'

/-! ### Explicit arrow family, underlying edges, and vertex sets on `DoubledQuiver` -/

namespace TauCeti.DoubledQuiver

section Basic

variable {V : Type u} (G : SimpleGraph V)

/-- The explicit arrow family of `DoubledQuiver G`, exposing its `Quiver` hom types to the
explicit-family `TauCeti.Assignment`, `TauCeti.ArrowWalk`, and `TauCeti.Network` interfaces. -/
abbrev Hom (i j : DoubledQuiver G) : Type :=
  i ⟶ j

/-- Over graph-labelled vertices, the adjacency arrow family `G.AdjHom` and the hom types of
`DoubledQuiver G` are canonically equivalent. -/
def adjHomEquiv (u v : V) : G.AdjHom u v ≃ (vertex G u ⟶ vertex G v) where
  toFun a := arrow G a.down
  invFun e := ⟨by simpa only [vertexEquiv_symm_vertex] using e.down⟩
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

@[simp]
theorem adjHomEquiv_apply {u v : V} (a : G.AdjHom u v) :
    adjHomEquiv G u v a = arrow G a.down :=
  (rfl)

@[simp]
theorem adjHomEquiv_symm_apply {u v : V} (e : vertex G u ⟶ vertex G v) :
    (adjHomEquiv G u v).symm e = ⟨by simpa only [vertexEquiv_symm_vertex] using e.down⟩ :=
  (rfl)

/-- The underlying undirected edge of an arrow in `DoubledQuiver G`, read off through
`DoubledQuiver.totalArrowEquivDart`. -/
def edge {i j : DoubledQuiver G} (e : i ⟶ j) : Sym2 V :=
  (totalArrowEquivDart G ⟨i, j, e⟩).edge

/-- The underlying undirected edge of `e : i ⟶ j` is the unordered pair of its graph endpoints. -/
theorem edge_def {i j : DoubledQuiver G} (e : i ⟶ j) :
    edge G e = s((vertexEquiv G).symm i, (vertexEquiv G).symm j) := by
  rw [edge, totalArrowEquivDart_apply, SimpleGraph.Dart.edge_mk]

/-- The arrow attached to an adjacency proof `h : G.Adj u v` lies over the unordered pair
`s(u, v)`. -/
@[simp]
theorem edge_arrow {u v : V} (h : G.Adj u v) :
    edge G (arrow G h) = s(u, v) := by
  simp [edge_def]

/-- Every arrow of `DoubledQuiver G` lies over an edge of `G`. -/
@[simp]
theorem edge_mem {i j : DoubledQuiver G} (e : i ⟶ j) :
    edge G e ∈ G.edgeSet :=
  (totalArrowEquivDart G ⟨i, j, e⟩).edge_mem

/-- The underlying undirected edge of a doubled-quiver arrow is never diagonal. -/
@[simp]
theorem not_isDiag_edge {i j : DoubledQuiver G} (e : i ⟶ j) :
    ¬(edge G e).IsDiag :=
  G.not_isDiag_of_mem_edgeSet (edge_mem G e)

/-- Reversing an arrow in `DoubledQuiver G` preserves its underlying undirected edge. -/
@[simp]
theorem edge_reverse {i j : DoubledQuiver G} (e : i ⟶ j) :
    edge G (Quiver.reverse e) = edge G e := by
  simp only [edge_def, Sym2.eq_swap]

/-- Transporting the endpoints of an arrow along equalities does not change its underlying edge. -/
@[simp]
theorem edge_homOfEq {i j i' j' : DoubledQuiver G} (e : i ⟶ j) (hi : i = i') (hj : j = j') :
    edge G (Quiver.homOfEq e hi hj) = edge G e := by
  subst hi hj
  rfl

/-- Two total arrows of `DoubledQuiver G` have the same underlying undirected edge if and only if
they are equal or reverses of one another. -/
theorem edge_eq_iff (a b : TotalArrow G) :
    edge G a.2.2 = edge G b.2.2 ↔ a = b ∨ a = reverseTotalArrow G b := by
  rw [edge, edge, SimpleGraph.dart_edge_eq_iff, ← totalArrowEquivDart_reverse,
    (totalArrowEquivDart G).injective.eq_iff, (totalArrowEquivDart G).injective.eq_iff]

/-- At most one arrow leaving a vertex set `S` in `DoubledQuiver G` can lie over any undirected
edge: the opposite arrow of that edge enters `S`. -/
theorem edge_injOn_cut (S : Set (DoubledQuiver G)) :
    Set.InjOn (fun a : TotalArrow G ↦ edge G a.2.2) {a | a.1 ∈ S ∧ a.2.1 ∉ S} := by
  rintro ⟨i₁, j₁, e₁⟩ ⟨hi₁, _⟩ ⟨i₂, j₂, e₂⟩ ⟨_, hj₂⟩ hab
  simp only [edge_def, Sym2.eq_iff] at hab
  rcases hab with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
  · obtain rfl : i₁ = i₂ := (vertexEquiv G).symm.injective h₁
    obtain rfl : j₁ = j₂ := (vertexEquiv G).symm.injective h₂
    simp [Subsingleton.elim e₁ e₂]
  · obtain rfl : i₁ = j₂ := (vertexEquiv G).symm.injective h₁
    exact absurd hi₁ hj₂

/-- Include a finite set of graph vertices into `DoubledQuiver G`. -/
def vertexFinset (S : Finset V) : Finset (DoubledQuiver G) :=
  S.map (vertexEquiv G).toEmbedding

@[simp]
theorem mem_vertexFinset_iff {S : Finset V} {i : DoubledQuiver G} :
    i ∈ vertexFinset G S ↔ (vertexEquiv G).symm i ∈ S := by
  rw [vertexFinset, Finset.mem_map_equiv]

@[simp]
theorem vertexFinset_empty : vertexFinset G (∅ : Finset V) = ∅ :=
  Finset.map_empty _

@[simp]
theorem vertexFinset_univ [Fintype V] :
    vertexFinset G (univ : Finset V) = univ :=
  Finset.map_univ_of_surjective (vertexEquiv G).surjective

/-- Mapping back along `(vertexEquiv G).symm` recovers the original finite set of graph vertices. -/
@[simp]
theorem map_symm_vertexFinset (S : Finset V) :
    (vertexFinset G S).map (vertexEquiv G).symm.toEmbedding = S := by
  simp [vertexFinset, Finset.map_map]

/-- Vertex-set inclusion into `DoubledQuiver G` commutes with complementation. -/
theorem vertexFinset_compl [Fintype V] [DecidableEq V] (S : Finset V) :
    vertexFinset G Sᶜ = (vertexFinset G S)ᶜ := by
  ext i
  simp

end Basic

/-! ### Capacities and bundled network on `DoubledQuiver` -/

section Capacity

variable {V : Type u} {K : Type w} (G : SimpleGraph V)

/-- The arrow capacities on `DoubledQuiver G` induced by unordered-pair capacities `c : Sym2 V → K`:
each arrow carries the capacity of its underlying undirected edge, so opposite arrows carry equal
capacity and diagonal or non-edge values of `c` are ignored. -/
def capacity (c : Sym2 V → K) : Assignment (Hom G) K :=
  fun _ _ e ↦ c (edge G e)

@[simp]
theorem capacity_apply (c : Sym2 V → K) {i j : DoubledQuiver G} (e : i ⟶ j) :
    capacity G c e = c (edge G e) :=
  (rfl)

theorem capacity_arrow (c : Sym2 V → K) {u v : V} (h : G.Adj u v) :
    capacity G c (arrow G h) = c s(u, v) := by
  simp

/-- Opposite arrows in `DoubledQuiver G` carry equal capacity. -/
theorem capacity_reverse (c : Sym2 V → K) {i j : DoubledQuiver G} (e : i ⟶ j) :
    capacity G c (Quiver.reverse e) = capacity G c e := by
  simp

/-- Two pair-capacity functions that agree on `G.edgeSet` induce identical arrow capacities on
`DoubledQuiver G`; values on the diagonal or away from `G.edgeSet` have no effect. -/
theorem capacity_congr {c₁ c₂ : Sym2 V → K} (h : ∀ p ∈ G.edgeSet, c₁ p = c₂ p) :
    capacity G c₁ = capacity G c₂ := by
  funext _ _ e
  exact h (edge G e) (edge_mem G e)

/-- Pair capacities that are nonnegative on the edges of `G` induce nonnegative arrow capacities on
`DoubledQuiver G`. -/
theorem capacity_nonneg [Zero K] [LE K] {c : Sym2 V → K}
    (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) : 0 ≤ capacity G c :=
  fun _ _ e ↦ hc (edge G e) (edge_mem G e)

@[simp]
theorem capacity_zero [Zero K] : capacity G (0 : Sym2 V → K) = 0 :=
  (rfl)

/-- Mapping coefficients of `DoubledQuiver.capacity` composes the pair-capacity function with the
coefficient map. -/
@[simp]
theorem map_capacity {L : Type w'} (c : Sym2 V → K) (φ : K → L) :
    (capacity G c).map φ = capacity G (φ ∘ c) :=
  (rfl)

/-- `DoubledQuiver G` equipped with zero lower bounds and nonnegative pair capacities `c` on its
arrows, bundled as a `TauCeti.Network`.

This definition is exposed and reducible so that its arrow family reduces to `DoubledQuiver.Hom G`,
inheriting `Network.ofCapacity`'s projection lemmas as well as the `Quiver` and finiteness
instances of `DoubledQuiver G`. -/
@[expose, reducible]
def network [Zero K] [LE K] (c : Sym2 V → K) (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) :
    Network K (DoubledQuiver G) :=
  Network.ofCapacity (Hom G) (capacity G c) (fun {i j} e ↦ capacity_nonneg G hc i j e)

@[simp]
theorem network_lower [Zero K] [LE K] (c : Sym2 V → K) (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) :
    (network G c hc).lower = 0 :=
  (rfl)

@[simp]
theorem network_upper [Zero K] [LE K] (c : Sym2 V → K) (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) :
    (network G c hc).upper = capacity G c :=
  (rfl)

end Capacity

end TauCeti.DoubledQuiver

/-! ### Vertex, arrow, and dart identifications with `Graph.ofSimpleGraph` -/

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-- The canonical equivalence between the actual vertex subtype of `Graph.ofSimpleGraph G` and
`DoubledQuiver G`. -/
def doubledVertexEquiv : V(Graph.ofSimpleGraph G) ≃ DoubledQuiver G :=
  (Equiv.Set.univ V).trans (DoubledQuiver.vertexEquiv G)

@[simp]
theorem doubledVertexEquiv_apply (x : V(Graph.ofSimpleGraph G)) :
    G.doubledVertexEquiv x = DoubledQuiver.vertex G x.1 :=
  DoubledQuiver.vertexEquiv_apply G x.1

theorem doubledVertexEquiv_toOfSimpleGraphVertex (u : V) :
    G.doubledVertexEquiv (G.toOfSimpleGraphVertex u) = DoubledQuiver.vertex G u := by
  rw [doubledVertexEquiv_apply, toOfSimpleGraphVertex_val]

theorem coe_doubledVertexEquiv_symm_apply (i : DoubledQuiver G) :
    (G.doubledVertexEquiv.symm i : V) = (DoubledQuiver.vertexEquiv G).symm i :=
  (rfl)

@[simp]
theorem doubledVertexEquiv_symm_apply (i : DoubledQuiver G) :
    G.doubledVertexEquiv.symm i =
      G.toOfSimpleGraphVertex ((DoubledQuiver.vertexEquiv G).symm i) :=
  Subtype.ext ((G.coe_doubledVertexEquiv_symm_apply i).trans (G.toOfSimpleGraphVertex_val _).symm)

theorem doubledVertexEquiv_symm_vertex (u : V) :
    G.doubledVertexEquiv.symm (DoubledQuiver.vertex G u) = G.toOfSimpleGraphVertex u := by
  simp

/-- Transporting a finite set of vertices from `Graph.ofSimpleGraph G` along `doubledVertexEquiv`
produces `DoubledQuiver.vertexFinset`. -/
@[simp]
theorem map_doubledVertexEquiv_toOfSimpleGraphFinset (S : Finset V) :
    (G.toOfSimpleGraphFinset S).map G.doubledVertexEquiv.toEmbedding =
      DoubledQuiver.vertexFinset G S := by
  ext i
  rw [Finset.mem_map_equiv, G.doubledVertexEquiv_symm_apply, G.mem_toOfSimpleGraphFinset,
    DoubledQuiver.mem_vertexFinset_iff]

/-- Every bidirected arrow of `Graph.ofSimpleGraph G` witnesses adjacency of its endpoints in
`G`. -/
theorem adj_of_bidirectedHom {x y : V(Graph.ofSimpleGraph G)}
    (a : (Graph.ofSimpleGraph G).BidirectedHom x y) : G.Adj x.1 y.1 := by
  have ha := a.2
  rw [Graph.ofSimpleGraph_isLink] at ha
  simpa only [ha.1, SimpleGraph.mem_edgeSet] using ha.2

/-- The underlying multigraph edge of a bidirected arrow of `Graph.ofSimpleGraph G` is the
unordered pair of its endpoints. -/
theorem edge_eq_of_bidirectedHom {x y : V(Graph.ofSimpleGraph G)}
    (a : (Graph.ofSimpleGraph G).BidirectedHom x y) : a.1 = s(x.1, y.1) := by
  have ha := a.2
  rw [Graph.ofSimpleGraph_isLink] at ha
  exact ha.1

/-- Over corresponding endpoints, the bidirected arrows of `Graph.ofSimpleGraph G` and the arrows
of `DoubledQuiver G` are canonically equivalent. -/
def doubledHomEquiv (x y : V(Graph.ofSimpleGraph G)) :
    (Graph.ofSimpleGraph G).BidirectedHom x y ≃
      (G.doubledVertexEquiv x ⟶ G.doubledVertexEquiv y) where
  toFun a := Quiver.homOfEq (DoubledQuiver.arrow G (G.adj_of_bidirectedHom a))
    (G.doubledVertexEquiv_apply x).symm (G.doubledVertexEquiv_apply y).symm
  invFun e := ⟨s(x.1, y.1), by
    rw [Graph.ofSimpleGraph_isLink]
    refine ⟨rfl, ?_⟩
    have hmem := DoubledQuiver.edge_mem G e
    rwa [DoubledQuiver.edge_def, G.doubledVertexEquiv_apply, G.doubledVertexEquiv_apply,
      DoubledQuiver.vertexEquiv_symm_vertex, DoubledQuiver.vertexEquiv_symm_vertex] at hmem⟩
  left_inv a := Subtype.ext (G.edge_eq_of_bidirectedHom a).symm
  right_inv _ := Subsingleton.elim _ _

theorem doubledHomEquiv_apply {x y : V(Graph.ofSimpleGraph G)}
    (a : (Graph.ofSimpleGraph G).BidirectedHom x y) :
    G.doubledHomEquiv x y a = Quiver.homOfEq (DoubledQuiver.arrow G (G.adj_of_bidirectedHom a))
      (G.doubledVertexEquiv_apply x).symm (G.doubledVertexEquiv_apply y).symm :=
  (rfl)

@[simp]
theorem coe_doubledHomEquiv_symm_apply {x y : V(Graph.ofSimpleGraph G)}
    (e : G.doubledVertexEquiv x ⟶ G.doubledVertexEquiv y) :
    ((G.doubledHomEquiv x y).symm e : Sym2 V) = s(x.1, y.1) :=
  (rfl)

/-- Transporting a bidirected arrow of `Graph.ofSimpleGraph G` to `DoubledQuiver G` preserves its
underlying unordered-pair edge. -/
@[simp]
theorem edge_doubledHomEquiv {x y : V(Graph.ofSimpleGraph G)}
    (a : (Graph.ofSimpleGraph G).BidirectedHom x y) :
    DoubledQuiver.edge G (G.doubledHomEquiv x y a) = a.1 := by
  rw [doubledHomEquiv_apply, DoubledQuiver.edge_homOfEq, DoubledQuiver.edge_arrow,
    G.edge_eq_of_bidirectedHom a]

/-- The total arrows of `(Graph.ofSimpleGraph G).BidirectedHom` correspond canonically to the darts
of `G`. -/
def bidirectedTotalHomEquivDart :
    (Σ x y, (Graph.ofSimpleGraph G).BidirectedHom x y) ≃ G.Dart :=
  (Equiv.sigmaCongr G.doubledVertexEquiv fun x ↦
    Equiv.sigmaCongr G.doubledVertexEquiv (G.doubledHomEquiv x)).trans
    (DoubledQuiver.totalArrowEquivDart G)

@[simp]
theorem bidirectedTotalHomEquivDart_fst (a : Σ x y, (Graph.ofSimpleGraph G).BidirectedHom x y) :
    (G.bidirectedTotalHomEquivDart a).fst = a.1.1 := by
  rcases a with ⟨x, y, a⟩
  simp [bidirectedTotalHomEquivDart, Equiv.sigmaCongr]

@[simp]
theorem bidirectedTotalHomEquivDart_snd (a : Σ x y, (Graph.ofSimpleGraph G).BidirectedHom x y) :
    (G.bidirectedTotalHomEquivDart a).snd = a.2.1.1 := by
  rcases a with ⟨x, y, a⟩
  simp [bidirectedTotalHomEquivDart, Equiv.sigmaCongr]

@[simp]
theorem bidirectedTotalHomEquivDart_edge (a : Σ x y, (Graph.ofSimpleGraph G).BidirectedHom x y) :
    (G.bidirectedTotalHomEquivDart a).edge = a.2.2.1 := by
  rw [SimpleGraph.Dart.edge, G.bidirectedTotalHomEquivDart_fst, G.bidirectedTotalHomEquivDart_snd,
    ← G.edge_eq_of_bidirectedHom a.2.2]

end SimpleGraph

/-! ### Canonical bounded-network isomorphism -/

namespace TauCeti.DoubledQuiver

section NetworkIso

variable {V : Type u} {K : Type w} (G : SimpleGraph V)

/-- The canonical isomorphism of bounded networks from the bidirected network of
`Graph.ofSimpleGraph G` to `DoubledQuiver.network G c hc`. Both networks depend on `c` only along
`G.edgeSet`, so no off-graph support hypothesis is needed here. -/
def bidirectedNetworkIso [Zero K] [LE K] (c : Sym2 V → K) (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) :
    (Graph.ofSimpleGraph G).bidirectedNetwork (G.ofSimpleGraphCapacity c)
      (G.ofSimpleGraphCapacity_nonneg hc) ≃ₙ
    network G c hc where
  vertexEquiv := G.doubledVertexEquiv
  homEquiv := G.doubledHomEquiv
  map_lower _ := rfl
  map_upper a := by
    simp only [capacity_apply, G.edge_doubledHomEquiv, Graph.bidirectedCapacity_apply,
      SimpleGraph.ofSimpleGraphCapacity_apply]

theorem bidirectedNetworkIso_vertexEquiv [Zero K] [LE K] (c : Sym2 V → K)
    (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) :
    (bidirectedNetworkIso G c hc).vertexEquiv = G.doubledVertexEquiv :=
  (rfl)

@[simp]
theorem bidirectedNetworkIso_vertexEquiv_apply [Zero K] [LE K] (c : Sym2 V → K)
    (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) (x : V(Graph.ofSimpleGraph G)) :
    (bidirectedNetworkIso G c hc).vertexEquiv x = G.doubledVertexEquiv x :=
  (rfl)

theorem bidirectedNetworkIso_vertexEquiv_mk [Zero K] [LE K] (c : Sym2 V → K)
    (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) (u : V) (hu : u ∈ V(Graph.ofSimpleGraph G)) :
    (bidirectedNetworkIso G c hc).vertexEquiv ⟨u, hu⟩ = vertex G u :=
  G.doubledVertexEquiv_apply ⟨u, hu⟩

/-- Arrow transport along `bidirectedNetworkIso` applies `SimpleGraph.doubledHomEquiv` after
transporting endpoints along `bidirectedNetworkIso_vertexEquiv_apply`. -/
@[simp]
theorem bidirectedNetworkIso_homEquiv_apply [Zero K] [LE K] (c : Sym2 V → K)
    (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) (x y : V(Graph.ofSimpleGraph G))
    (a : (Graph.ofSimpleGraph G).BidirectedHom x y) :
    Quiver.homOfEq ((bidirectedNetworkIso G c hc).homEquiv x y a)
      (bidirectedNetworkIso_vertexEquiv_apply G c hc x)
      (bidirectedNetworkIso_vertexEquiv_apply G c hc y) = G.doubledHomEquiv x y a :=
  (rfl)

/-- Transporting an arrow along `bidirectedNetworkIso` preserves its underlying undirected edge. -/
@[simp]
theorem edge_bidirectedNetworkIso_homEquiv [Zero K] [LE K] (c : Sym2 V → K)
    (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) {x y : V(Graph.ofSimpleGraph G)}
    (a : (Graph.ofSimpleGraph G).BidirectedHom x y) :
    edge G ((bidirectedNetworkIso G c hc).homEquiv x y a) = a.1 := by
  rw [← G.edge_doubledHomEquiv a, ← bidirectedNetworkIso_homEquiv_apply G c hc x y a,
    edge_homOfEq]

/-- Composing the total-arrow equivalence of `bidirectedNetworkIso` with
`DoubledQuiver.totalArrowEquivDart` gives `SimpleGraph.bidirectedTotalHomEquivDart`. -/
@[simp]
theorem bidirectedNetworkIso_totalHomEquiv_trans_totalArrowEquivDart [Zero K] [LE K]
    (c : Sym2 V → K) (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) :
    (bidirectedNetworkIso G c hc).totalHomEquiv.trans (totalArrowEquivDart G) =
      G.bidirectedTotalHomEquivDart := by
  apply Equiv.ext
  rintro ⟨x, y, a⟩
  apply SimpleGraph.Dart.ext
  ext <;> simp

/-- Auxiliary `Unit`-capacitated instance of `bidirectedNetworkIso`, used to transport purely
structural walk, assignment, and connectivity statements without introducing capacity hypotheses. -/
private def unitBidirectedNetworkIso :
    (Graph.ofSimpleGraph G).bidirectedNetwork (G.ofSimpleGraphCapacity fun _ ↦ ())
      (G.ofSimpleGraphCapacity_nonneg fun _ _ ↦ le_rfl) ≃ₙ
    network G (fun _ ↦ ()) (fun _ _ ↦ le_rfl) :=
  bidirectedNetworkIso G (fun _ ↦ ()) (fun _ _ ↦ le_rfl)

private theorem unitBidirectedNetworkIso_vertexEquiv :
    (unitBidirectedNetworkIso G).vertexEquiv = G.doubledVertexEquiv :=
  bidirectedNetworkIso_vertexEquiv G _ _

@[simp]
private theorem unitBidirectedNetworkIso_vertexEquiv_apply (x : V(Graph.ofSimpleGraph G)) :
    (unitBidirectedNetworkIso G).vertexEquiv x = G.doubledVertexEquiv x :=
  bidirectedNetworkIso_vertexEquiv_apply G _ _ x

private theorem unitBidirectedNetworkIso_vertexEquiv_toOfSimpleGraphVertex (u : V) :
    (unitBidirectedNetworkIso G).vertexEquiv (G.toOfSimpleGraphVertex u) = vertex G u := by
  rw [unitBidirectedNetworkIso_vertexEquiv_apply, G.doubledVertexEquiv_toOfSimpleGraphVertex]

@[simp]
private theorem unitBidirectedNetworkIso_homEquiv_apply (x y : V(Graph.ofSimpleGraph G))
    (a : (Graph.ofSimpleGraph G).BidirectedHom x y) :
    Quiver.homOfEq ((unitBidirectedNetworkIso G).homEquiv x y a)
      (unitBidirectedNetworkIso_vertexEquiv_apply G x)
      (unitBidirectedNetworkIso_vertexEquiv_apply G y) = G.doubledHomEquiv x y a :=
  bidirectedNetworkIso_homEquiv_apply G _ _ x y a

@[simp]
private theorem edge_unitBidirectedNetworkIso_homEquiv {x y : V(Graph.ofSimpleGraph G)}
    (a : (Graph.ofSimpleGraph G).BidirectedHom x y) :
    edge G ((unitBidirectedNetworkIso G).homEquiv x y a) = a.1 :=
  edge_bidirectedNetworkIso_homEquiv G _ _ a

end NetworkIso

/-! ### Walk, path, cycle, and connectivity bridge -/

section WalkAndConnectivity

variable {V : Type u} (G : SimpleGraph V)

/-- **Walk coherence.** Sending a simple-graph walk to `Graph.ofSimpleGraph G`, orienting its steps
in `(Graph.ofSimpleGraph G).BidirectedHom`, and transporting the resulting directed walk along
`bidirectedNetworkIso` yields `DoubledQuiver.walkToPath` after transporting the endpoints along
`bidirectedNetworkIso_vertexEquiv_mk`. -/
theorem mapPath_bidirectedNetworkIso_toBidirected {K : Type w} [Zero K] [LE K]
    (c : Sym2 V → K) (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) {u v : V} (p : G.Walk u v)
    (hu : u ∈ V(Graph.ofSimpleGraph G) := by simp) :
    Quiver.Path.cast
      (bidirectedNetworkIso_vertexEquiv_mk G c hc u hu)
      (bidirectedNetworkIso_vertexEquiv_mk G c hc v (p.toGraph.end_mem_vertexSet hu))
      ((bidirectedNetworkIso G c hc).mapPath (p.toGraph.toBidirected hu)) =
      walkToPath G p := by
  apply ArrowWalk.vertices_injective (Q := Hom G)
  rw [ArrowWalk.vertices_cast (Q := Hom G), Network.Iso.vertices_mapPath]
  have hv : ⇑(bidirectedNetworkIso G c hc).vertexEquiv = vertex G ∘ Subtype.val :=
    funext fun x ↦ (bidirectedNetworkIso_vertexEquiv_apply G c hc x).trans
      (G.doubledVertexEquiv_apply x)
  rw [hv, ← List.map_map, ← List.unattach, Graph.Walk.vertices_toBidirected,
    SimpleGraph.Walk.support_toGraph, ArrowWalk.vertices, vertices_walkToPath]

/-- Reading the darts off the traversed arrows of `walkToPath G p` recovers `p.darts`. -/
@[simp]
theorem map_totalArrowEquivDart_arrows_walkToPath {u v : V} (p : G.Walk u v) :
    (ArrowWalk.arrows (Q := Hom G) (walkToPath G p)).map (totalArrowEquivDart G) = p.darts := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [walkToPath_cons, ← ArrowWalk.comp, ArrowWalk.arrows_comp, List.map_append, ih]
    simp [Quiver.Hom.toPath]

/-- Reading the underlying undirected edges off the traversed arrows of `walkToPath G p` recovers
`p.edges`. -/
@[simp]
theorem map_edge_arrows_walkToPath {u v : V} (p : G.Walk u v) :
    (ArrowWalk.arrows (Q := Hom G) (walkToPath G p)).map (fun a ↦ edge G a.2.2) = p.edges := by
  rw [p.edges_eq_map_darts, ← map_totalArrowEquivDart_arrows_walkToPath G p, List.map_map]
  simp only [Function.comp_def, edge]

/-- `DoubledQuiver.walkToPath` preserves and reflects simple paths. -/
@[simp]
theorem isPath_walkToPath_iff {u v : V} {p : G.Walk u v} :
    ArrowWalk.IsPath (Q := Hom G) (walkToPath G p) ↔ p.IsPath := by
  rw [ArrowWalk.isPath_def, SimpleGraph.Walk.isPath_def, ArrowWalk.vertices, vertices_walkToPath,
    List.nodup_map_iff (vertex_injective G)]

/-- `DoubledQuiver.pathToWalk` preserves and reflects simple paths. -/
@[simp]
theorem isPath_pathToWalk_iff {u v : V} {q : Quiver.Path (vertex G u) (vertex G v)} :
    (pathToWalk G q).IsPath ↔ ArrowWalk.IsPath (Q := Hom G) q := by
  rw [← isPath_walkToPath_iff (G := G), walkToPath_pathToWalk]

/-- `DoubledQuiver.walkToPath` preserves and reflects internal vertex disjointness between fixed
endpoints. -/
@[simp]
theorem internallyDisjoint_walkToPath_iff {u v : V} {p q : G.Walk u v} :
    ArrowWalk.InternallyDisjoint (Q := Hom G) (walkToPath G p) (walkToPath G q) ↔
      p.InternallyDisjoint q := by
  rw [ArrowWalk.internallyDisjoint_def, SimpleGraph.Walk.internallyDisjoint_def]
  simp only [ArrowWalk.vertices, vertices_walkToPath, List.mem_map]
  refine ⟨fun h w hwp hwq ↦ ?_, ?_⟩
  · exact (h (vertex G w) ⟨w, hwp, rfl⟩ ⟨w, hwq, rfl⟩).imp
      (fun h₁ ↦ (vertex_injective G) h₁) (fun h₂ ↦ (vertex_injective G) h₂)
  · rintro h _ ⟨w, hwp, rfl⟩ ⟨w', hwq, hww'⟩
    exact (h w hwp (((vertex_injective G) hww') ▸ hwq)).imp
      (congrArg (vertex G)) (congrArg (vertex G))

/-- A closed walk of `G` is an undirected cycle if and only if `walkToPath G p` is a directed cycle
in `DoubledQuiver G` and `p` is a trail. A two-step backtrack `u → v → u` forms a directed cycle
in `DoubledQuiver G`, so the trail condition cannot be dropped. -/
theorem isCycle_iff_isCycle_walkToPath_and_isTrail {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ ArrowWalk.IsCycle (Q := Hom G) (walkToPath G p) ∧ p.IsTrail := by
  have htail : (ArrowWalk.vertices (Q := Hom G) (walkToPath G p)).tail.Nodup ↔
      p.support.tail.Nodup := by
    rw [ArrowWalk.vertices, vertices_walkToPath, ← List.map_tail,
      List.nodup_map_iff (vertex_injective G)]
  rw [SimpleGraph.Walk.isCycle_def, ArrowWalk.isCycle_def, htail, ArrowWalk.length,
    length_walkToPath, ne_eq, SimpleGraph.Walk.eq_nil_iff_nil,
    ← SimpleGraph.Walk.length_eq_zero_iff, Nat.pos_iff_ne_zero]
  tauto

/-- Purely in terms of `DoubledQuiver G`, a closed walk of `G` is an undirected cycle if and only
if `walkToPath G p` is a directed cycle whose traversed arrows have distinct underlying undirected
edges. -/
theorem isCycle_iff_isCycle_walkToPath_and_nodup_edges {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ ArrowWalk.IsCycle (Q := Hom G) (walkToPath G p) ∧
      ((ArrowWalk.arrows (Q := Hom G) (walkToPath G p)).map (fun a ↦ edge G a.2.2)).Nodup := by
  rw [isCycle_iff_isCycle_walkToPath_and_isTrail, map_edge_arrows_walkToPath,
    SimpleGraph.Walk.isTrail_def]

/-- Reachability in `DoubledQuiver G` while avoiding `vertex G '' X` is the existence of a walk of
`G` visiting no vertex of `X`. -/
theorem reachableAvoiding_hom_iff {X : Set V} {u v : V} :
    ReachableAvoiding (Hom G) (vertex G '' X) (vertex G u) (vertex G v) ↔
      ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∉ X := by
  simp only [reachableAvoiding_def]
  refine ⟨fun ⟨q, hq⟩ ↦ ⟨pathToWalk G q, fun w hw hwX ↦ hq (vertex G w) ?_ ⟨w, hwX, rfl⟩⟩,
    fun ⟨p, hp⟩ ↦ ⟨walkToPath G p, ?_⟩⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ((support_pathToWalk G q) ▸ hw)
    simpa only [vertexEquiv_symm_apply] using hi
  · rintro _ hi ⟨w, hwX, rfl⟩
    have hmem : vertex G w ∈ p.support.map (vertex G) := by
      simpa only [ArrowWalk.vertices, vertices_walkToPath] using hi
    exact hp w ((List.mem_map_of_injective (vertex_injective G)).1 hmem) hwX

/-- Reachability in `DoubledQuiver G` after deleting all arrows whose underlying undirected edge
lies in `F` agrees with reachability in `G.deleteEdges F`. -/
theorem reachableWithout_edge_mem_iff (F : Set (Sym2 V)) {u v : V} :
    ReachableWithout (Q := Hom G) {a : TotalArrow G | edge G a.2.2 ∈ F}
      (vertex G u) (vertex G v) ↔ (G.deleteEdges F).Reachable u v := by
  have hpre : (unitBidirectedNetworkIso G).totalHomEquiv ⁻¹'
      {a : TotalArrow G | edge G a.2.2 ∈ F} =
      {a : Σ x y, (Graph.ofSimpleGraph G).BidirectedHom x y | a.2.2.1 ∈ F} := by
    ext ⟨x, y, a⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Network.Iso.totalHomEquiv_apply]
    rw [edge_unitBidirectedNetworkIso_homEquiv]
  simpa [hpre, Graph.reachableWithout_bidirectedHom_iff, Graph.ofSimpleGraph_deleteEdges] using
    ((unitBidirectedNetworkIso G).reachableWithout_preimage_iff
      (F := {a : TotalArrow G | edge G a.2.2 ∈ F})
      (s := G.toOfSimpleGraphVertex u) (t := G.toOfSimpleGraphVertex v)).symm

/-- Local `k`-arc-reachability in `DoubledQuiver G` agrees with `k`-edge-reachability in `G`. -/
@[simp]
theorem isArcReachable_hom_iff {k : ℕ} {u v : V} :
    IsArcReachable (Hom G) k (vertex G u) (vertex G v) ↔ G.IsEdgeReachable k u v := by
  simpa using ((unitBidirectedNetworkIso G).isArcReachable_iff (k := k)
    (s := G.toOfSimpleGraphVertex u) (t := G.toOfSimpleGraphVertex v)).symm

/-- Global `k`-arc-strength of `DoubledQuiver G` agrees with `k`-edge-connectivity of `G`. -/
@[simp]
theorem isArcStrong_hom_iff {k : ℕ} :
    IsArcStrong (Hom G) k ↔ G.IsEdgeConnected k := by
  rw [← (unitBidirectedNetworkIso G).isArcStrong_iff, Graph.isArcStrong_bidirectedHom_iff,
    Graph.isEdgeConnected_ofSimpleGraph_iff]

/-- The arc connectivity of `DoubledQuiver G` equals the edge connectivity of `G`. -/
@[simp]
theorem arcConnectivity_hom :
    arcConnectivity (Hom G) = G.edgeConnectivity := by
  rw [← (unitBidirectedNetworkIso G).arcConnectivity_eq, Graph.arcConnectivity_bidirectedHom,
    Graph.edgeConnectivity_ofSimpleGraph]

/-- Global `k`-vertex-strength of `DoubledQuiver G` agrees with `k`-vertex-connectivity of `G`. -/
@[simp]
theorem isVertexStrong_hom_iff {k : ℕ} :
    IsVertexStrong (Hom G) k ↔ G.IsVertexConnected k := by
  rw [← (unitBidirectedNetworkIso G).isVertexStrong_iff, Graph.isVertexStrong_bidirectedHom_iff,
    Graph.isVertexConnected_ofSimpleGraph_iff]

/-- The vertex strong connectivity of `DoubledQuiver G` equals the vertex connectivity of `G`. -/
@[simp]
theorem vertexStrongConnectivity_hom :
    vertexStrongConnectivity (Hom G) = G.vertexConnectivity := by
  rw [← (unitBidirectedNetworkIso G).vertexStrongConnectivity_eq,
    Graph.vertexStrongConnectivity_bidirectedHom, Graph.vertexConnectivity_ofSimpleGraph]

end WalkAndConnectivity

/-! ### Assignment, excess, acyclic-support, cut-capacity, and flow transport -/

section Assignments

variable {V : Type u} (G : SimpleGraph V) (R : Type w')

/-- Transport arrow assignments between the bidirected arrow family of `Graph.ofSimpleGraph G` and
`DoubledQuiver G`. -/
def assignmentEquiv :
    Assignment (Graph.ofSimpleGraph G).BidirectedHom R ≃ Assignment (Hom G) R :=
  (unitBidirectedNetworkIso G).assignmentEquiv R

variable {R}

private theorem assignmentEquiv_eq :
    assignmentEquiv G R = (unitBidirectedNetworkIso G).assignmentEquiv R :=
  (rfl)

@[simp]
theorem assignmentEquiv_apply (f : Assignment (Graph.ofSimpleGraph G).BidirectedHom R)
    {x y : V(Graph.ofSimpleGraph G)} (a : (Graph.ofSimpleGraph G).BidirectedHom x y) :
    assignmentEquiv G R f (G.doubledHomEquiv x y a) = f a := by
  rw [assignmentEquiv_eq, ← unitBidirectedNetworkIso_homEquiv_apply G x y a,
    Assignment.apply_homOfEq ((unitBidirectedNetworkIso G).assignmentEquiv R f)]
  exact (unitBidirectedNetworkIso G).assignmentEquiv_apply R f a

@[simp]
theorem assignmentEquiv_symm_apply (f : Assignment (Hom G) R)
    {x y : V(Graph.ofSimpleGraph G)} (a : (Graph.ofSimpleGraph G).BidirectedHom x y) :
    (assignmentEquiv G R).symm f a = f (G.doubledHomEquiv x y a) := by
  rw [assignmentEquiv_eq, (unitBidirectedNetworkIso G).assignmentEquiv_symm_apply,
    ← unitBidirectedNetworkIso_homEquiv_apply G x y a, Assignment.apply_homOfEq f]

/-- Assignment transport along any `bidirectedNetworkIso` agrees with the capacity-free
`DoubledQuiver.assignmentEquiv`. -/
@[simp]
theorem bidirectedNetworkIso_assignmentEquiv {K : Type w} [Zero K] [LE K] (c : Sym2 V → K)
    (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) :
    (bidirectedNetworkIso G c hc).assignmentEquiv R = assignmentEquiv G R := by
  apply Equiv.ext
  intro f
  apply (assignmentEquiv G R).symm.injective
  ext x y a
  rw [assignmentEquiv_symm_apply, Equiv.symm_apply_apply,
    ← bidirectedNetworkIso_homEquiv_apply G c hc x y a,
    Assignment.apply_homOfEq ((bidirectedNetworkIso G c hc).assignmentEquiv R f)]
  exact (bidirectedNetworkIso G c hc).assignmentEquiv_apply R f a

@[simp]
theorem assignmentEquiv_zero [Zero R] :
    assignmentEquiv G R 0 = 0 := by
  rw [assignmentEquiv_eq, (unitBidirectedNetworkIso G).assignmentEquiv_zero]

/-- Transporting `(Graph.ofSimpleGraph G).bidirectedCapacity (G.ofSimpleGraphCapacity c)` produces
`DoubledQuiver.capacity G c`, with no nonnegativity or support assumption on `c`. -/
@[simp]
theorem assignmentEquiv_bidirectedCapacity (c : Sym2 V → R) :
    assignmentEquiv G R ((Graph.ofSimpleGraph G).bidirectedCapacity (G.ofSimpleGraphCapacity c)) =
      capacity G c := by
  apply (assignmentEquiv G R).symm.injective
  ext x y a
  simp

/-- Assignment transport preserves and reflects the pointwise order. -/
theorem assignmentEquiv_le_assignmentEquiv_iff [LE R]
    (f g : Assignment (Graph.ofSimpleGraph G).BidirectedHom R) :
    assignmentEquiv G R f ≤ assignmentEquiv G R g ↔ f ≤ g := by
  rw [assignmentEquiv_eq]
  exact (unitBidirectedNetworkIso G).assignmentEquiv_le_assignmentEquiv_iff f g

/-- Assignment transport preserves and reflects subgroup membership of arrow values. -/
theorem forall_assignmentEquiv_mem_iff {M : Type*} [SetLike M R] (A : M)
    (f : Assignment (Graph.ofSimpleGraph G).BidirectedHom R) :
    (∀ ⦃i j : DoubledQuiver G⦄ (e : i ⟶ j), assignmentEquiv G R f e ∈ A) ↔
      ∀ ⦃x y : V(Graph.ofSimpleGraph G)⦄ (a : (Graph.ofSimpleGraph G).BidirectedHom x y),
        f a ∈ A := by
  rw [assignmentEquiv_eq]
  exact (unitBidirectedNetworkIso G).forall_assignmentEquiv_mem_iff A f

/-- Assignment transport preserves and reflects acyclicity of positive support. -/
@[simp]
theorem isAcyclic_assignmentEquiv_iff [Zero R] [LT R]
    (f : Assignment (Graph.ofSimpleGraph G).BidirectedHom R) :
    (assignmentEquiv G R f).IsAcyclic ↔ f.IsAcyclic := by
  rw [assignmentEquiv_eq, (unitBidirectedNetworkIso G).isAcyclic_assignmentEquiv_iff]

end Assignments

section CutAndExcess

variable {V : Type u} {K : Type w} (G : SimpleGraph V)

/-- Transporting both the assignment and the endpoint sets along `doubledVertexEquiv` and
`doubledHomEquiv` preserves `arrowSum`. -/
theorem arrowSum_assignmentEquiv
    [∀ x y, Fintype ((Graph.ofSimpleGraph G).BidirectedHom x y)]
    [∀ i j : DoubledQuiver G, Fintype (i ⟶ j)] [AddCommMonoid K]
    (f : Assignment (Graph.ofSimpleGraph G).BidirectedHom K)
    (S T : Finset V(Graph.ofSimpleGraph G)) :
    arrowSum (assignmentEquiv G K f)
      (S.map G.doubledVertexEquiv.toEmbedding) (T.map G.doubledVertexEquiv.toEmbedding) =
      arrowSum f S T := by
  rw [assignmentEquiv_eq, ← unitBidirectedNetworkIso_vertexEquiv G,
    (unitBidirectedNetworkIso G).arrowSum_assignmentEquiv]

/-- The directed capacity leaving `vertexFinset G S` in `DoubledQuiver G` equals the multigraph
cut capacity of `S` in `Graph.ofSimpleGraph G`, with no off-graph support condition on `c`. -/
theorem arrowSum_capacity_eq_edgeCutCapacity [Fintype V]
    [DecidableEq (DoubledQuiver G)] [∀ i j : DoubledQuiver G, Fintype (i ⟶ j)]
    [AddCommMonoid K] (c : Sym2 V → K) (S : Finset V) :
    arrowSum (capacity G c) (vertexFinset G S) (vertexFinset G S)ᶜ =
      (Graph.ofSimpleGraph G).edgeCutCapacity (G.ofSimpleGraphCapacity c)
        (G.toOfSimpleGraphFinset S) := by
  classical
  have hcompl : (G.toOfSimpleGraphFinset S)ᶜ.map G.doubledVertexEquiv.toEmbedding =
      (vertexFinset G S)ᶜ := by
    ext i
    rw [Finset.mem_map_equiv, Finset.mem_compl, Finset.mem_compl, G.doubledVertexEquiv_symm_apply,
      G.mem_toOfSimpleGraphFinset, mem_vertexFinset_iff]
  rw [← assignmentEquiv_bidirectedCapacity G c, ← hcompl,
    ← G.map_doubledVertexEquiv_toOfSimpleGraphFinset S, arrowSum_assignmentEquiv,
    Graph.arrowSum_bidirectedCapacity]

/-- When `c` vanishes off `G.edgeSet` away from the diagonal, the directed capacity leaving
`vertexFinset G S` in `DoubledQuiver G` equals `TauCeti.pairCutCapacity c S`. Diagonal values of
`c` may be arbitrary. -/
theorem arrowSum_capacity_eq_pairCutCapacity [Fintype V]
    [DecidableEq (DoubledQuiver G)] [∀ i j : DoubledQuiver G, Fintype (i ⟶ j)]
    [AddCommMonoid K] (c : Sym2 V → K)
    (hsupport : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0) (S : Finset V) :
    arrowSum (capacity G c) (vertexFinset G S) (vertexFinset G S)ᶜ =
      pairCutCapacity c S := by
  rw [arrowSum_capacity_eq_edgeCutCapacity, G.edgeCutCapacity_eq_pairCutCapacity c hsupport S]

/-- On the bundled network `DoubledQuiver.network G c hc`, the cut bound of `vertexFinset G S`
equals `TauCeti.pairCutCapacity c S` whenever off-diagonal capacities are supported on
`G.edgeSet`. -/
theorem cutBound_network_eq_pairCutCapacity [Fintype V]
    [DecidableEq (DoubledQuiver G)] [∀ i j : DoubledQuiver G, Fintype (i ⟶ j)]
    [AddCommGroup K] [LE K] (c : Sym2 V → K) (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p)
    (hsupport : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0) (S : Finset V) :
    cutBound (network G c hc).lower (network G c hc).upper (vertexFinset G S) =
      pairCutCapacity c S := by
  rw [network_lower, network_upper, cutBound_zero_left,
    arrowSum_capacity_eq_pairCutCapacity G c hsupport S]

/-- Excess is preserved by `DoubledQuiver.assignmentEquiv`. -/
theorem excessAt_assignmentEquiv [Fintype V] [∀ i j : DoubledQuiver G, Fintype (i ⟶ j)]
    [AddCommGroup K] (f : Assignment (Graph.ofSimpleGraph G).BidirectedHom K)
    (x : V(Graph.ofSimpleGraph G)) :
    excessAt (assignmentEquiv G K f) (G.doubledVertexEquiv x) = excessAt f x := by
  rw [assignmentEquiv_eq, ← unitBidirectedNetworkIso_vertexEquiv_apply G x,
    (unitBidirectedNetworkIso G).excessAt_assignmentEquiv]

/-- Excess at `vertex G u` under `DoubledQuiver.assignmentEquiv` agrees with excess at
`G.toOfSimpleGraphVertex u`. -/
@[simp]
theorem excessAt_assignmentEquiv_vertex [Fintype V] [∀ i j : DoubledQuiver G, Fintype (i ⟶ j)]
    [AddCommGroup K] (f : Assignment (Graph.ofSimpleGraph G).BidirectedHom K) (u : V) :
    excessAt (assignmentEquiv G K f) (vertex G u) =
      excessAt f (G.toOfSimpleGraphVertex u) := by
  rw [← G.doubledVertexEquiv_toOfSimpleGraphVertex u, excessAt_assignmentEquiv]

/-- Circulations on `(Graph.ofSimpleGraph G).BidirectedHom` correspond to circulations on
`DoubledQuiver G`. -/
@[simp]
theorem isCirculation_assignmentEquiv_iff [Fintype V] [∀ i j : DoubledQuiver G, Fintype (i ⟶ j)]
    [AddCommGroup K] (f : Assignment (Graph.ofSimpleGraph G).BidirectedHom K) :
    IsCirculation (assignmentEquiv G K f) ↔ IsCirculation f := by
  rw [assignmentEquiv_eq, (unitBidirectedNetworkIso G).isCirculation_assignmentEquiv_iff]

end CutAndExcess

section Flows

variable {V : Type u} {K : Type w} (G : SimpleGraph V)
variable [Fintype V] [∀ i j : DoubledQuiver G, Fintype (i ⟶ j)]
variable [AddCommGroup K] [Preorder K]

-- `SimpleGraph.instFintypeOfSimpleGraphVertexSet` is noncomputable, so passing it as a `Type`
-- argument to `Network.Iso.boundedFlowEquiv` directly would force `boundedFlowEquiv` and
-- `flowEquiv` to be noncomputable. Building the data field `toFun` directly via `assignmentEquiv`
-- and projecting the `Prop` fields from these auxiliary equivalences keeps the public equivalences
-- computable without duplicating any conservation or interval proofs.
private noncomputable def boundedFlowEquivAux
    (lo hi : Assignment (Graph.ofSimpleGraph G).BidirectedHom K) (s t : V) :
    BoundedFlow lo hi (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t) ≃
      BoundedFlow (assignmentEquiv G K lo) (assignmentEquiv G K hi)
        (vertex G s) (vertex G t) :=
  ((unitBidirectedNetworkIso G).boundedFlowEquiv lo hi
    (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t)).trans
    (BoundedFlow.congr (DFunLike.congr_fun (assignmentEquiv_eq G).symm lo)
      (DFunLike.congr_fun (assignmentEquiv_eq G).symm hi)
      (unitBidirectedNetworkIso_vertexEquiv_toOfSimpleGraphVertex G s)
      (unitBidirectedNetworkIso_vertexEquiv_toOfSimpleGraphVertex G t))

/-- Bounded `s`–`t` assignments on `(Graph.ofSimpleGraph G).BidirectedHom` correspond to bounded
assignments between the transported bounds on `DoubledQuiver G`. -/
def boundedFlowEquiv (lo hi : Assignment (Graph.ofSimpleGraph G).BidirectedHom K) (s t : V) :
    BoundedFlow lo hi (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t) ≃
      BoundedFlow (assignmentEquiv G K lo) (assignmentEquiv G K hi)
        (vertex G s) (vertex G t) where
  toFun f :=
    { toFun := assignmentEquiv G K f.toFun
      mem_Icc := by
        simpa [boundedFlowEquivAux, assignmentEquiv_eq] using
          (boundedFlowEquivAux G lo hi s t f).mem_Icc
      conserve := by
        simpa [boundedFlowEquivAux, assignmentEquiv_eq] using
          (boundedFlowEquivAux G lo hi s t f).conserve }
  invFun f :=
    { toFun := (assignmentEquiv G K).symm f.toFun
      mem_Icc := by
        simpa [boundedFlowEquivAux, assignmentEquiv_eq] using
          ((boundedFlowEquivAux G lo hi s t).symm f).mem_Icc
      conserve := by
        simpa [boundedFlowEquivAux, assignmentEquiv_eq] using
          ((boundedFlowEquivAux G lo hi s t).symm f).conserve }
  left_inv f := BoundedFlow.ext ((assignmentEquiv G K).symm_apply_apply f.toFun)
  right_inv f := BoundedFlow.ext ((assignmentEquiv G K).apply_symm_apply f.toFun)

@[simp]
theorem boundedFlowEquiv_toFun {lo hi : Assignment (Graph.ofSimpleGraph G).BidirectedHom K}
    {s t : V} (f : BoundedFlow lo hi (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t)) :
    (boundedFlowEquiv G lo hi s t f).toFun = assignmentEquiv G K f.toFun :=
  (rfl)

@[simp]
theorem boundedFlowEquiv_symm_toFun {lo hi : Assignment (Graph.ofSimpleGraph G).BidirectedHom K}
    {s t : V}
    (f : BoundedFlow (assignmentEquiv G K lo) (assignmentEquiv G K hi) (vertex G s) (vertex G t)) :
    ((boundedFlowEquiv G lo hi s t).symm f).toFun = (assignmentEquiv G K).symm f.toFun :=
  (rfl)

private theorem boundedFlowEquiv_eq_aux
    (lo hi : Assignment (Graph.ofSimpleGraph G).BidirectedHom K) (s t : V) :
    boundedFlowEquiv G lo hi s t = boundedFlowEquivAux G lo hi s t := by
  apply Equiv.ext
  intro f
  exact BoundedFlow.ext (by simp [boundedFlowEquivAux, assignmentEquiv_eq])

@[simp]
theorem val_boundedFlowEquiv {lo hi : Assignment (Graph.ofSimpleGraph G).BidirectedHom K}
    {s t : V} (f : BoundedFlow lo hi (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t)) :
    (boundedFlowEquiv G lo hi s t f).val = f.val := by
  rw [boundedFlowEquiv_eq_aux, boundedFlowEquivAux, Equiv.trans_apply, BoundedFlow.val_congr,
    (unitBidirectedNetworkIso G).val_boundedFlowEquiv]

@[simp]
theorem val_boundedFlowEquiv_symm {lo hi : Assignment (Graph.ofSimpleGraph G).BidirectedHom K}
    {s t : V}
    (f : BoundedFlow (assignmentEquiv G K lo) (assignmentEquiv G K hi) (vertex G s) (vertex G t)) :
    ((boundedFlowEquiv G lo hi s t).symm f).val = f.val := by
  simpa only [Equiv.apply_symm_apply] using
    (val_boundedFlowEquiv G ((boundedFlowEquiv G lo hi s t).symm f)).symm

private noncomputable def flowEquivAux (c : Sym2 V → K) (s t : V) :
    Flow ((Graph.ofSimpleGraph G).bidirectedCapacity (G.ofSimpleGraphCapacity c))
        (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t) ≃
      Flow (capacity G c) (vertex G s) (vertex G t) :=
  ((unitBidirectedNetworkIso G).flowEquiv
    ((Graph.ofSimpleGraph G).bidirectedCapacity (G.ofSimpleGraphCapacity c))
    (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t)).trans
    (Flow.congr
      ((DFunLike.congr_fun (assignmentEquiv_eq G).symm _).trans
        (assignmentEquiv_bidirectedCapacity G c))
      (unitBidirectedNetworkIso_vertexEquiv_toOfSimpleGraphVertex G s)
      (unitBidirectedNetworkIso_vertexEquiv_toOfSimpleGraphVertex G t))

/-- Ordinary `s`–`t` flows for simple-graph pair capacities on
`(Graph.ofSimpleGraph G).BidirectedHom` are canonically equivalent to ordinary flows on
`DoubledQuiver G` for `DoubledQuiver.capacity G c`. -/
def flowEquiv (c : Sym2 V → K) (s t : V) :
    Flow ((Graph.ofSimpleGraph G).bidirectedCapacity (G.ofSimpleGraphCapacity c))
        (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t) ≃
      Flow (capacity G c) (vertex G s) (vertex G t) where
  toFun f :=
    { toFun := assignmentEquiv G K f.toFun
      mem_Icc := by
        simpa [flowEquivAux, assignmentEquiv_eq] using (flowEquivAux G c s t f).mem_Icc
      conserve := by
        simpa [flowEquivAux, assignmentEquiv_eq] using (flowEquivAux G c s t f).conserve
      excessAt_sink_nonneg := by
        simpa [flowEquivAux, assignmentEquiv_eq] using
          (flowEquivAux G c s t f).excessAt_sink_nonneg }
  invFun f :=
    { toFun := (assignmentEquiv G K).symm f.toFun
      mem_Icc := by
        simpa [flowEquivAux, assignmentEquiv_eq] using ((flowEquivAux G c s t).symm f).mem_Icc
      conserve := by
        simpa [flowEquivAux, assignmentEquiv_eq] using ((flowEquivAux G c s t).symm f).conserve
      excessAt_sink_nonneg := by
        simpa [flowEquivAux, assignmentEquiv_eq] using
          ((flowEquivAux G c s t).symm f).excessAt_sink_nonneg }
  left_inv f := Flow.ext ((assignmentEquiv G K).symm_apply_apply f.toFun)
  right_inv f := Flow.ext ((assignmentEquiv G K).apply_symm_apply f.toFun)

@[simp]
theorem flowEquiv_toFun {c : Sym2 V → K} {s t : V}
    (f : Flow ((Graph.ofSimpleGraph G).bidirectedCapacity (G.ofSimpleGraphCapacity c))
      (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t)) :
    (flowEquiv G c s t f).toFun = assignmentEquiv G K f.toFun :=
  (rfl)

@[simp]
theorem flowEquiv_symm_toFun {c : Sym2 V → K} {s t : V}
    (f : Flow (capacity G c) (vertex G s) (vertex G t)) :
    ((flowEquiv G c s t).symm f).toFun = (assignmentEquiv G K).symm f.toFun :=
  (rfl)

private theorem flowEquiv_eq_aux (c : Sym2 V → K) (s t : V) :
    flowEquiv G c s t = flowEquivAux G c s t := by
  apply Equiv.ext
  intro f
  exact Flow.ext (by simp [flowEquivAux, assignmentEquiv_eq])

@[simp]
theorem val_flowEquiv {c : Sym2 V → K} {s t : V}
    (f : Flow ((Graph.ofSimpleGraph G).bidirectedCapacity (G.ofSimpleGraphCapacity c))
      (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t)) :
    (flowEquiv G c s t f).val = f.val := by
  rw [flowEquiv_eq_aux, flowEquivAux, Equiv.trans_apply, Flow.val_congr,
    (unitBidirectedNetworkIso G).val_flowEquiv]

@[simp]
theorem val_flowEquiv_symm {c : Sym2 V → K} {s t : V}
    (f : Flow (capacity G c) (vertex G s) (vertex G t)) :
    ((flowEquiv G c s t).symm f).val = f.val := by
  simpa only [Equiv.apply_symm_apply] using (val_flowEquiv G ((flowEquiv G c s t).symm f)).symm

/-- `DoubledQuiver.flowEquiv` preserves and reflects maximality of flows. -/
@[simp]
theorem isMaximum_flowEquiv_iff {c : Sym2 V → K} {s t : V}
    (f : Flow ((Graph.ofSimpleGraph G).bidirectedCapacity (G.ofSimpleGraphCapacity c))
      (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t)) :
    (flowEquiv G c s t f).IsMaximum ↔ f.IsMaximum := by
  rw [flowEquiv_eq_aux, flowEquivAux, Equiv.trans_apply, Flow.isMaximum_congr_iff,
    (unitBidirectedNetworkIso G).isMaximum_flowEquiv_iff]

/-- **Weak duality on `DoubledQuiver G`.** When off-diagonal capacities vanish away from
`G.edgeSet`, every flow on `DoubledQuiver G` from `vertex G s` to `vertex G t` has value at most
`TauCeti.pairCutCapacity c S` for every cut `S` separating `s` from `t`. -/
theorem val_le_pairCutCapacity [AddLeftMono K] {c : Sym2 V → K} {s t : V}
    (f : Flow (capacity G c) (vertex G s) (vertex G t))
    (hsupport : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0)
    {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    f.val ≤ pairCutCapacity c S := by
  rw [← val_flowEquiv_symm G f]
  exact ((flowEquiv G c s t).symm f).val_le_pairCutCapacity hsupport hs ht

end Flows

section MaxFlowMinCut

variable {V : Type u} {K : Type w} (G : SimpleGraph V)
variable [Fintype V] [∀ i j : DoubledQuiver G, Fintype (i ⟶ j)]
variable [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]

/-- **Undirected max-flow/min-cut on `DoubledQuiver G`, with integrality.** Let pair capacities `c`
be nonnegative on `G.edgeSet` and vanish off `G.edgeSet` away from the diagonal. For distinct
vertices `s` and `t`, there is an acyclic flow on `DoubledQuiver G` from `vertex G s` to
`vertex G t` whose value equals `TauCeti.pairCutCapacity c S` for some separating cut `S`. If all
edge capacities lie in an additive subgroup `A`, all arrow values of the flow can be chosen in `A`
as well. -/
theorem exists_flow_val_eq_pairCutCapacity_mem (c : Sym2 V → K) {s t : V} (hst : s ≠ t)
    (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p)
    (hsupport : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0)
    (A : AddSubgroup K) (hcA : ∀ p ∈ G.edgeSet, c p ∈ A) :
    ∃ f : Flow (capacity G c) (vertex G s) (vertex G t),
      f.toFun.IsAcyclic ∧
      (∀ ⦃i j : DoubledQuiver G⦄ (e : i ⟶ j), f.toFun e ∈ A) ∧
      ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ f.val = pairCutCapacity c S := by
  obtain ⟨f, hfacyc, hfA, S, hsS, htS, hval⟩ :=
    G.exists_flow_val_eq_pairCutCapacity_mem c hst hc hsupport A hcA
  refine ⟨flowEquiv G c s t f, ?_, ?_, S, hsS, htS, ?_⟩
  · rwa [flowEquiv_toFun, isAcyclic_assignmentEquiv_iff]
  · rwa [flowEquiv_toFun, forall_assignmentEquiv_mem_iff]
  · rwa [val_flowEquiv]

/-- **Undirected max-flow/min-cut on `DoubledQuiver G`.** For pair capacities nonnegative on
`G.edgeSet` and supported off the diagonal on `G.edgeSet`, distinct vertices admit an acyclic flow
on `DoubledQuiver G` and a separating cut of equal value and pair capacity. -/
theorem exists_flow_val_eq_pairCutCapacity (c : Sym2 V → K) {s t : V} (hst : s ≠ t)
    (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p)
    (hsupport : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0) :
    ∃ f : Flow (capacity G c) (vertex G s) (vertex G t),
      f.toFun.IsAcyclic ∧
      ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ f.val = pairCutCapacity c S := by
  obtain ⟨f, hfacyc, -, hS⟩ :=
    exists_flow_val_eq_pairCutCapacity_mem G c hst hc hsupport ⊤ fun _ _ ↦ AddSubgroup.mem_top _
  exact ⟨f, hfacyc, hS⟩

end MaxFlowMinCut

end TauCeti.DoubledQuiver
