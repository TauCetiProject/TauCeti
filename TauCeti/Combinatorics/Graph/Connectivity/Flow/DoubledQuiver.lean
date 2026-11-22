/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Flow.Basic
public import TauCeti.Combinatorics.Network.Isomorphism.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Basic

/-!
# Bidirected simple graphs as doubled-quiver networks

The bidirected network of a multigraph has one arrow in each direction for every nonloop edge and
one arrow for every loop. For the multigraph `Graph.ofSimpleGraph G`, this arrow family is
canonically the existing doubled quiver `TauCeti.DoubledQuiver G`.

This file packages that identification as an isomorphism of bounded networks. Consequently it
preserves capacities, assignments, excess, flows, and directed walks through the generic network
isomorphism API. Parallel edges and loops remain part of the general bidirected-network
constructor; the doubled-quiver comparison specializes to simple graphs.

## Main definitions

* `Graph.bidirectedNetwork`: the zero-lower-bound network of a weighted multigraph.
* `SimpleGraph.doubledNetwork`: the same construction on the doubled quiver of a simple graph.
* `SimpleGraph.bidirectedDoubledIso`: the canonical network isomorphism between the bidirected
  network of `Graph.ofSimpleGraph G` and `G.doubledNetwork`.
-/

public section

open TauCeti

universe u v w

namespace Graph

variable {V : Type u} {E : Type v} {K : Type w} [Zero K] [LE K]

/-- The bidirected network of a weighted multigraph. Both directions of a nonloop edge have the
edge's capacity, while a loop gives one loop arrow with that capacity. -/
@[expose, reducible]
def bidirectedNetwork (G : Graph V E) (c : E(G) → K) (hc : 0 ≤ c) : Network K V(G) :=
  Network.ofCapacity G.BidirectedHom (G.bidirectedCapacity c) fun {x y} a ↦ by
    rw [G.bidirectedCapacity_apply]
    exact hc ⟨a.1, a.2.edge_mem⟩

/-- The arrow family of the bidirected network is the bidirected arrow family of the graph. -/
@[simp]
theorem bidirectedNetwork_Hom (G : Graph V E) (c : E(G) → K) (hc : 0 ≤ c) :
    (G.bidirectedNetwork c hc).Hom = G.BidirectedHom :=
  (rfl)

/-- Every lower bound in a bidirected network is zero. -/
@[simp]
theorem bidirectedNetwork_lower (G : Graph V E) (c : E(G) → K) (hc : 0 ≤ c)
    {x y : V(G)} (a : (G.bidirectedNetwork c hc).Hom x y) :
    (G.bidirectedNetwork c hc).lower a = 0 :=
  (rfl)

/-- The upper bound on a bidirected arrow is its edge's capacity. -/
theorem bidirectedNetwork_upper (G : Graph V E) (c : E(G) → K) (hc : 0 ≤ c)
    {x y : V(G)} (a : (G.bidirectedNetwork c hc).Hom x y) :
    (G.bidirectedNetwork c hc).upper a = G.bidirectedCapacity c a :=
  (rfl)

end Graph

namespace SimpleGraph

variable {V : Type u} {K : Type w} (G : SimpleGraph V)

/-- The actual vertices of `Graph.ofSimpleGraph G` are canonically the vertices of the doubled
quiver of `G`. -/
abbrev bidirectedDoubledVertexEquiv :
    (Graph.ofSimpleGraph G).vertexSet ≃ DoubledQuiver G where
  toFun x := DoubledQuiver.vertex G x.1
  invFun x := ⟨(DoubledQuiver.vertexEquiv G).symm x, by
    rw [Graph.vertexSet_ofSimpleGraph]
    exact Set.mem_univ _⟩
  left_inv x := by
    apply Subtype.ext
    exact DoubledQuiver.vertexEquiv_symm_vertex G x.1
  right_inv := DoubledQuiver.vertexEquiv_symm_apply G

/-- The vertex equivalence sends an actual vertex to the corresponding doubled-quiver vertex. -/
@[simp]
theorem bidirectedDoubledVertexEquiv_apply
    (x : (Graph.ofSimpleGraph G).vertexSet) :
    G.bidirectedDoubledVertexEquiv x = DoubledQuiver.vertex G x.1 :=
  (rfl)

/-- The inverse vertex equivalence sends a doubled-quiver vertex to the corresponding actual
vertex of `Graph.ofSimpleGraph G`. -/
theorem bidirectedDoubledVertexEquiv_symm_vertex (x : V) :
    G.bidirectedDoubledVertexEquiv.symm (DoubledQuiver.vertex G x) =
      G.toOfSimpleGraphVertex x := by
  apply Subtype.ext
  calc
    (G.bidirectedDoubledVertexEquiv.symm (DoubledQuiver.vertex G x)).1 =
        (DoubledQuiver.vertexEquiv G).symm (DoubledQuiver.vertex G x) := rfl
    _ = x := DoubledQuiver.vertexEquiv_symm_vertex G x
    _ = (G.toOfSimpleGraphVertex x).1 := (G.toOfSimpleGraphVertex_val x).symm

/-- A bidirected arrow of `Graph.ofSimpleGraph G` is canonically the corresponding arrow of the
doubled quiver. -/
def bidirectedDoubledHomEquiv (x y : (Graph.ofSimpleGraph G).vertexSet) :
    (Graph.ofSimpleGraph G).BidirectedHom x y ≃
      (G.bidirectedDoubledVertexEquiv x ⟶ G.bidirectedDoubledVertexEquiv y) where
  toFun a := DoubledQuiver.arrow G ((Graph.ofSimpleGraph_adj_iff x.1 y.1).mp a.2.adj)
  invFun a := ⟨s(x.1, y.1), by
    have hxy : G.Adj x.1 y.1 := by
      simpa only [bidirectedDoubledVertexEquiv_apply,
        DoubledQuiver.vertexEquiv_symm_vertex] using a.down
    simpa only [Graph.ofSimpleGraph_isLink, SimpleGraph.mem_edgeSet, true_and] using hxy⟩
  left_inv a := by
    apply Subtype.ext
    exact a.2.1.symm
  right_inv _ := Subsingleton.elim _ _

/-- The arrow equivalence sends a directed incidence to the doubled-quiver arrow induced by the
same adjacency. -/
theorem bidirectedDoubledHomEquiv_apply
    {x y : (Graph.ofSimpleGraph G).vertexSet}
    (a : (Graph.ofSimpleGraph G).BidirectedHom x y) :
    G.bidirectedDoubledHomEquiv x y a =
      DoubledQuiver.arrow G ((Graph.ofSimpleGraph_adj_iff x.1 y.1).mp a.2.adj) :=
  (rfl)

/-- The inverse arrow equivalence recovers the unordered pair of its source and target. -/
theorem bidirectedDoubledHomEquiv_symm_apply_val
    {x y : (Graph.ofSimpleGraph G).vertexSet}
    (a : G.bidirectedDoubledVertexEquiv x ⟶ G.bidirectedDoubledVertexEquiv y) :
    ((G.bidirectedDoubledHomEquiv x y).symm a).1 = s(x.1, y.1) :=
  (rfl)

/-- Capacities on the doubled quiver, indexed by unordered pairs of graph vertices. Only values
on edges are used because arrows exist exactly between adjacent vertices. -/
def doubledCapacity (c : Sym2 V → K) :
    Assignment (fun x y : DoubledQuiver G ↦ x ⟶ y) K :=
  fun {x y} _ ↦ c s((DoubledQuiver.vertexEquiv G).symm x,
    (DoubledQuiver.vertexEquiv G).symm y)

/-- A doubled-quiver arrow carries the capacity of the unordered pair of its endpoints. -/
@[simp]
theorem doubledCapacity_apply (c : Sym2 V → K) {x y : DoubledQuiver G} (a : x ⟶ y) :
    G.doubledCapacity c a = c s((DoubledQuiver.vertexEquiv G).symm x,
      (DoubledQuiver.vertexEquiv G).symm y) :=
  (rfl)

/-- The doubled-quiver arrow induced by an adjacency carries the capacity of that edge. -/
theorem doubledCapacity_arrow (c : Sym2 V → K) {x y : V} (h : G.Adj x y) :
    G.doubledCapacity c (DoubledQuiver.arrow G h) = c s(x, y) :=
  by simp only [doubledCapacity_apply, DoubledQuiver.vertexEquiv_symm_vertex]

variable [Zero K] [LE K]

/-- Pair capacities on the edges of a simple graph equip its doubled quiver with zero lower
bounds. Values away from the graph's edge set do not affect this network. -/
@[expose, reducible]
def doubledNetwork (c : Sym2 V → K) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) :
    Network K (DoubledQuiver G) :=
  Network.ofCapacity (fun x y : DoubledQuiver G ↦ x ⟶ y) (G.doubledCapacity c) fun
    {x y} a ↦ by
      rw [G.doubledCapacity_apply]
      exact hc s((DoubledQuiver.vertexEquiv G).symm x,
        (DoubledQuiver.vertexEquiv G).symm y) (by
          simpa only [SimpleGraph.mem_edgeSet] using a.down)

/-- The doubled network uses the existing doubled-quiver arrow family. -/
@[simp]
theorem doubledNetwork_Hom (c : Sym2 V → K) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) :
    (G.doubledNetwork c hc).Hom = fun x y : DoubledQuiver G ↦ x ⟶ y :=
  (rfl)

/-- Every lower bound in the doubled network is zero. -/
@[simp]
theorem doubledNetwork_lower (c : Sym2 V → K) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e)
    {x y : DoubledQuiver G} (a : (G.doubledNetwork c hc).Hom x y) :
    (G.doubledNetwork c hc).lower a = 0 :=
  (rfl)

/-- The upper bound on a doubled-quiver arrow is its pair capacity. -/
theorem doubledNetwork_upper (c : Sym2 V → K) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e)
    {x y : DoubledQuiver G} (a : (G.doubledNetwork c hc).Hom x y) :
    (G.doubledNetwork c hc).upper a = G.doubledCapacity c a :=
  (rfl)

/-- The weighted bidirected network of `Graph.ofSimpleGraph G` is the doubled-quiver network of
`G`. The isomorphism fixes the underlying graph vertices and sends each directed incidence of an
edge to the arrow induced by the same adjacency. -/
def bidirectedDoubledIso (c : Sym2 V → K) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) :
    Network.Iso
      ((Graph.ofSimpleGraph G).bidirectedNetwork (G.ofSimpleGraphCapacity c)
        (fun e : (Graph.ofSimpleGraph G).edgeSet ↦ by
          rw [G.ofSimpleGraphCapacity_apply]
          exact hc e.1 (by simpa using e.2)))
      (G.doubledNetwork c hc) where
  vertexEquiv := G.bidirectedDoubledVertexEquiv
  homEquiv := G.bidirectedDoubledHomEquiv
  map_lower := fun _ ↦ rfl
  map_upper := fun {x y} a ↦ by
    rw [doubledNetwork_upper, Graph.bidirectedNetwork_upper, doubledCapacity_apply,
      Graph.bidirectedCapacity_apply, G.ofSimpleGraphCapacity_apply]
    simp only [bidirectedDoubledVertexEquiv_apply, DoubledQuiver.vertexEquiv_symm_vertex]
    rw [a.2.1]

/-- Transporting the bidirected capacity assignment gives the doubled-quiver capacity assignment,
so the generic flow transport along `bidirectedDoubledIso` has the expected target capacity. -/
@[simp]
theorem assignmentEquiv_bidirectedCapacity
    (c : Sym2 V → K) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) :
    (G.bidirectedDoubledIso c hc).assignmentEquiv K
        ((Graph.ofSimpleGraph G).bidirectedCapacity (G.ofSimpleGraphCapacity c)) =
      G.doubledCapacity c :=
  (G.bidirectedDoubledIso c hc).assignmentEquiv_upper

/-- The network isomorphism sends an actual vertex to the corresponding doubled-quiver vertex. -/
@[simp]
theorem bidirectedDoubledIso_vertexEquiv_apply
    (c : Sym2 V → K) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e)
    (x : (Graph.ofSimpleGraph G).vertexSet) :
    (G.bidirectedDoubledIso c hc).vertexEquiv x = DoubledQuiver.vertex G x.1 :=
  G.bidirectedDoubledVertexEquiv_apply x

/-- The network isomorphism sends a bidirected incidence to the doubled-quiver arrow induced by
the same adjacency. -/
@[simp]
theorem bidirectedDoubledIso_homEquiv_apply
    (c : Sym2 V → K) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e)
    {x y : (Graph.ofSimpleGraph G).vertexSet}
    (a : (Graph.ofSimpleGraph G).BidirectedHom x y) :
    (G.bidirectedDoubledIso c hc).homEquiv x y a =
      @Quiver.homOfEq (DoubledQuiver G) inferInstance _ _ _ _
        (DoubledQuiver.arrow G ((Graph.ofSimpleGraph_adj_iff x.1 y.1).mp a.2.adj))
        (G.bidirectedDoubledIso_vertexEquiv_apply c hc x).symm
        (G.bidirectedDoubledIso_vertexEquiv_apply c hc y).symm :=
  Subsingleton.elim _ _

end SimpleGraph
