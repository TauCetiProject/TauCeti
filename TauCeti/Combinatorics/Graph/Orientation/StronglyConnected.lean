/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.EdgeConnectivity
public import TauCeti.Combinatorics.Graph.Orientation.OfSimpleGraph
public import TauCeti.Combinatorics.Graph.Orientation.Walk
public import TauCeti.Combinatorics.Network.DirectedCycle

/-!
# Strong orientations and edge connectivity

This file proves the necessary direction of Robbins' theorem: a multigraph admitting a strongly
connected orientation is `2`-edge-connected. More generally, an orientation that is strongly
connected within each undirected connected component leaves no bridge in the graph.

The argument retains edge identities. Every oriented edge of a strongly connected component lies
on a directed cycle; forgetting its direction gives an undirected cycle through the same edge, so
that edge cannot be a bridge. The result requires no finiteness assumptions and includes loops,
parallel edges, disconnected graphs in the componentwise statement, and graphs with no vertices.

## References

* H. E. Robbins, *A theorem on graphs, with an application to a problem of traffic control*,
  Amer. Math. Monthly 46 (1939), 281--283.
-/

public section

namespace Graph.Orientation

open TauCeti

universe u v

variable {V : Type u} {E : Type v} {G : Graph V E}

/-- If the arrow chosen for an edge by an orientation lies on a directed cycle, the underlying
edge is not a bridge. -/
theorem not_isBridge_of_liesOnCycle (o : G.Orientation) (e : E(G))
    (hcycle : ArrowWalk.LiesOnCycle (o.arrow e)) : ¬ G.IsBridge e.1 := by
  rw [ArrowWalk.liesOnCycle_def] at hcycle
  rintro he
  obtain ⟨x, p, hp, hep⟩ := hcycle
  have hcycle' : (o.forgetWalk p).IsCycle := (o.isCycle_forgetWalk_iff p).2 hp
  apply he.notMem_edges_of_isCycle hcycle'
  rw [o.edges_forgetWalk]
  exact List.mem_map.mpr ⟨⟨_, _, o.arrow e⟩, hep, by simp⟩

/-- If the head of an oriented edge can reach its tail in the orientation, the edge is not a
bridge. -/
theorem not_isBridge_of_nonempty_returnWalk (o : G.Orientation) (e : E(G))
    (hreturn : Nonempty (ArrowWalk o.Hom (o.head e) (o.tail e))) : ¬ G.IsBridge e.1 :=
  o.not_isBridge_of_liesOnCycle e
    ((ArrowWalk.liesOnCycle_iff_nonempty (o.arrow e)).2 hreturn)

/-- An orientation that is strongly connected within every connected component has no bridge.

The hypothesis only asks for a directed walk when the two vertices are already connected in the
underlying undirected graph, so the statement also applies to disconnected graphs. -/
theorem forall_not_isBridge_of_componentwiseStrong (o : G.Orientation)
    (hstrong : ∀ x y : V(G), G.Reachable x y → Nonempty (ArrowWalk o.Hom x y)) :
    ∀ e, ¬ G.IsBridge e := by
  intro e he
  let e' : E(G) := ⟨e, he.mem_edgeSet⟩
  exact o.not_isBridge_of_nonempty_returnWalk e'
    (hstrong (o.head e') (o.tail e') (o.arrow e').isLink.reachable.symm) he

/-- Every edge of a graph with a strongly connected orientation is not a bridge. -/
theorem forall_not_isBridge (o : G.Orientation)
    (hstrong : @Quiver.IsStronglyConnected V(G) ⟨o.Hom⟩) :
    ∀ e, ¬ G.IsBridge e :=
  o.forall_not_isBridge_of_componentwiseStrong fun x y _ ↦ hstrong x y

/-- The necessary direction of Robbins' theorem: a strongly connected orientation forces
`2`-edge-connectivity. No finiteness or nonemptiness assumption is needed. -/
theorem isEdgeConnected_two (o : G.Orientation)
    (hstrong : @Quiver.IsStronglyConnected V(G) ⟨o.Hom⟩) : G.IsEdgeConnected 2 := by
  rw [Graph.isEdgeConnected_two_iff_forall_reachable_and_forall_not_isBridge]
  refine ⟨?_, o.forall_not_isBridge hstrong⟩
  intro x hx y hy
  exact Graph.reachable_def.mpr ⟨hx, (hstrong ⟨x, hx⟩ ⟨y, hy⟩).map o.forgetWalk⟩

end Graph.Orientation

namespace Graph

open TauCeti

universe u v

variable {V : Type u} {E : Type v} {G : Graph V E}

/-- If a multigraph admits a strongly connected orientation, it is `2`-edge-connected. -/
theorem isEdgeConnected_two_of_exists_stronglyConnected_orientation
    (h : ∃ o : G.Orientation, @Quiver.IsStronglyConnected V(G) ⟨o.Hom⟩) :
    G.IsEdgeConnected 2 := by
  obtain ⟨o, ho⟩ := h
  exact o.isEdgeConnected_two ho

end Graph

namespace SimpleGraph

open TauCeti

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- If a simple graph admits a strongly connected dart orientation, it is `2`-edge-connected. -/
theorem isEdgeConnected_two_of_exists_stronglyConnected_orientation
    (h : ∃ o : TauCeti.DoubledQuiver.Orientation G,
      Quiver.IsStronglyConnected (TauCeti.DoubledQuiver.OrientedQuiver G o)) :
    G.IsEdgeConnected 2 := by
  obtain ⟨o, ho⟩ := h
  let o' : (Graph.ofSimpleGraph G).Orientation := G.graphOrientationEquiv.symm o
  have ho_eq : o'.toDartOrientation = o := by
    rw [← G.graphOrientationEquiv_apply]
    exact G.graphOrientationEquiv.apply_symm_apply o
  have ho' : @Quiver.IsStronglyConnected (Graph.ofSimpleGraph G).vertexSet ⟨o'.Hom⟩ := by
    apply (o'.isStronglyConnected_orientedQuiver_iff).1
    rw [ho_eq]
    exact ho
  exact (Graph.isEdgeConnected_ofSimpleGraph_iff G 2).mp (o'.isEdgeConnected_two ho')

end SimpleGraph
