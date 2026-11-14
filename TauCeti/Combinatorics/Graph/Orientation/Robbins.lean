/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Characterization
public import TauCeti.Combinatorics.Graph.Orientation.StronglyConnected
public import TauCeti.Combinatorics.Graph.Orientation.Subgraph

/-!
# Robbins' strong orientation theorem

This file proves Robbins' theorem for finite multigraphs: a multigraph admits a strongly
connected orientation exactly when it is `2`-edge-connected. The construction directs every ear
of a vertex-starting ear decomposition along its underlying walk. Directing an open ear from one
old endpoint to the other, or a closed ear cyclically from its base back to itself, preserves
strong connectivity.

Loops and parallel edges retain their identities throughout. Consequently the theorem includes
one-vertex graphs with loops and the two-vertex graph with two parallel edges. The empty graph is
included as well: its orientation is strongly connected vacuously.

## References

* H. E. Robbins, *A theorem on graphs, with an application to a problem of traffic control*,
  Amer. Math. Monthly 46 (1939), 281--283.
-/

public section

open Set
open TauCeti

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G H : Graph α β}

namespace Ear

/-- Orient the graph traced by an ear in the order of its underlying walk. -/
noncomputable def toGraphOrientation (ear : G.Ear H) : ear.toGraph.Orientation :=
  (ear.toWalk.2.2.orientation ear.isTrail).restrict ear.toGraph_le

/-- The underlying walk of an ear, restricted to its traced graph, follows the canonical
orientation of that trace. -/
theorem followsOrientation_toGraphOrientation (ear : G.Ear H) :
    (ear.toWalk.2.2.transfer ear.toGraph_le fun e he ↦
      ear.edges_subset_edgeSet_toGraph e he).FollowsOrientation
        ear.toGraphOrientation := by
  exact (ear.toWalk.2.2.followsOrientation_orientation ear.isTrail).transfer
    ear.toGraph_le ear.edges_subset_edgeSet_toGraph

end Ear

namespace Orientation

/-- Extend an orientation over an adjoined ear by directing every new edge in the order of the
ear's underlying walk. -/
noncomputable def addEar (o : H.Orientation) (ear : G.Ear H) : ear.add.Orientation :=
  (o.union ear.toGraphOrientation ear.compatible).restrict ear.add_eq_union.le

@[simp]
theorem restrict_addEar_base (o : H.Orientation) (ear : G.Ear H) :
    (o.addEar ear).restrict ear.base_le_add = o := by
  rw [addEar, restrict_restrict]
  exact restrict_union_left ..

@[simp]
theorem restrict_addEar_toGraph (o : H.Orientation) (ear : G.Ear H) :
    (o.addEar ear).restrict ear.toGraph_le_add = ear.toGraphOrientation := by
  rw [addEar, restrict_restrict]
  exact restrict_union_right ear.disjoint_edgeSet_toGraph

/-- Every vertex traced by an ear lies on the directed ear, so it is reachable from the ear's
start and reaches the ear's end. -/
private theorem nonempty_arrowWalk_of_mem_toGraph (o : H.Orientation) (ear : G.Ear H)
    (x : ear.add.vertexSet) (hx : x.1 ∈ V(ear.toGraph)) :
    Nonempty (ArrowWalk (o.addEar ear).Hom
        (Set.inclusion ear.base_le_add.vertexSet_mono ⟨ear.toWalk.1, ear.toWalk_fst_mem⟩) x) ∧
      Nonempty (ArrowWalk (o.addEar ear).Hom x
        (Set.inclusion ear.base_le_add.vertexSet_mono ⟨ear.toWalk.2.1, ear.toWalk_snd_mem⟩)) := by
  let p := ear.toWalk.2.2
  let q := p.transfer ear.toGraph_le ear.edges_subset_edgeSet_toGraph
  have hq : q.FollowsOrientation ear.toGraphOrientation := by
    simpa only [p, q] using ear.followsOrientation_toGraphOrientation
  have hqAdd : (q.mapLe ear.toGraph_le_add).FollowsOrientation (o.addEar ear) := by
    apply (Walk.followsOrientation_mapLe_iff ear.toGraph_le_add q (o.addEar ear)).2
    simpa only [restrict_addEar_toGraph] using hq
  let directed := (q.mapLe ear.toGraph_le_add).toOriented hqAdd
    (ear.base_le_add.vertexSet_mono ear.toWalk_fst_mem)
  have hxDirected : x ∈ directed.vertices := by
    have hxSupport : x.1 ∈ directed.vertices.unattach := by
      rw [Walk.vertices_toOriented]
      simpa only [Walk.support_mapLe_eq_support, q, Walk.support_transfer,
        Ear.vertexSet_toGraph, Set.mem_ofPred_eq] using hx
    obtain ⟨_, hxmem⟩ := List.mem_unattach.1 hxSupport
    simpa using hxmem
  obtain ⟨r, s, -⟩ := @Quiver.Path.exists_eq_comp_of_mem_vertices
    ear.add.vertexSet ⟨(o.addEar ear).Hom⟩ _ _ directed x hxDirected
  exact ⟨⟨r⟩, ⟨s⟩⟩

/-- Directed walks of the base orientation remain directed walks after adjoining an ear. -/
private theorem nonempty_arrowWalk_addEar_of_base (o : H.Orientation) (ear : G.Ear H)
    {a b : H.vertexSet} (r : ArrowWalk o.Hom a b) :
    Nonempty (ArrowWalk (o.addEar ear).Hom (Set.inclusion ear.base_le_add.vertexSet_mono a)
      (Set.inclusion ear.base_le_add.vertexSet_mono b)) := by
  rw [← restrict_addEar_base o ear] at r
  exact (o.addEar ear).nonempty_arrowWalk_of_restrict ear.base_le_add r

/-- Every vertex of the extended graph is reachable from a base vertex and reaches a base
vertex. -/
private theorem exists_arrowWalks_base (o : H.Orientation) (ear : G.Ear H)
    (x : ear.add.vertexSet) :
    ∃ a b : H.vertexSet,
      Nonempty (ArrowWalk (o.addEar ear).Hom (Set.inclusion ear.base_le_add.vertexSet_mono a) x) ∧
        Nonempty (ArrowWalk (o.addEar ear).Hom x
          (Set.inclusion ear.base_le_add.vertexSet_mono b)) := by
  have hx : x.1 ∈ V(H) ∪ V(ear.toGraph) := by
    rw [← ear.vertexSet_add]
    exact x.2
  rcases hx with hx | hx
  · exact ⟨⟨x, hx⟩, ⟨x, hx⟩, ⟨.nil x⟩, ⟨.nil x⟩⟩
  · exact ⟨_, _, nonempty_arrowWalk_of_mem_toGraph o ear x hx⟩

/-- Directing an ear from its old start to its old end preserves strong connectivity. -/
theorem isStronglyConnected_addEar (o : H.Orientation) (ear : G.Ear H)
    (hH : @Quiver.IsStronglyConnected H.vertexSet ⟨o.Hom⟩) :
    @Quiver.IsStronglyConnected ear.add.vertexSet ⟨(o.addEar ear).Hom⟩ := by
  intro x y
  obtain ⟨-, a, -, ⟨r⟩⟩ := exists_arrowWalks_base o ear x
  obtain ⟨b, -, ⟨t⟩, -⟩ := exists_arrowWalks_base o ear y
  obtain ⟨s⟩ := hH a b
  obtain ⟨s'⟩ := nonempty_arrowWalk_addEar_of_base o ear s
  exact ⟨(r.comp s').comp t⟩

end Orientation

namespace EarDecomposition

/-- A vertex-starting ear decomposition determines a strongly connected orientation of its
final graph. -/
theorem exists_stronglyConnected_orientation (d : G.EarDecomposition H)
    (hd : d.IsVertexStart) :
    ∃ o : H.Orientation, @Quiver.IsStronglyConnected H.vertexSet ⟨o.Hom⟩ := by
  rw [← d.graphAfter_last]
  exact d.graphAfter_induction
    (P := fun K ↦ ∃ o : K.Orientation, @Quiver.IsStronglyConnected K.vertexSet ⟨o.Hom⟩)
    (by
      rw [isVertexStart_iff] at hd
      obtain ⟨x, hx⟩ := hd
      rw [hx]
      let o := Orientation.ofEdgeEnds (Graph.noEdge {x.1} β)
      refine ⟨o, ?_⟩
      intro a b
      have ha := a.2
      have hb := b.2
      simp only [vertexSet_noEdge, Set.mem_singleton_iff] at ha hb
      have hab : a = b := Subtype.ext (ha.trans hb.symm)
      subst b
      exact ⟨TauCeti.ArrowWalk.nil a⟩)
    (fun i hi ↦ by
      rw [← d.earAt_fst i] at hi
      obtain ⟨o, ho⟩ := hi
      exact ⟨o.addEar (d.earAt i).2, o.isStronglyConnected_addEar (d.earAt i).2 ho⟩)
    (Fin.last d.length)

end EarDecomposition

/-- The sufficient direction of Robbins' theorem: a `2`-edge-connected multigraph with finitely
many edges admits a strongly connected orientation. -/
theorem IsEdgeConnected.exists_stronglyConnected_orientation [Finite E(G)]
    (hG : G.IsEdgeConnected 2) :
    ∃ o : G.Orientation, @Quiver.IsStronglyConnected G.vertexSet ⟨o.Hom⟩ := by
  cases isEmpty_or_nonempty G.vertexSet with
  | inl h =>
      let o := Orientation.ofEdgeEnds G
      exact ⟨o, fun x ↦ isEmptyElim x⟩
  | inr h =>
      obtain ⟨d, hd⟩ :=
        (isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition (G := G)).1 hG
      exact d.exists_stronglyConnected_orientation hd

/-- **Robbins' theorem.** A multigraph with finitely many edges is `2`-edge-connected exactly
when it admits a strongly connected orientation. -/
theorem isEdgeConnected_two_iff_exists_stronglyConnected_orientation
    [Finite E(G)] :
    G.IsEdgeConnected 2 ↔
      ∃ o : G.Orientation, @Quiver.IsStronglyConnected G.vertexSet ⟨o.Hom⟩ :=
  ⟨IsEdgeConnected.exists_stronglyConnected_orientation,
    isEdgeConnected_two_of_exists_stronglyConnected_orientation⟩

end Graph

namespace SimpleGraph

open TauCeti

variable {V : Type u} {G : SimpleGraph V}

/-- **Robbins' theorem for simple graphs.** A finite simple graph is `2`-edge-connected exactly
when its doubled quiver admits a strongly connected dart orientation. -/
theorem isEdgeConnected_two_iff_exists_stronglyConnected_orientation [Finite V] :
    G.IsEdgeConnected 2 ↔ ∃ o : DoubledQuiver.Orientation G,
      Quiver.IsStronglyConnected (DoubledQuiver.OrientedQuiver G o) := by
  constructor
  · intro hG
    obtain ⟨o, ho⟩ := Graph.IsEdgeConnected.exists_stronglyConnected_orientation
      ((Graph.isEdgeConnected_ofSimpleGraph_iff G 2).2 hG)
    refine ⟨o.toDartOrientation, ?_⟩
    exact o.isStronglyConnected_orientedQuiver_iff.mpr ho
  · rintro ⟨o, ho⟩
    exact SimpleGraph.isEdgeConnected_two_of_exists_stronglyConnected_orientation ⟨o, ho⟩

end SimpleGraph
