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
  (ear.toWalk.2.2.orientation ear.edges_nodup).restrict ear.toGraph_le

/-- The underlying walk of an ear, restricted to its traced graph, follows the canonical
orientation of that trace. -/
theorem followsOrientation_toGraphOrientation (ear : G.Ear H) :
    (ear.toWalk.2.2.transfer ear.toGraph_le fun e he ↦
      (by rw [ear.edgeSet_toGraph]; exact he)).FollowsOrientation
        ear.toGraphOrientation := by
  exact (ear.toWalk.2.2.followsOrientation_orientation ear.edges_nodup).transfer
    ear.toGraph_le fun e he ↦ by
      rw [ear.edgeSet_toGraph]
      exact he

end Ear

namespace Orientation

private noncomputable def unionOfEq {K : Graph α β} (o₁ : H.Orientation)
    {L : Graph α β} (o₂ : L.Orientation) (h : H.Compatible L) (hK : K = h.union) :
    K.Orientation := by
  rw [hK]
  exact o₁.union o₂ h

private theorem restrict_unionOfEq_left {K L : Graph α β} (o₁ : H.Orientation)
    (o₂ : L.Orientation) (h : H.Compatible L) (hK : K = h.union) (hH : H ≤ K) :
    (unionOfEq o₁ o₂ h hK).restrict hH = o₁ := by
  subst K
  exact restrict_union_left

private theorem restrict_unionOfEq_right {K L : Graph α β} (o₁ : H.Orientation)
    (o₂ : L.Orientation) (h : H.Compatible L) (hK : K = h.union) (hL : L ≤ K)
    (hE : Disjoint E(H) E(L)) : (unionOfEq o₁ o₂ h hK).restrict hL = o₂ := by
  subst K
  exact restrict_union_right hE

/-- Extend an orientation over an adjoined ear by directing every new edge in the order of the
ear's underlying walk. -/
noncomputable def addEar (o : H.Orientation) (ear : G.Ear H) : ear.add.Orientation :=
  unionOfEq o ear.toGraphOrientation ear.compatible ear.add_eq_union

@[simp]
theorem restrict_addEar_base (o : H.Orientation) (ear : G.Ear H) :
    (o.addEar ear).restrict ear.base_le_add = o := by
  exact restrict_unionOfEq_left o ear.toGraphOrientation ear.compatible ear.add_eq_union
    ear.base_le_add

@[simp]
theorem restrict_addEar_toGraph (o : H.Orientation) (ear : G.Ear H) :
    (o.addEar ear).restrict ear.toGraph_le_add = ear.toGraphOrientation := by
  exact restrict_unionOfEq_right o ear.toGraphOrientation ear.compatible ear.add_eq_union
    ear.toGraph_le_add ear.disjoint_edgeSet_toGraph

/-- Directing an ear from its old start to its old end preserves strong connectivity. -/
theorem isStronglyConnected_addEar (o : H.Orientation) (ear : G.Ear H)
    (hH : @Quiver.IsStronglyConnected H.vertexSet ⟨o.Hom⟩) :
    @Quiver.IsStronglyConnected ear.add.vertexSet ⟨(o.addEar ear).Hom⟩ := by
  let p := ear.toWalk.2.2
  let q := p.transfer ear.toGraph_le fun e he ↦ by
    rw [ear.edgeSet_toGraph]
    exact he
  have hq : q.FollowsOrientation ear.toGraphOrientation := by
    simpa only [p, q] using ear.followsOrientation_toGraphOrientation
  have hqAdd : (q.mapLe ear.toGraph_le_add).FollowsOrientation (o.addEar ear) := by
    apply (Walk.followsOrientation_mapLe_iff ear.toGraph_le_add q (o.addEar ear)).2
    simpa only [restrict_addEar_toGraph] using hq
  have hstart : ear.toWalk.1 ∈ V(ear.add) :=
    ear.base_le_add.vertexSet_mono ear.toWalk_fst_mem
  have hend : ear.toWalk.2.1 ∈ V(ear.add) :=
    ear.base_le_add.vertexSet_mono ear.toWalk_snd_mem
  let source : ear.add.vertexSet := ⟨ear.toWalk.1, hstart⟩
  let target : ear.add.vertexSet := ⟨ear.toWalk.2.1, hend⟩
  let directed : TauCeti.ArrowWalk (o.addEar ear).Hom source target :=
    (q.mapLe ear.toGraph_le_add).toOriented hqAdd hstart
  have hvertices : directed.vertices.unattach = p.support := by
    rw [Walk.vertices_toOriented]
    simp only [Walk.support_mapLe_eq_support, q, Walk.support_transfer]
  have splitAt (x : ear.add.vertexSet) (hx : x.1 ∈ V(ear.toGraph)) :
      Nonempty (TauCeti.ArrowWalk (o.addEar ear).Hom source x) ∧
        Nonempty (TauCeti.ArrowWalk (o.addEar ear).Hom x target) := by
    have hxSupport : x.1 ∈ p.support := by
      simpa only [Ear.vertexSet_toGraph, Set.mem_ofPred_eq] using hx
    have hxDirected : x ∈ directed.vertices := by
      have : x.1 ∈ directed.vertices.unattach := hvertices.symm ▸ hxSupport
      rw [List.mem_unattach] at this
      obtain ⟨hxProof, hxmem⟩ := this
      simpa using hxmem
    obtain ⟨r, s, -⟩ := @Quiver.Path.exists_eq_comp_of_mem_vertices
      ear.add.vertexSet ⟨(o.addEar ear).Hom⟩ source target directed x hxDirected
    exact ⟨⟨r⟩, ⟨s⟩⟩
  have oldPath (a b : H.vertexSet) :
      Nonempty (TauCeti.ArrowWalk (o.addEar ear).Hom
        (Set.inclusion ear.base_le_add.vertexSet_mono a)
        (Set.inclusion ear.base_le_add.vertexSet_mono b)) := by
    obtain ⟨r⟩ := hH a b
    let w := o.forgetWalk r
    have hw : w.FollowsOrientation o := o.followsOrientation_forgetWalk r
    have hwAdd : (w.mapLe ear.base_le_add).FollowsOrientation (o.addEar ear) := by
      apply (Walk.followsOrientation_mapLe_iff ear.base_le_add w (o.addEar ear)).2
      simpa only [restrict_addEar_base] using hw
    exact ⟨(w.mapLe ear.base_le_add).toOriented hwAdd
      (ear.base_le_add.vertexSet_mono a.2)⟩
  have fromOld (x : ear.add.vertexSet) :
      ∃ a : H.vertexSet, Nonempty (ArrowWalk (o.addEar ear).Hom
        (Set.inclusion ear.base_le_add.vertexSet_mono a) x) := by
    have hxUnion : x.1 ∈ V(H) ∪ V(ear.toGraph) := by
      rw [← ear.vertexSet_add]
      exact x.2
    rcases hxUnion with hx | hx
    · let a : H.vertexSet := ⟨x, hx⟩
      have hax : Set.inclusion ear.base_le_add.vertexSet_mono a = x := Subtype.ext rfl
      exact ⟨a, hax ▸ ⟨TauCeti.ArrowWalk.nil x⟩⟩
    · have hs := (splitAt x hx).1
      let a : H.vertexSet := ⟨ear.toWalk.1, ear.toWalk_fst_mem⟩
      have ha : Set.inclusion ear.base_le_add.vertexSet_mono a = source := Subtype.ext rfl
      exact ⟨a, ha ▸ hs⟩
  have toOld (x : ear.add.vertexSet) :
      ∃ a : H.vertexSet, Nonempty (TauCeti.ArrowWalk (o.addEar ear).Hom x
        (Set.inclusion ear.base_le_add.vertexSet_mono a)) := by
    have hxUnion : x.1 ∈ V(H) ∪ V(ear.toGraph) := by
      rw [← ear.vertexSet_add]
      exact x.2
    rcases hxUnion with hx | hx
    · let a : H.vertexSet := ⟨x, hx⟩
      have hax : Set.inclusion ear.base_le_add.vertexSet_mono a = x := Subtype.ext rfl
      exact ⟨a, hax ▸ ⟨TauCeti.ArrowWalk.nil x⟩⟩
    · have ht := (splitAt x hx).2
      let a : H.vertexSet := ⟨ear.toWalk.2.1, ear.toWalk_snd_mem⟩
      have ha : Set.inclusion ear.base_le_add.vertexSet_mono a = target := Subtype.ext rfl
      exact ⟨a, ha ▸ ht⟩
  intro x y
  obtain ⟨a, ⟨r⟩⟩ := toOld x
  obtain ⟨b, ⟨t⟩⟩ := fromOld y
  obtain ⟨s⟩ := oldPath a b
  exact ⟨(r.comp s).comp t⟩

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
      have hab : a = b := Subtype.ext (by simpa using a.2.trans b.2.symm)
      subst b
      exact ⟨TauCeti.ArrowWalk.nil a⟩)
    (fun i hi ↦ by
      rw [← d.earAt_fst i] at hi
      obtain ⟨o, ho⟩ := hi
      exact ⟨o.addEar (d.earAt i).2, o.isStronglyConnected_addEar (d.earAt i).2 ho⟩)
    (Fin.last d.length)

end EarDecomposition

/-- The sufficient direction of Robbins' theorem: a finite `2`-edge-connected multigraph admits
a strongly connected orientation. -/
theorem IsEdgeConnected.exists_stronglyConnected_orientation [Finite V(G)] [Finite E(G)]
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

/-- **Robbins' theorem.** A finite multigraph is `2`-edge-connected exactly when it admits a
strongly connected orientation. -/
theorem isEdgeConnected_two_iff_exists_stronglyConnected_orientation
    [Finite V(G)] [Finite E(G)] :
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
