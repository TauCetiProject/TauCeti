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

namespace Walk

/-- A walk in a subgraph follows the restricted orientation exactly when its image in the
larger graph follows the original orientation. -/
@[simp]
theorem followsOrientation_mapLe_iff {H : Graph α β} (h : H ≤ G)
    {x y : α} (p : H.Walk x y) (o : G.Orientation) :
    (p.mapLe h).FollowsOrientation o ↔ p.FollowsOrientation (o.restrict h) := by
  induction p with
  | nil => simp
  | @cons x y z e he p ih =>
      simp only [mapLe_cons, followsOrientation_cons, ih, Orientation.coe_restrict_tail,
        Orientation.coe_restrict_head]

/-- Restricting a walk to a subgraph and restricting its orientation preserve the property of
following that orientation. -/
theorem FollowsOrientation.transfer {H : Graph α β} {x y : α} {o : G.Orientation}
    {p : G.Walk x y} (hp : p.FollowsOrientation o) (h : H ≤ G)
    (hedges : ∀ e, e ∈ p.edges → e ∈ E(H)) :
    (p.transfer h hedges).FollowsOrientation (o.restrict h) := by
  apply (followsOrientation_mapLe_iff h (p.transfer h hedges) o).mp
  simpa only [mapLe_transfer] using hp

/-- Orient a graph so that a trail is traversed from its start to its end. Edges outside the
trail retain an arbitrary orientation. -/
noncomputable def orientation : {x y : α} → (p : G.Walk x y) → p.edges.Nodup → G.Orientation
  | _, _, .nil, _ => Orientation.ofEdgeEnds G
  | _, _, .cons' x y z e h p, hp => by
      classical
      have hp' : (e :: p.edges).Nodup := by simpa only [edges_cons] using hp
      exact Orientation.ofHead
        (fun f ↦ if hf : f.1 = e then ⟨y, h.right_mem⟩
          else (p.orientation (List.nodup_cons.1 hp').2).head f)
        fun f ↦ by
          split_ifs with hf
          · subst hf
            exact h.inc_right
          · exact (p.orientation (List.nodup_cons.1 hp').2).head_inc f

@[simp]
theorem orientation_cons_head {x y z : α} (e : β) (h : G.IsLink e x y)
    (p : G.Walk y z) (hp : (Walk.cons e h p).edges.Nodup) :
    ((Walk.cons e h p).orientation hp).head ⟨e, h.edge_mem⟩ = ⟨y, h.right_mem⟩ := by
  simp [orientation]

@[simp]
theorem orientation_cons_tail {x y z : α} (e : β) (h : G.IsLink e x y)
    (p : G.Walk y z) (hp : (Walk.cons e h p).edges.Nodup) :
    ((Walk.cons e h p).orientation hp).tail ⟨e, h.edge_mem⟩ = ⟨x, h.left_mem⟩ := by
  apply Subtype.ext
  apply (((Walk.cons e h p).orientation hp).isLink ⟨e, h.edge_mem⟩).left_unique
  simpa using h

/-- A trail follows the orientation obtained by directing its successive edges forward. -/
theorem followsOrientation_orientation {x y : α} (p : G.Walk x y) (hp : p.edges.Nodup) :
    p.FollowsOrientation (p.orientation hp) := by
  induction p with
  | nil => simp
  | @cons x y z e h p ih =>
      have hp' : (e :: p.edges).Nodup := by simpa only [edges_cons] using hp
      have hpTail : p.edges.Nodup := (List.nodup_cons.1 hp').2
      rw [followsOrientation_cons]
      refine ⟨by simp, by simp, ih hpTail |>.congr fun f hf ↦ ?_⟩
      have hne : f.1 ≠ e := fun hfe ↦ (List.nodup_cons.1 hp').1 (hfe ▸ hf)
      simp [orientation, hne]

end Walk

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

/-- An edge of an adjoined ear outside the base belongs to the traced graph. -/
private theorem mem_toGraph_of_notMem_base (ear : G.Ear H) {e : ear.add.edgeSet}
    (he : e.1 ∉ E(H)) : e.1 ∈ E(ear.toGraph) := by
  have heUnion : e.1 ∈ E(H) ∪ E(ear.toGraph) := by
    simpa only [ear.edgeSet_add] using e.2
  exact heUnion.resolve_left he

open Classical in
/-- Extend an orientation over an adjoined ear by directing every new edge in the order of the
ear's underlying walk. -/
noncomputable def addEar (o : H.Orientation) (ear : G.Ear H) : ear.add.Orientation where
  tail e := if he : e.1 ∈ E(H) then
      ⟨o.tail ⟨e, he⟩, by
        rw [ear.vertexSet_add]
        exact Or.inl (o.tail ⟨e, he⟩).2⟩
    else
      ⟨ear.toGraphOrientation.tail ⟨e, mem_toGraph_of_notMem_base ear he⟩, by
        rw [ear.vertexSet_add]
        exact Or.inr (ear.toGraphOrientation.tail
          ⟨e, mem_toGraph_of_notMem_base ear he⟩).2⟩
  head e := if he : e.1 ∈ E(H) then
      ⟨o.head ⟨e, he⟩, by
        rw [ear.vertexSet_add]
        exact Or.inl (o.head ⟨e, he⟩).2⟩
    else
      ⟨ear.toGraphOrientation.head ⟨e, mem_toGraph_of_notMem_base ear he⟩, by
        rw [ear.vertexSet_add]
        exact Or.inr (ear.toGraphOrientation.head
          ⟨e, mem_toGraph_of_notMem_base ear he⟩).2⟩
  isLink e := by
    by_cases he : e.1 ∈ E(H)
    · simpa [he] using (o.isLink ⟨e, he⟩).mono ear.base_le_add
    · simpa [he] using (ear.toGraphOrientation.isLink
        ⟨e, mem_toGraph_of_notMem_base ear he⟩).mono ear.toGraph_le_add

@[simp]
theorem restrict_addEar_base (o : H.Orientation) (ear : G.Ear H) :
    (o.addEar ear).restrict ear.base_le_add = o := by
  apply ext_of_head
  intro e
  apply Subtype.ext
  simp [addEar]

@[simp]
theorem restrict_addEar_toGraph (o : H.Orientation) (ear : G.Ear H) :
    (o.addEar ear).restrict ear.toGraph_le_add = ear.toGraphOrientation := by
  apply ext_of_head
  intro e
  apply Subtype.ext
  simp [addEar, ear.disjoint_edgeSet_toGraph.notMem_of_mem_right e.2]

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
