/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Characterization
public import TauCeti.Combinatorics.Graph.Orientation.StronglyConnected
public import TauCeti.Combinatorics.Graph.Orientation.Trail

/-!
# Robbins' theorem

This file proves Robbins' theorem for finite multigraphs: a multigraph admits a strongly
connected orientation exactly when it is `2`-edge-connected.  The statement includes empty and
singleton vertex sets, loops, and parallel edges.

The forward implication is the bridge obstruction proved in
`Graph.Orientation.StronglyConnected`.  For the converse, take a vertex-starting ear
decomposition.  Orient each open or closed ear along its defining trail.  A new vertex can then
be reached from the old graph along a prefix of the ear and can return along a suffix; hence
strong connectivity is preserved at every stage.

## References

* H. E. Robbins, *A theorem on graphs, with an application to a problem of traffic control*,
  Amer. Math. Monthly 46 (1939), 281--283.
* R. Diestel, *Graph Theory*, Chapter 3, for the ear-decomposition proof.
-/

public section

open Set

universe u v

namespace Graph

open TauCeti

variable {V : Type u} {E : Type v} {G H : Graph V E}

namespace Orientation

private theorem exists_stronglyConnected_union_walk {x y : V} (p : G.Walk x y)
    (c : H.Compatible (G.walkGraph p)) (hp : p.IsTrail)
    (hx : x ∈ V(H)) (hy : y ∈ V(H))
    (hnew : ∀ e ∈ p.edges, e ∉ E(H)) (o : H.Orientation)
    (ho : @Quiver.IsStronglyConnected V(H) ⟨o.Hom⟩) :
    ∃ o' : c.union.Orientation, @Quiver.IsStronglyConnected V(c.union) ⟨o'.Hom⟩ := by
  classical
  obtain ⟨op, q, hqo, hqv, _⟩ := hp.exists_orientation_walkGraph
  have hdisj : Disjoint E(H) E(G.walkGraph p) := by
    rw [Set.disjoint_left]
    intro e heH hep
    exact hnew e ((p.mem_edgeSet_walkGraph e).mp hep) heH
  let o' := o.union op c
  let q' : c.union.Walk x y := q.mapLe c.right_le_union
  have hq' : q'.FollowsOrientation o' := by
    -- Expose the mapped walk hidden by `q'` so the restriction equivalence applies.
    change (q.mapLe c.right_le_union).FollowsOrientation o'
    rw [Walk.followsOrientation_mapLe_iff_restrict,
      Orientation.restrict_union_right hdisj]
    exact hqo
  have toBase (z : V) (hz : z ∈ V(c.union)) :
      ∃ a, a ∈ V(H) ∧ ∃ r : c.union.Walk z a, r.FollowsOrientation o' := by
    rw [c.vertexSet_union] at hz
    rcases hz with hzH | hzP
    · exact ⟨z, hzH, .nil, by simp⟩
    · have hzq : z ∈ q'.support := by
        simpa [q', hqv] using hzP
      exact ⟨y, hy, q'.dropUntil z hzq, hq'.dropUntil hzq⟩
  have fromBase (z : V) (hz : z ∈ V(c.union)) :
      ∃ a, a ∈ V(H) ∧ ∃ r : c.union.Walk a z, r.FollowsOrientation o' := by
    rw [c.vertexSet_union] at hz
    rcases hz with hzH | hzP
    · exact ⟨z, hzH, .nil, by simp⟩
    · have hzq : z ∈ q'.support := by
        simpa [q', hqv] using hzP
      exact ⟨x, hx, q'.takeUntil z hzq, hq'.takeUntil hzq⟩
  refine ⟨o', fun a b ↦ ?_⟩
  obtain ⟨a', ha', ra, hra⟩ := toBase a a.2
  obtain ⟨b', hb', rb, hrb⟩ := fromBase b b.2
  obtain ⟨r⟩ := ho ⟨a', ha'⟩ ⟨b', hb'⟩
  let r' : c.union.Walk a' b' := (o.forgetWalk r).mapLe c.left_le_union
  have hr' : r'.FollowsOrientation o' := by
    -- Expose the mapped walk hidden by `r'` so the restriction equivalence applies.
    change ((o.forgetWalk r).mapLe c.left_le_union).FollowsOrientation o'
    rw [Walk.followsOrientation_mapLe_iff_restrict,
      Orientation.restrict_union_left]
    exact o.followsOrientation_forgetWalk r
  rw [o'.nonempty_arrowWalk_iff]
  exact ⟨ra.append (r'.append rb), by simp [hra, hr', hrb]⟩

/-- Adjoining an open or closed ear to a graph with a strongly connected orientation produces a
strongly connected orientation of the enlarged graph. -/
theorem _root_.Graph.Ear.exists_stronglyConnected_orientation (ear : G.Ear H)
    (o : H.Orientation) (ho : @Quiver.IsStronglyConnected V(H) ⟨o.Hom⟩) :
    ∃ o' : ear.add.Orientation, @Quiver.IsStronglyConnected V(ear.add) ⟨o'.Hom⟩ := by
  cases ear with
  | @«open» hHG x y p hp hx hy hxy hinter hnew =>
      let ear : G.Ear H := Ear.open hHG p hp hx hy hxy hinter hnew
      have htg : ear.toGraph = G.walkGraph p := by
        simp only [ear, Ear.toGraph_open]
      let c : H.Compatible (G.walkGraph p) := htg ▸ ear.compatible
      have hc : c.union = ear.add := by
        apply le_antisymm
        · exact IsSubgraph.union_le ear.base_le_add (htg ▸ ear.toGraph_le_add)
        · exact ear.add_le_iff.mpr ⟨c.left_le_union, htg.symm ▸ c.right_le_union⟩
      rw [← hc]
      exact exists_stronglyConnected_union_walk p c hp.isTrail hx hy hnew o ho
  | @«closed» hHG x p hp hx hinter hnew =>
      let ear : G.Ear H := Ear.closed hHG p hp hx hinter hnew
      have htg : ear.toGraph = G.walkGraph p := by
        simp only [ear, Ear.toGraph_closed]
      let c : H.Compatible (G.walkGraph p) := htg ▸ ear.compatible
      have hc : c.union = ear.add := by
        apply le_antisymm
        · exact IsSubgraph.union_le ear.base_le_add (htg ▸ ear.toGraph_le_add)
        · exact ear.add_le_iff.mpr ⟨c.left_le_union, htg.symm ▸ c.right_le_union⟩
      rw [← hc]
      exact exists_stronglyConnected_union_walk p c hp.isTrail hx hx hnew o ho

end Orientation

namespace EarDecomposition

/-- Every vertex-starting ear decomposition yields a strongly connected orientation of its
final graph. -/
theorem IsVertexStart.exists_stronglyConnected_orientation (d : G.EarDecomposition H)
    (hd : d.IsVertexStart) :
    ∃ o : H.Orientation, @Quiver.IsStronglyConnected V(H) ⟨o.Hom⟩ := by
  rw [← d.graphAfter_last]
  refine d.graphAfter_induction
    (P := fun K ↦ ∃ o : K.Orientation, @Quiver.IsStronglyConnected V(K) ⟨o.Hom⟩) ?_ ?_
    (Fin.last d.length)
  · obtain ⟨v, hv⟩ := (isVertexStart_iff d).mp hd
    rw [hv]
    let o := Orientation.ofEdgeEnds (Graph.noEdge {v.1} E)
    refine ⟨o, fun x y ↦ ?_⟩
    have hxv : x.1 = v.1 := by simpa using x.2
    have hyv : y.1 = v.1 := by simpa using y.2
    have hxy : x = y := Subtype.ext (hxv.trans hyv.symm)
    subst y
    exact ⟨ArrowWalk.nil x⟩
  · intro i hi
    rw [← d.earAt_fst i] at hi
    obtain ⟨o, ho⟩ := hi
    exact (d.earAt i).2.exists_stronglyConnected_orientation o ho

end EarDecomposition

/-- The sufficient direction of Robbins' theorem: every finite `2`-edge-connected multigraph
admits a strongly connected orientation. -/
theorem IsEdgeConnected.exists_stronglyConnected_orientation [Finite V(G)] [Finite E(G)]
    (hG : G.IsEdgeConnected 2) :
    ∃ o : G.Orientation, @Quiver.IsStronglyConnected V(G) ⟨o.Hom⟩ := by
  classical
  cases isEmpty_or_nonempty V(G) with
  | inl h =>
      let o := Orientation.ofEdgeEnds G
      exact ⟨o, fun x ↦ isEmptyElim x⟩
  | inr h =>
      obtain ⟨d, hd⟩ :=
        isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition.mp hG
      exact hd.exists_stronglyConnected_orientation d

/-- **Robbins' theorem.** A finite multigraph admits a strongly connected orientation exactly
when it is `2`-edge-connected. -/
theorem isEdgeConnected_two_iff_exists_stronglyConnected_orientation
    [Finite V(G)] [Finite E(G)] :
    G.IsEdgeConnected 2 ↔
      ∃ o : G.Orientation, @Quiver.IsStronglyConnected V(G) ⟨o.Hom⟩ :=
  ⟨IsEdgeConnected.exists_stronglyConnected_orientation,
    isEdgeConnected_two_of_exists_stronglyConnected_orientation⟩

/-- The classical connected form of Robbins' theorem: a finite connected multigraph has a
strongly connected orientation exactly when it has no bridge. -/
theorem Connected.exists_stronglyConnected_orientation_iff_forall_not_isBridge
    [Finite V(G)] [Finite E(G)] (hG : G.Connected) :
    (∃ o : G.Orientation, @Quiver.IsStronglyConnected V(G) ⟨o.Hom⟩) ↔
      ∀ e, ¬ G.IsBridge e := by
  rw [← isEdgeConnected_two_iff_exists_stronglyConnected_orientation,
    isEdgeConnected_two_iff_connected_and_forall_not_isBridge hG.nonempty,
    and_iff_right hG]

end Graph

namespace SimpleGraph

open TauCeti

variable {V : Type u} {G : SimpleGraph V}

/-- The simple-graph form of Robbins' theorem, using orientations of the doubled quiver. -/
theorem isEdgeConnected_two_iff_exists_stronglyConnected_orientation [Finite V] :
    G.IsEdgeConnected 2 ↔
      ∃ o : DoubledQuiver.Orientation G,
        Quiver.IsStronglyConnected (DoubledQuiver.OrientedQuiver G o) := by
  constructor
  · intro hG
    have hG' : (Graph.ofSimpleGraph G).IsEdgeConnected 2 :=
      (Graph.isEdgeConnected_ofSimpleGraph_iff G 2).mpr hG
    obtain ⟨o, ho⟩ := hG'.exists_stronglyConnected_orientation
    refine ⟨o.toDartOrientation, ?_⟩
    exact (o.isStronglyConnected_orientedQuiver_iff).2 ho
  · exact isEdgeConnected_two_of_exists_stronglyConnected_orientation

end SimpleGraph
