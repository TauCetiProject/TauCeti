/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Trace
public import TauCeti.Combinatorics.Graph.Orientation.Subgraph
public import TauCeti.Combinatorics.Graph.Orientation.Walk

/-!
# Orienting trails

Every edge-labelled trail has a natural forward orientation on the graph that it traces.  Rather
than choosing a particular implementation of that orientation, this file exposes the property
needed by ear arguments: the traced graph admits an orientation and a walk with the same vertex
and edge sequences that follows it.

The construction is stable under adjoining a first traversal.  The one-edge trace is oriented in
the direction of that traversal, the remaining trace is oriented recursively, and the two
orientations combine because a trail never uses the first edge again.
-/

public section

open Set

universe u v

namespace Graph

variable {V : Type u} {E : Type v} {G H : Graph V E}

namespace Walk

/-- Mapping a walk to a supergraph follows an orientation exactly when the original walk follows
the restriction of that orientation. -/
theorem followsOrientation_mapLe_iff_restrict {x y : V} (p : H.Walk x y) (hHG : H ≤ G)
    (o : G.Orientation) :
    (p.mapLe hHG).FollowsOrientation o ↔ p.FollowsOrientation (o.restrict hHG) := by
  induction p with
  | nil => simp
  | cons e h p ih =>
      simp only [mapLe_cons, followsOrientation_cons, ih]
      simp only [Orientation.coe_restrict_tail, Orientation.coe_restrict_head]

/-- Prefixes of a walk following an orientation follow the same orientation. -/
theorem FollowsOrientation.takeUntil [DecidableEq V] {x y a : V} {p : G.Walk x y}
    (hp : p.FollowsOrientation o) (ha : a ∈ p.support) :
    (p.takeUntil a ha).FollowsOrientation o := by
  classical
  have h := congrArg (fun q ↦ q.FollowsOrientation o) (p.takeUntil_append_dropUntil ha)
  exact (followsOrientation_append _ _).1 (h.symm.mp hp) |>.1

/-- Suffixes of a walk following an orientation follow the same orientation. -/
theorem FollowsOrientation.dropUntil [DecidableEq V] {x y a : V} {p : G.Walk x y}
    (hp : p.FollowsOrientation o) (ha : a ∈ p.support) :
    (p.dropUntil a ha).FollowsOrientation o := by
  classical
  have h := congrArg (fun q ↦ q.FollowsOrientation o) (p.takeUntil_append_dropUntil ha)
  exact (followsOrientation_append _ _).1 (h.symm.mp hp) |>.2

end Walk

namespace IsLink

variable {e : E} {x y : V}

/-- Orient the graph traced by one edge traversal in the direction of that traversal. -/
private noncomputable def forwardOrientation (h : G.IsLink e x y) :
    (G.walkGraph h.toWalk).Orientation where
  tail f := ⟨x, by simp⟩
  head f := ⟨y, by simp⟩
  isLink f := by
    have hf : f.1 = e := by
      simpa using (h.toWalk.mem_edgeSet_walkGraph f.1).mp f.2
    rw [h.toWalk.walkGraph_isLink]
    exact ⟨hf.symm ▸ h, by simpa using hf⟩

/-- The one-edge walk in its traced graph follows its forward orientation. -/
private theorem followsOrientation_forwardWalk (h : G.IsLink e x y) :
    ((h.toWalk.walkGraph_isLink e x y).2 ⟨h, by simp⟩).toWalk.FollowsOrientation
      h.forwardOrientation := by
  simp [forwardOrientation]

end IsLink

namespace Walk

/-- A trail can be oriented forward on the graph that it traces.

The witness walk has exactly the original vertex and edge sequences.  Stating the result this
way avoids tying callers to a choice of orientation when the traced graph has no edges. -/
theorem IsTrail.exists_orientation_walkGraph {x y : V} {p : G.Walk x y} (hp : p.IsTrail) :
    ∃ o : (G.walkGraph p).Orientation, ∃ q : (G.walkGraph p).Walk x y,
      q.FollowsOrientation o ∧ q.support = p.support ∧ q.edges = p.edges := by
  induction p with
  | nil =>
      refine ⟨Orientation.ofEdgeEnds _, .nil, by simp⟩
  | @cons x y z e h p ih =>
      obtain ⟨hp, he⟩ := (isTrail_cons e h p).1 hp
      obtain ⟨o, q, hqo, hqv, hqe⟩ := ih hp
      rw [walkGraph_cons]
      let c := h.toWalk.walkGraph_compatible p
      have hdisj : Disjoint E(G.walkGraph h.toWalk) E(G.walkGraph p) := by
        rw [Set.disjoint_left]
        intro f hf hfp
        have hfe : f = e := by simpa using (h.toWalk.mem_edgeSet_walkGraph f).mp hf
        exact he (hfe ▸ (p.mem_edgeSet_walkGraph f).mp hfp)
      let o' := h.forwardOrientation.union o c
      let first : c.union.Walk x y :=
        ((h.toWalk.walkGraph_isLink e x y).2 ⟨h, by simp⟩).toWalk.mapLe c.left_le_union
      let rest : c.union.Walk y z := q.mapLe c.right_le_union
      refine ⟨o', first.append rest, ?_, ?_, ?_⟩
      · rw [followsOrientation_append]
        constructor
        · rw [followsOrientation_mapLe_iff_restrict,
            Orientation.restrict_union_left]
          exact h.followsOrientation_forwardWalk
        · rw [followsOrientation_mapLe_iff_restrict,
            Orientation.restrict_union_right hdisj]
          exact hqo
      · simp [first, rest, hqv]
      · simp [first, rest, hqe]

end Walk

end Graph
