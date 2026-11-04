/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Forest

/-!
# Paths in the bridge forest

This file refines the projection and lifting operations of `Bridge.Forest` to ordered
edge lists and support control. Projection keeps exactly the original bridges, in order,
and respects concatenation and reversal. A forest path lifts between arbitrary prescribed
vertices of its end components, and projecting the canonical lift recovers the forest path.
No finiteness assumptions on vertices or edges are needed.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {x y z : α}

namespace Walk

/-- Projection cannot increase the number of traversed edges. -/
theorem length_toBridgeForest_le (p : G.Walk x y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toBridgeForest hx hy).length ≤ p.length := by
  classical
  rw [← Walk.length_edges, edges_toBridgeForest, ← Walk.length_edges]
  exact List.length_filter_le _ _

/-- Projection respects concatenation. -/
@[simp]
theorem toBridgeForest_append (p : G.Walk x y) (q : G.Walk y z)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) (hz : z ∈ V(G)) :
    (p.append q).toBridgeForest hx hz =
      (p.toBridgeForest hx hy).append (q.toBridgeForest hy hz) := by
  classical
  apply ext_edges
  simp [edges_append, List.filter_append]

/-- Projection respects reversal. -/
@[simp]
theorem toBridgeForest_reverse (p : G.Walk x y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    p.reverse.toBridgeForest hy hx = (p.toBridgeForest hx hy).reverse := by
  classical
  apply ext_edges
  simp [List.filter_reverse]

/-- Every vertex visited by a walk projects to a vertex visited by its projection. -/
theorem bridgeComponentOf_mem_support_toBridgeForest (p : G.Walk x y)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) {a : α} (ha : a ∈ V(G)) (h : a ∈ p.support) :
    G.bridgeComponentOf a ha ∈ (p.toBridgeForest hx hy).support := by
  obtain ⟨r, s, rfl⟩ := mem_support_iff_exists_append.mp h
  rw [toBridgeForest_append r s hx ha hy, support_append]
  exact List.mem_append_left _ (r.toBridgeForest hx ha).end_mem_support

/-- Trails project to paths: filtering preserves distinct edges, and a forest trail is a path. -/
theorem IsTrail.toBridgeForest {p : G.Walk x y} (hp : p.IsTrail)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) : (p.toBridgeForest hx hy).IsPath := by
  apply (G.isForest_bridgeForest.isPath_iff_isTrail _).mpr
  rw [isTrail_def, edges_toBridgeForest]
  exact ((isTrail_def p).mp hp).filter _

end Walk

open Classical in
/-- A bridge-forest path lifts between arbitrary vertices of its end components. The lift
retains its bridges in order, and all its vertices belong to components on the given path. -/
theorem Walk.IsPath.exists_lift_bridgeForest {C D : G.BridgeComponent}
    {q : G.bridgeForest.Walk C D} (hq : q.IsPath) (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) :
    ∃ p : G.Walk x y, p.IsPath ∧
      p.edges.filter (fun e ↦ decide (G.IsBridge e)) = q.edges ∧
      ∀ a ∈ p.support, ∃ E ∈ q.support, a ∈ V(E.1) := by
  classical
  induction q generalizing x with
  | nil =>
    obtain ⟨p, hp, he, hv⟩ := BridgeComponent.exists_path hx hy
    refine ⟨p, hp, ?_, fun a ha ↦ ⟨_, by simp, hv a ha⟩⟩
    rw [Walk.edges_nil]
    exact List.filter_eq_nil_iff.mpr (fun e he' ↦ by simp [he e he'])
  | @cons C D E e h q ih =>
    obtain ⟨hqp, hCq⟩ := (Walk.isPath_cons e h q).mp hq
    obtain ⟨he, a, ha, b, hb, hab⟩ := bridgeForest_isLink.mp h
    obtain ⟨p, hp, hpe, hpv⟩ := BridgeComponent.exists_path hx ha
    obtain ⟨r, hr, hre, hrv⟩ := ih hqp hb hy
    refine ⟨p.append (.cons e hab r), ?_, ?_, ?_⟩
    · rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons,
        List.nodup_append]
      refine ⟨hp.support_nodup, hr.support_nodup, ?_⟩
      intro v hv w hw hvw
      subst w
      obtain ⟨F, hF, hvF⟩ := hrv v hw
      exact hCq ((ConnectedComponent.eq_of_mem_of_mem (hpv v hv) hvF) ▸ hF)
    · have hfilter : p.edges.filter (fun f ↦ decide (G.IsBridge f)) = [] :=
        List.filter_eq_nil_iff.mpr (fun f hf ↦ by simpa using hpe f hf)
      simp [Walk.edges_append, hfilter, he, hre]
    · intro v hv
      rw [Walk.support_append, Walk.support_cons, List.tail_cons, List.mem_append] at hv
      rcases hv with hv | hv
      · exact ⟨C, by simp, hpv v hv⟩
      · obtain ⟨F, hF, hvF⟩ := hrv v hv
        exact ⟨F, by simp [hF], hvF⟩

namespace Walk

variable {C D : G.BridgeComponent}

/-- Projecting the canonical lift of a forest path recovers that path, with endpoints
identified with the bridge components of the prescribed vertices. -/
@[simp]
theorem toBridgeForest_liftBridgeForest (q : G.bridgeForest.Walk C D) (hq : q.IsPath)
    (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) :
    (q.liftBridgeForest hx hy).toBridgeForest (BridgeComponent.mem_vertexSet hx)
      (BridgeComponent.mem_vertexSet hy) =
      q.copy (BridgeComponent.eq_bridgeComponentOf hx)
        (BridgeComponent.eq_bridgeComponentOf hy) := by
  apply G.isForest_bridgeForest.eq_of_isPath
  · exact (q.isPath_liftBridgeForest hx hy).toBridgeForest _ _
  · exact (isPath_copy _ _ _).mpr hq

open Classical in
/-- The bridges in the canonical lift are exactly the edges of the forest path, in order. -/
@[simp]
theorem filter_edges_liftBridgeForest (q : G.bridgeForest.Walk C D) (hq : q.IsPath)
    (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) :
    (q.liftBridgeForest hx hy).edges.filter (fun e ↦ decide (G.IsBridge e)) = q.edges := by
  simpa only [edges_toBridgeForest, edges_copy] using
    congrArg Walk.edges (toBridgeForest_liftBridgeForest q hq hx hy)

/-- The canonical lift stays in the union of the components on the forest path. -/
theorem exists_mem_support_of_mem_support_liftBridgeForest
    (q : G.bridgeForest.Walk C D) (hq : q.IsPath)
    (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) {a : α}
    (ha : a ∈ (q.liftBridgeForest hx hy).support) :
    ∃ E ∈ q.support, a ∈ V(E.1) := by
  have haG := (q.liftBridgeForest hx hy).support_subset_vertexSet
    (BridgeComponent.mem_vertexSet hx) a ha
  refine ⟨G.bridgeComponentOf a haG, ?_, mem_vertexSet_bridgeComponentOf_self haG⟩
  have hm := (q.liftBridgeForest hx hy).bridgeComponentOf_mem_support_toBridgeForest
    (BridgeComponent.mem_vertexSet hx) (BridgeComponent.mem_vertexSet hy) haG ha
  rwa [toBridgeForest_liftBridgeForest q hq hx hy, support_copy] at hm

end Walk

end Graph
