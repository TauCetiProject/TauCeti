/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Forest

/-!
# Paths in the bridge forest

A walk projects to the bridge forest by omitting its nonbridge edges. Its edge list is
exactly the original edge list filtered to bridges; in particular trails, and hence paths,
project to paths. Conversely, a path in the bridge forest lifts to a native path between
any prescribed vertices of its end components, retaining exactly the displayed bridges in
order. The portions inside bridge components need not be unique.

These operations refine the reachability correspondence to actual edge-labelled witnesses.
No finiteness assumptions on vertices or edges are needed.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {x y z : α}

namespace Walk

open Classical in
/-- Project a walk to the bridge forest, omitting traversals of nonbridges. -/
noncomputable def toBridgeForest : {x y : α} → (p : G.Walk x y) →
    (hx : x ∈ V(G)) → (hy : y ∈ V(G)) →
    G.bridgeForest.Walk (G.bridgeComponentOf x hx) (G.bridgeComponentOf y hy)
  | _, _, .nil, _, _ => .nil
  | _, _, .cons e h p, hx, hy =>
    if he : G.IsBridge e then
      .cons e (he.isLink_bridgeForest h) (p.toBridgeForest h.right_mem hy)
    else
      ((G.bridgeComponentOf_eq_bridgeComponentOf_iff hx h.right_mem).mpr
        (h.reachable_deleteEdges_bridgeSet he)).symm ▸ p.toBridgeForest h.right_mem hy

/-- A zero-length walk projects to the zero-length walk. -/
@[simp]
theorem toBridgeForest_nil (hx : x ∈ V(G)) :
    (Walk.nil : G.Walk x x).toBridgeForest hx hx = .nil := (rfl)

open Classical in
/-- Projection retains exactly the original bridge identities, in their original order. -/
@[simp]
theorem edges_toBridgeForest (p : G.Walk x y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toBridgeForest hx hy).edges = p.edges.filter (fun e ↦ decide (G.IsBridge e)) := by
  classical
  induction p with
  | nil => simp [toBridgeForest]
  | cons e h p ih =>
    by_cases he : G.IsBridge e <;> simp [toBridgeForest, he, ih]

/-- A bridge traversal is retained by projection. -/
@[simp]
theorem toBridgeForest_cons_of_isBridge {e : β} (h : G.IsLink e x y)
    (p : G.Walk y z) (he : G.IsBridge e) (hx : x ∈ V(G)) (hz : z ∈ V(G)) :
    (cons e h p).toBridgeForest hx hz =
      cons e (he.isLink_bridgeForest h) (p.toBridgeForest h.right_mem hz) := by
  apply ext_edges
  simp [he]

/-- A nonbridge traversal is omitted; only the identification of its end components remains. -/
@[simp]
theorem toBridgeForest_cons_of_not_isBridge {e : β} (h : G.IsLink e x y)
    (p : G.Walk y z) (he : ¬ G.IsBridge e) (hx : x ∈ V(G)) (hz : z ∈ V(G)) :
    (cons e h p).toBridgeForest hx hz =
      ((G.bridgeComponentOf_eq_bridgeComponentOf_iff hx h.right_mem).mpr
        (h.reachable_deleteEdges_bridgeSet he)).symm ▸ p.toBridgeForest h.right_mem hz := by
  apply ext_edges
  simp [he]

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

/-- Trails project to paths: filtering preserves distinct edges, and a forest trail is a path. -/
theorem IsTrail.toBridgeForest {p : G.Walk x y} (hp : p.IsTrail)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) : (p.toBridgeForest hx hy).IsPath := by
  apply (G.isForest_bridgeForest.isPath_iff_isTrail _).mpr
  rw [isTrail_def, edges_toBridgeForest]
  exact ((isTrail_def p).mp hp).filter _

/-- Paths project to paths in the bridge forest. -/
theorem IsPath.toBridgeForest {p : G.Walk x y} (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) : (p.toBridgeForest hx hy).IsPath :=
  hp.isTrail.toBridgeForest hx hy

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

/-- Choose a path lifting a bridge-forest path between specified original endpoints.
The choices concern only the paths inside bridge components. -/
noncomputable def liftBridgeForest (q : G.bridgeForest.Walk C D) (hq : q.IsPath)
    (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) : G.Walk x y :=
  (hq.exists_lift_bridgeForest hx hy).choose

/-- A chosen lift has no repeated vertices. -/
@[simp]
theorem isPath_liftBridgeForest (q : G.bridgeForest.Walk C D) (hq : q.IsPath)
    (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) : (q.liftBridgeForest hq hx hy).IsPath :=
  (hq.exists_lift_bridgeForest hx hy).choose_spec.1

open Classical in
/-- The bridges in the chosen lift are exactly the edges of the forest path, in order. -/
@[simp]
theorem filter_edges_liftBridgeForest (q : G.bridgeForest.Walk C D) (hq : q.IsPath)
    (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) :
    (q.liftBridgeForest hq hx hy).edges.filter (fun e ↦ decide (G.IsBridge e)) = q.edges :=
  (hq.exists_lift_bridgeForest hx hy).choose_spec.2.1

/-- The lift stays in the union of the components on the forest path. -/
theorem exists_mem_support_of_mem_support_liftBridgeForest
    (q : G.bridgeForest.Walk C D) (hq : q.IsPath)
    (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) {a : α}
    (ha : a ∈ (q.liftBridgeForest hq hx hy).support) :
    ∃ E ∈ q.support, a ∈ V(E.1) :=
  (hq.exists_lift_bridgeForest hx hy).choose_spec.2.2 a ha

/-- Projecting a lifted path recovers the original forest path. -/
@[simp]
theorem toBridgeForest_liftBridgeForest (hx : x ∈ V(G)) (hy : y ∈ V(G))
    (q : G.bridgeForest.Walk (G.bridgeComponentOf x hx) (G.bridgeComponentOf y hy))
    (hq : q.IsPath) :
    (q.liftBridgeForest hq (mem_vertexSet_bridgeComponentOf_self hx)
      (mem_vertexSet_bridgeComponentOf_self hy)).toBridgeForest hx hy = q := by
  classical
  apply ext_edges
  simp

end Walk

end Graph
