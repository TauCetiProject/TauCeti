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
    (hx : x ∈ V(G)) (hz : z ∈ V(G)) :
    (p.append q).toBridgeForest hx hz =
      (p.toBridgeForest hx (p.end_mem_vertexSet hx)).append
        (q.toBridgeForest (p.end_mem_vertexSet hx) hz) := by
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

/-- The support of a projected walk consists exactly of the components of its visited vertices. -/
theorem mem_support_toBridgeForest_iff (p : G.Walk x y)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) {C : G.BridgeComponent} :
    C ∈ (p.toBridgeForest hx hy).support ↔
      ∃ a ∈ p.support, ∃ ha : a ∈ V(G), G.bridgeComponentOf a ha = C := by
  constructor
  · intro hC
    induction p with
    | @nil x =>
        simp only [toBridgeForest_nil, support_nil, List.mem_singleton] at hC
        exact ⟨x, by simp, hx, hC.symm⟩
    | @cons x y z e h p ih =>
        by_cases he : G.IsBridge e
        · simp only [toBridgeForest_cons_of_isBridge h p he, support_cons,
            List.mem_cons] at hC
          rcases hC with hC | hC
          · exact ⟨x, by simp, hx, hC.symm⟩
          · obtain ⟨a, ha, haG, haC⟩ := ih h.right_mem hy hC
            exact ⟨a, by simp [ha], haG, haC⟩
        · simp only [toBridgeForest_cons_of_not_isBridge h p he, support_copy] at hC
          obtain ⟨a, ha, haG, haC⟩ := ih h.right_mem hy hC
          exact ⟨a, by simp [ha], haG, haC⟩
  · rintro ⟨a, ha, haG, rfl⟩
    obtain ⟨r, s, rfl⟩ := mem_support_iff_exists_append.mp ha
    rw [toBridgeForest_append, support_append]
    exact List.mem_append_left _ (r.toBridgeForest hx haG).end_mem_support

/-- Every vertex visited by a walk projects to a vertex visited by its projection. -/
theorem bridgeComponentOf_mem_support_toBridgeForest (p : G.Walk x y)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) {a : α} (ha : a ∈ V(G)) (h : a ∈ p.support) :
    G.bridgeComponentOf a ha ∈ (p.toBridgeForest hx hy).support :=
  (p.mem_support_toBridgeForest_iff hx hy).mpr ⟨a, h, ha, rfl⟩

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
  · exact (q.isPath_liftBridgeForest hx hy).isTrail.toBridgeForest _ _
  · exact (isPath_copy _ _ _).mpr hq

open Classical in
/-- The bridges in the canonical lift are exactly the edges of the forest path, in order. -/
@[simp]
theorem filter_edges_liftBridgeForest (q : G.bridgeForest.Walk C D) (hq : q.IsPath)
    (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) :
    (q.liftBridgeForest hx hy).edges.filter (fun e ↦ decide (G.IsBridge e)) = q.edges := by
  simpa only [edges_toBridgeForest, edges_copy] using
    congrArg Walk.edges (toBridgeForest_liftBridgeForest q hq hx hy)

/-- A path lift of a bridge-forest path traverses every bridge displayed by that forest path. -/
theorem IsPath.mem_edges_liftBridgeForest {e : β}
    {q : G.bridgeForest.Walk C D} (hq : q.IsPath) (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1))
    (he : e ∈ q.edges) : e ∈ (q.liftBridgeForest hx hy).edges := by
  classical
  rw [← filter_edges_liftBridgeForest q hq hx hy] at he
  exact (List.mem_filter.mp he).1

/-- For a bridge-forest path, the bridge identities in its lift are exactly its displayed
edges. -/
theorem IsPath.mem_edges_liftBridgeForest_iff {e : β}
    {q : G.bridgeForest.Walk C D} (hq : q.IsPath) (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) :
    e ∈ (q.liftBridgeForest hx hy).edges ∧ G.IsBridge e ↔ e ∈ q.edges := by
  classical
  rw [← filter_edges_liftBridgeForest q hq hx hy, List.mem_filter, decide_eq_true_eq]

/-- The canonical lift stays in the union of the components on the forest walk. -/
theorem exists_mem_support_of_mem_support_liftBridgeForest
    (q : G.bridgeForest.Walk C D)
    (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) {a : α}
    (ha : a ∈ (q.liftBridgeForest hx hy).support) :
    ∃ E ∈ q.support, a ∈ V(E.1) := by
  have haG := (q.liftBridgeForest hx hy).support_subset_vertexSet
    (BridgeComponent.mem_vertexSet hx) a ha
  refine ⟨G.bridgeComponentOf a haG, ?_, mem_vertexSet_bridgeComponentOf_self haG⟩
  have hm := (q.liftBridgeForest hx hy).bridgeComponentOf_mem_support_toBridgeForest
    (BridgeComponent.mem_vertexSet hx) (BridgeComponent.mem_vertexSet hy) haG ha
  obtain ⟨r, s, hrs⟩ := mem_support_iff_exists_append.mp hm
  have hsub : r.edges ⊆ q.edges := by
    intro e he
    have he' : e ∈ ((q.liftBridgeForest hx hy).toBridgeForest
        (BridgeComponent.mem_vertexSet hx) (BridgeComponent.mem_vertexSet hy)).edges := by
      rw [hrs, edges_append]
      exact List.mem_append_left _ he
    classical
    rw [edges_toBridgeForest, List.mem_filter, decide_eq_true_eq] at he'
    exact q.mem_edges_of_mem_edges_liftBridgeForest hx hy he'.1 he'.2
  have hstart : G.bridgeComponentOf x (BridgeComponent.mem_vertexSet hx) ∈ q.support := by
    rw [← BridgeComponent.eq_bridgeComponentOf hx]
    exact q.start_mem_support
  suffices ∀ {A B} (r : G.bridgeForest.Walk A B),
      r.edges ⊆ q.edges → A ∈ q.support → B ∈ q.support from this r hsub hstart
  intro A B r
  induction r with
  | nil => exact fun _ hstart ↦ hstart
  | cons e h r ih =>
      intro hsub _
      exact ih (fun f hf ↦ hsub (by simp [hf]))
        (q.mem_support_of_isLink_of_mem_edges h.symm (hsub (by simp)))

end Walk

end Graph
