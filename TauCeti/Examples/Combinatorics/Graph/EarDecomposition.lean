/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Graph.Connectivity.Ear.EdgeConnected
import TauCeti.Combinatorics.Graph.Orientation.Walk
import Mathlib.Combinatorics.Quiver.ConnectedComponent

/-!
# Multigraph ear-decomposition and `2`-edge-connectivity examples

These examples illustrate how ear decompositions and `2`-edge-connectivity retain loop and
parallel-edge identities on multigraphs:

1. **Two vertices joined by two parallel edges (`banana 0 1 {0, 1}`), compared with its
   single-edge simplification.** The multigraph has edge connectivity `2`, an explicit two-edge
   cycle and two-edge closed ear over `{0}` assembling into a length-`1` vertex-started ear
   decomposition, and an explicit strongly connected orientation sending the two parallel edges in
   opposite directions. By contrast, its underlying simple graph `(banana 0 1 {0, 1}).toSimpleGraph`
   collapses the parallel pair into a single bridge, drops to edge connectivity `1`, and admits
   neither an ear decomposition nor a strongly connected orientation (illustrated on the
   single-edge multigraph `banana 0 1 {0}`).
2. **A loop on one vertex (`bouquet 0 {0}`).** The loop traces a one-edge cycle and a one-edge
   closed ear over `noEdge {0} ℕ`, giving a length-`1` vertex-started ear decomposition; the graph
   has no bridge, edge connectivity `⊤`, and empty edge cut along every vertex set.
-/

open Graph Set

/-! ### Two parallel edges versus the single-edge simplification -/

-- Two distinct vertices joined by two parallel edges have edge connectivity `2` and are
-- `2`-edge-connected.
example :
    let G : Graph ℕ ℕ := banana 0 1 {0, 1}
    G.edgeConnectivity = 2 ∧ G.IsEdgeConnected 2 := by
  intro G
  have hconn : G.edgeConnectivity = 2 := by
    dsimp only [G]
    rw [edgeConnectivity_banana (by decide), Set.encard_pair (by decide)]
  exact ⟨hconn, (isEdgeConnected_iff_le_edgeConnectivity 2).mpr (by simp [hconn])⟩

-- The two parallel edges `0` and `1` form a two-edge cycle and a two-edge closed ear over `{0}`,
-- giving an explicit vertex-started ear decomposition of length `1`.
example :
    let G : Graph ℕ ℕ := banana 0 1 {0, 1}
    ∃ (c : G.Walk 0 0) (d : G.EarDecomposition G) (hlen : d.length = 1),
      c.IsCycle ∧ c.edges = [0, 1] ∧ ¬ d.start.IsCycle ∧ d.kindAt ⟨0, by omega⟩ = .closed := by
  intro G
  have h01 : G.IsLink 0 0 1 := by simp [G]
  have h10 : G.IsLink 1 1 0 := by simp [G]
  let c : G.Walk 0 0 := .cons 0 h01 h10.toWalk
  have hc : c.IsCycle := by
    refine (Walk.cons_isCycle_iff 0 h01 h10.toWalk).mpr
      ⟨h10.isPath_toWalk_iff.mpr (by decide), ?_⟩
    simp [IsLink.edges_toWalk]
  let ear : G.Ear (Graph.noEdge {0} ℕ) := Ear.ofIsCycle c hc
  have hadd : ear.add = G := by
    refine (Compatible.of_le_le ear.add_le le_rfl).ext ?_ ?_
    · ext x
      simp only [ear, Ear.add_noEdge_singleton, Ear.toGraph_ofIsCycle, Walk.vertexSet_walkGraph, c,
        G, Walk.support_cons, IsLink.support_toWalk, vertexSet_banana, mem_insert_iff,
        mem_singleton_iff, mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false]
      omega
    · ext e
      simp [ear, c, G, IsLink.edges_toWalk]
  let d0 : G.EarDecomposition (Graph.noEdge {0} ℕ) :=
    EarDecomposition.vertex ⟨0, by simp [G]⟩
  let d : G.EarDecomposition G := (d0.snoc ear).copy hadd
  have hlen : d.length = 1 := by simp [d, d0]
  refine ⟨c, d, hlen, hc, by simp [c, IsLink.edges_toWalk], by simp [d, d0], ?_⟩
  have hidx : (⟨0, by omega⟩ : Fin d.length) =
      Fin.cast (EarDecomposition.length_copy _ hadd).symm
        (Fin.cast (EarDecomposition.length_snoc d0 ear).symm (Fin.last d0.length)) := by
    ext
    simp [d0]
  rw [hidx]
  dsimp only [d]
  rw [EarDecomposition.kindAt_copy, EarDecomposition.kindAt_snoc_last]
  dsimp only [ear]
  simp

-- Orienting edge `0` from `0` to `1` and edge `1` from `1` to `0` makes `banana 0 1 {0, 1}`
-- strongly connected.
example :
    let G : Graph ℕ ℕ := banana 0 1 {0, 1}
    ∃ o : G.Orientation,
      @Quiver.IsStronglyConnected V(G) ⟨o.Hom⟩ := by
  intro G
  let v0 : V(G) := ⟨0, by simp [G]⟩
  let v1 : V(G) := ⟨1, by simp [G]⟩
  let o : G.Orientation :=
    { tail e := if e.1 = 0 then v0 else v1
      head e := if e.1 = 0 then v1 else v0
      isLink e := by
        have he : e.1 = 0 ∨ e.1 = 1 := by simpa [G] using e.2
        rcases he with h | h <;> simp [h, v0, v1, G] }
  refine ⟨o, (@Quiver.isStronglyConnected_iff V(G) ⟨o.Hom⟩).mpr fun x y ↦ ?_⟩
  rw [o.nonempty_arrowWalk_iff]
  have hx : x = v0 ∨ x = v1 := by
    rcases (by simpa [G] using x.2 : x.1 = 0 ∨ x.1 = 1) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hy : y = v0 ∨ y = v1 := by
    rcases (by simpa [G] using y.2 : y.1 = 0 ∨ y.1 = 1) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have h01 : G.IsLink 0 0 1 := by simp [G]
  have h10 : G.IsLink 1 1 0 := by simp [G]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact ⟨.nil, by simp⟩
  · exact ⟨h01.toWalk, by simp [o, v0, v1]⟩
  · exact ⟨h10.toWalk, by simp [o, v0, v1]⟩
  · exact ⟨.nil, by simp⟩

-- Simplifying `banana 0 1 {0, 1}` to its underlying simple graph collapses the two parallel edges
-- into a single bridge, dropping edge connectivity to `1` and eliminating ear decompositions.
example :
    let G : Graph ℕ ℕ := banana 0 1 {0, 1}
    let H := G.toSimpleGraph
    let v0 : V(G) := ⟨0, by simp [G]⟩
    let v1 : V(G) := ⟨1, by simp [G]⟩
    H.Adj v0 v1 ∧ H.IsBridge s(v0, v1) ∧ H.edgeConnectivity = 1 ∧
      ¬ Nonempty ((Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)) := by
  intro G H v0 v1
  have hv01 : v0 ≠ v1 := fun h ↦ by simpa [v0, v1] using congrArg Subtype.val h
  have hV : ∀ u : V(G), u = v0 ∨ u = v1 := fun u ↦ by
    rcases (by simpa [G] using u.2 : u.1 = 0 ∨ u.1 = 1) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hadj01 : H.Adj v0 v1 := by
    rw [Graph.toSimpleGraph_adj]
    exact ⟨hv01, 0, by simp [G, v0, v1]⟩
  have hbridge : H.IsBridge s(v0, v1) := by
    rw [SimpleGraph.isBridge_iff_forall_walk_mem_edges]
    intro p
    generalize hv1 : v1 = x at p
    cases p with
    | nil => exact (hv01 hv1.symm).elim
    | @cons _ w _ hadj _ =>
        rcases hV w with rfl | rfl
        · exact (hadj.ne rfl).elim
        · simp [hv1]
  have hnot2 : ¬ H.IsEdgeConnected 2 := fun h2 ↦
    (SimpleGraph.isEdgeConnected_two_iff_forall_not_isBridge.mp h2) s(v0, v1) hbridge
  have hfin : Finite V(G) := by
    have : V(G) = {0, 1} := by simp [G]
    rw [this]
    infer_instance
  have : Nonempty V(G) := ⟨v0⟩
  have hnoEar :
      ¬ Nonempty ((Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)) := by
    rwa [← H.isEdgeConnected_two_iff_nonempty_earDecomposition]
  have h1 : H.IsEdgeConnected 1 := by
    rw [← Nat.cast_one, ← isEdgeConnected_ofSimpleGraph_iff, isEdgeConnected_one]
    intro x _ y _
    have h01' : (Graph.ofSimpleGraph H).IsLink s(v0, v1) v0 v1 := by
      simp [hadj01]
    rcases hV x with rfl | rfl <;> rcases hV y with rfl | rfl
    · exact .refl trivial
    · exact h01'.reachable
    · exact h01'.symm.reachable
    · exact .refl trivial
  have hconn : H.edgeConnectivity = 1 := by
    apply le_antisymm
    · by_contra! hlt
      have h2le : (2 : ℕ∞) ≤ H.edgeConnectivity := Order.succ_le_of_lt hlt
      exact hnot2 (SimpleGraph.isEdgeConnected_iff_le_edgeConnectivity.mpr h2le)
    · exact SimpleGraph.isEdgeConnected_iff_le_edgeConnectivity.mp h1
  exact ⟨hadj01, hbridge, hconn, hnoEar⟩

-- Likewise, the single-edge multigraph `banana 0 1 {0}` has edge `0` as a bridge, edge
-- connectivity `1`, no ear decomposition, and no strongly connected orientation.
example :
    let G : Graph ℕ ℕ := banana 0 1 {0}
    G.IsBridge 0 ∧ G.edgeConnectivity = 1 ∧ ¬ Nonempty (G.EarDecomposition G) ∧
      ∀ o : G.Orientation, ¬ @Quiver.IsStronglyConnected V(G) ⟨o.Hom⟩ := by
  intro G
  have h01 : G.IsLink 0 0 1 := by simp [G]
  have hbridge : G.IsBridge 0 := by
    rw [h01.isBridge_iff_not_reachable_deleteEdges]
    have hdel : G.deleteEdges {0} = banana 0 1 ∅ := by simp [G, banana_deleteEdges]
    rw [hdel, reachable_banana_iff (by decide)]
    simp
  have hconn : G.edgeConnectivity = 1 := by
    dsimp only [G]
    rw [edgeConnectivity_banana (by decide), Set.encard_singleton]
  have hfin : Finite E(G) := by
    have : E(G) = {0} := by simp [G]
    rw [this]
    infer_instance
  have hnoEar : ¬ Nonempty (G.EarDecomposition G) := by
    rw [← G.isEdgeConnected_two_iff_nonempty_earDecomposition ⟨0, by simp [G]⟩,
      isEdgeConnected_iff_le_edgeConnectivity, hconn]
    decide
  refine ⟨hbridge, hconn, hnoEar, fun o hsc ↦ ?_⟩
  let v0 : V(G) := ⟨0, by simp [G]⟩
  let v1 : V(G) := ⟨1, by simp [G]⟩
  let e0 : E(G) := ⟨0, by simp [G]⟩
  have hsc' := (@Quiver.isStronglyConnected_iff V(G) ⟨o.Hom⟩).mp hsc
  obtain ⟨p01, hp01⟩ := (o.nonempty_arrowWalk_iff v0 v1).mp (hsc' v0 v1)
  obtain ⟨p10, hp10⟩ := (o.nonempty_arrowWalk_iff v1 v0).mp (hsc' v1 v0)
  cases p01 with
  | @cons _ w _ f hf q =>
      have hf0 : f = 0 := by simpa [G] using hf.edge_mem
      subst hf0
      have hw1 : w = 1 := by simpa [G, v0] using hf
      subst hw1
      have hhead : (o.head e0 : ℕ) = 1 := (Walk.followsOrientation_cons hf q |>.mp hp01).2.1
      cases p10 with
      | @cons _ z _ g hg r =>
          have hg0 : g = 0 := by simpa [G] using hg.edge_mem
          subst hg0
          have htail : (o.tail e0 : ℕ) = 1 := (Walk.followsOrientation_cons hg r |>.mp hp10).1
          have hloop : G.IsLink 0 1 1 := by
            simpa [e0, htail, hhead] using o.isLink e0
          simp [G] at hloop

/-! ### A loop on one vertex -/

-- A single loop on one vertex forms a one-edge cycle and a one-edge closed ear over `noEdge {0} ℕ`,
-- has no bridge, has edge connectivity `⊤`, and contributes nothing to any edge cut.
example :
    let G : Graph ℕ ℕ := bouquet 0 {0}
    (∃ (c : G.Walk 0 0) (d : G.EarDecomposition G) (hlen : d.length = 1),
        c.IsCycle ∧ c.edges = [0] ∧ ¬ d.start.IsCycle ∧ d.kindAt ⟨0, by omega⟩ = .closed) ∧
      (∀ e, ¬ G.IsBridge e) ∧
      G.IsEdgeConnected 2 ∧
      G.edgeConnectivity = ⊤ ∧
      ∀ S : Set ℕ, G.edgeCut S = ∅ := by
  intro G
  have hloop : G.IsLoopAt 0 0 := by simp [G]
  have hl : G.IsLink 0 0 0 := isLink_self_iff.mpr hloop
  have hle : Graph.noEdge ({0} : Set ℕ) ℕ ≤ G :=
    Graph.noEdge_le_iff.mpr (by simp [G])
  let ear : G.Ear (Graph.noEdge {0} ℕ) :=
    Ear.ofIsLoopAt hle hloop (by simp) (by simp)
  have hadd : ear.add = G := by
    refine (Compatible.of_le_le ear.add_le le_rfl).ext ?_ ?_
    · ext x
      dsimp only [ear, G]
      simp
    · ext e
      dsimp only [ear, G]
      simp
  let d0 : G.EarDecomposition (Graph.noEdge {0} ℕ) :=
    EarDecomposition.vertex ⟨0, by simp [G]⟩
  let d : G.EarDecomposition G := (d0.snoc ear).copy hadd
  have hlen : d.length = 1 := by simp [d, d0]
  refine ⟨⟨hl.toWalk, d, hlen, hl.isCycle_toWalk, by simp [IsLink.edges_toWalk],
    by simp [d, d0], ?_⟩, ?_, d.isEdgeConnected_two, ?_, fun S ↦ ?_⟩
  · have hidx : (⟨0, by omega⟩ : Fin d.length) =
        Fin.cast (EarDecomposition.length_copy _ hadd).symm
          (Fin.cast (EarDecomposition.length_snoc d0 ear).symm (Fin.last d0.length)) := by
      ext
      simp [d0]
    rw [hidx]
    dsimp only [d]
    rw [EarDecomposition.kindAt_copy, EarDecomposition.kindAt_snoc_last]
    dsimp only [ear]
    simp
  · intro e he
    have he0 : e = 0 := by simpa [G] using he.mem_edgeSet
    subst he0
    exact hloop.not_isBridge he
  · exact edgeConnectivity_eq_top_of_subsingleton (by simp [G, Set.subsingleton_singleton])
  · ext e
    simp only [mem_empty_iff_false, iff_false]
    intro he
    have he0 : e = 0 := by
      obtain ⟨x, y, hxy, -, -⟩ := mem_edgeCut_iff.mp he
      simpa [G] using hxy.edge_mem
    subst he0
    exact hloop.notMem_edgeCut he
