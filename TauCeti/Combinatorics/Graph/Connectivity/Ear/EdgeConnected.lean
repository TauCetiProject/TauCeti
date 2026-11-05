/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.EdgeConnectivity

/-!
# Edge connectivity from ear decompositions

This file proves the forward direction of the ear characterization of `2`-edge-connected
multigraphs: adjoining an open or closed ear preserves `2`-edge-connectivity, so every graph
admitting an ear decomposition is `2`-edge-connected.  The proof works without finiteness
assumptions on the ambient vertex and edge types.

The key point is that an open ear, together with a path in the old graph between its endpoints,
places every new edge on a cycle.  A closed ear is already such a cycle.  Thus adjoining an ear
preserves both connectedness and the absence of bridges.

The argument follows the ear-decomposition proof of the bridge criterion in R. Diestel,
*Graph Theory*, Chapter 3, with edge identities retained for multigraphs.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G H : Graph α β}

namespace EarStart

/-- Every permitted initial graph for an ear decomposition is `2`-edge-connected. -/
theorem isEdgeConnected_two {K : Graph α β} (start : G.EarStart K) :
    K.IsEdgeConnected 2 := by
  cases start with
  | vertex v => exact IsEdgeConnected.of_subsingleton (by simp)
  | cycle p hp => exact hp.isEdgeConnected_two_walkGraph

end EarStart

namespace Ear

variable (ear : G.Ear H)

/-- Adjoining an ear to a connected graph preserves connectedness. -/
theorem connected_add (hH : H.Connected) : ear.add.Connected := by
  rw [connected_iff_forall_reachable]
  refine ⟨⟨ear.toWalk.1, by
    simp only [vertexSet_add, Set.mem_union]
    exact Or.inl ear.toWalk_fst_mem⟩, fun x y hx hy ↦ ?_⟩
  have toBase : ∀ {z}, z ∈ V(ear.add) → ear.add.Reachable z ear.toWalk.1 := by
    intro z hz
    simp only [vertexSet_add, Set.mem_union] at hz
    rcases hz with hz | hz
    · exact (hH.reachable hz ear.toWalk_fst_mem).mono ear.base_le_add
    · apply Reachable.mono ear.toGraph_le_add
      exact ear.connected_toGraph.reachable hz (by
        simpa only [Ear.vertexSet_toGraph, Set.mem_ofPred_eq] using
          ear.toWalk.2.2.start_mem_support)
  exact (toBase hx).trans (toBase hy).symm

/-- Every edge in the graph traced by an ear lies on a cycle after adjoining the ear to a
connected base graph. -/
theorem exists_isCycle_add_of_mem_edgeSet_toGraph (hH : H.Connected) {e : β}
    (he : e ∈ E(ear.toGraph)) :
    ∃ x, ∃ p : ear.add.Walk x x, p.IsCycle ∧ e ∈ p.edges := by
  cases ear with
  | @«open» hHG s t p hp hs ht hst hinter hedges =>
      rw [Ear.toGraph_open] at he
      obtain ⟨q, hq⟩ := (hH.reachable ht hs).exists_isPath
      let qG := q.mapLe hHG
      have hqG : qG.IsPath := (Walk.isPath_mapLe hHG q).mpr hq
      have hv : p.support.tail.Disjoint qG.support.tail := by
        rw [List.disjoint_left]
        intro z hzp hzq
        have hzq' : z ∈ q.support.tail := by
          simpa only [qG, Walk.support_mapLe_eq_support] using hzq
        have hpNodup := hp.support_nodup
        rw [← p.cons_tail_support] at hpNodup
        have hqNodup := hq.support_nodup
        rw [← q.cons_tail_support] at hqNodup
        have hzs : z ≠ s := fun hzs ↦ (List.nodup_cons.mp hpNodup).1 (hzs ▸ hzp)
        have hzt : z ≠ t := fun hzt ↦ (List.nodup_cons.mp hqNodup).1 (hzt ▸ hzq')
        exact hinter z (List.mem_of_mem_tail hzp) hzs hzt
          (q.support_subset_vertexSet ht z (List.mem_of_mem_tail hzq'))
      have hedisj : p.edges.Disjoint qG.edges := by
        rw [List.disjoint_left]
        intro f hfp hfq
        apply hedges f hfp
        apply q.edges_subset_edgeSet
        simpa only [qG, Walk.edges_mapLe_eq_edges] using hfq
      have hcycle : (p.append qG).IsCycle := hp.isCycle_append hqG hv hedisj
        (Or.inl (Nat.pos_of_ne_zero fun h ↦ hst (p.eq_of_length_eq_zero h)))
      let c := (p.append qG).transfer
        (Ear.open hHG p hp hs ht hst hinter hedges).add_le fun f hf ↦ by
          rw [Walk.edges_append] at hf
          rw [edgeSet_add]
          rcases List.mem_append.mp hf with hfp | hfq
          · exact Or.inr (by
              simpa only [Ear.toGraph_open] using (p.mem_edgeSet_walkGraph f).mpr hfp)
          · exact Or.inl (q.edges_subset_edgeSet (by
              simpa only [qG, Walk.edges_mapLe_eq_edges] using hfq))
      have hc : c.IsCycle := (Walk.isCycle_transfer
        (Ear.open hHG p hp hs ht hst hinter hedges).add_le (p.append qG) _).mpr hcycle
      have heP : e ∈ p.edges := (p.mem_edgeSet_walkGraph e).mp he
      exact ⟨s, c, hc, by
        simp only [c, Walk.edges_transfer, Walk.edges_append, List.mem_append]
        exact Or.inl heP⟩
  | @«closed» hHG s p hp hs hinter hedges =>
      rw [Ear.toGraph_closed] at he
      let c := p.transfer (Ear.closed hHG p hp hs hinter hedges).add_le fun f hf ↦ by
        rw [edgeSet_add]
        exact Or.inr (by
          simpa only [Ear.toGraph_closed] using (p.mem_edgeSet_walkGraph f).mpr hf)
      have hc : c.IsCycle := (Walk.isCycle_transfer
        (Ear.closed hHG p hp hs hinter hedges).add_le p _).mpr hp
      exact ⟨s, c, hc, by
        simpa only [c, Walk.edges_transfer] using (p.mem_edgeSet_walkGraph e).mp he⟩

/-- Adjoining an ear to a connected graph without bridges produces no bridge. -/
theorem not_isBridge_add (hH : H.Connected) (hbridge : ∀ e, ¬ H.IsBridge e) (e : β) :
    ¬ ear.add.IsBridge e := by
  intro he
  have heAdd := he.mem_edgeSet
  rw [edgeSet_add] at heAdd
  rcases heAdd with heH | heEar
  · exact hbridge e (he.anti_of_mem ear.base_le_add heH)
  obtain ⟨x, p, hp, hep⟩ := ear.exists_isCycle_add_of_mem_edgeSet_toGraph hH heEar
  exact hp.not_isBridge_of_le le_rfl hep he

/-- Adjoining an ear preserves `2`-edge-connectivity. -/
theorem isEdgeConnected_two_add (hH : H.IsEdgeConnected 2) : ear.add.IsEdgeConnected 2 := by
  have hV : V(H).Nonempty := by
    cases ear with
    | «open» _ _ _ hs => exact ⟨_, hs⟩
    | «closed» _ _ _ hs => exact ⟨_, hs⟩
  rw [isEdgeConnected_two_iff_connected_and_forall_not_isBridge hV] at hH
  rw [isEdgeConnected_two_iff_connected_and_forall_not_isBridge
    (ear.connected_add hH.1).nonempty]
  exact ⟨ear.connected_add hH.1, ear.not_isBridge_add hH.1 hH.2⟩

end Ear

namespace EarDecomposition

/-- Every graph admitting an ear decomposition is `2`-edge-connected. -/
theorem isEdgeConnected_two (d : G.EarDecomposition H) : H.IsEdgeConnected 2 := by
  rw [← d.graphAfter_last]
  exact d.graphAfter_induction (P := fun K ↦ K.IsEdgeConnected 2)
    (by rw [initial_eq_graphAfter]; exact d.start.isEdgeConnected_two)
    (fun i hi ↦ by
      rw [← d.earAt_fst i] at hi
      exact (d.earAt i).2.isEdgeConnected_two_add hi)
    (Fin.last d.length)

end EarDecomposition

end Graph
