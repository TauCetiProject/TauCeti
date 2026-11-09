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
  have hV : V(H).Nonempty := ⟨_, ear.toWalk_fst_mem⟩
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
