/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Project
-/
module

public import TauCeti.Combinatorics.Graph.Incidence.Basic

/-!
# Internal and incident edges after restriction and deletion

Restricting edges filters internal and incident edges by the retained edge identities.
The deletion formulas follow by restricting to the complement of the deleted edges.
Deleting edges retains the actual vertex type, including isolated vertices. The finite sets of
internal and incident edges therefore compare on the same vertex set. Mapping surviving edge
identities into the original edge type identifies each set with the filter removing deleted edges.
The resulting counting identities split the original count into surviving and deleted identities,
counting parallel edges separately and loops once. No finiteness of the vertex set or ambient
vertex and edge types is needed.
-/

public section

namespace Graph

universe u v

variable {α : Type u} {β : Type v} (G : Graph α β)

section Restriction

variable (E₀ : Set β) [Fintype E(G)] [Fintype E(G.restrict E₀)]
variable [DecidablePred (· ∈ E₀)]

/-- The internal edges of an edge restriction are the original internal edges in the
retained set, with their original identities. -/
@[simp]
theorem map_internalEdges_restrict (S : Finset V(G)) :
    ((G.restrict E₀).internalEdges S).map
        (Set.embeddingOfSubset _ _ (restrict_le (G := G) (E₀ := E₀)).edgeSet_mono) =
      (G.internalEdges S).filter (fun e ↦ e.1 ∈ E₀) := by
  classical
  ext e
  simp only [Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := (mem_internalEdges _).1 hd
    exact ⟨(mem_internalEdges _).2 ⟨x, hx, y, hy, hxy.2⟩, d.2.2⟩
  · rintro ⟨he, heE⟩
    refine ⟨⟨e.1, e.2, heE⟩, ?_, rfl⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := (mem_internalEdges _).1 he
    exact (mem_internalEdges _).2 ⟨x, hx, y, hy, heE, hxy⟩

/-- The incident edges of an edge restriction are the original incident edges in the
retained set, with their original identities. -/
@[simp]
theorem map_incidentEdges_restrict (S : Finset V(G)) :
    ((G.restrict E₀).incidentEdges S).map
        (Set.embeddingOfSubset _ _ (restrict_le (G := G) (E₀ := E₀)).edgeSet_mono) =
      (G.incidentEdges S).filter (fun e ↦ e.1 ∈ E₀) := by
  classical
  ext e
  simp only [Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨x, hx, hdx⟩ := (mem_incidentEdges _).1 hd
    exact ⟨(mem_incidentEdges _).2 ⟨x, hx, (restrict_inc.1 hdx).1⟩, d.2.2⟩
  · rintro ⟨he, heE⟩
    refine ⟨⟨e.1, e.2, heE⟩, ?_, rfl⟩
    obtain ⟨x, hx, hex⟩ := (mem_incidentEdges _).1 he
    exact (mem_incidentEdges _).2 ⟨x, hx, restrict_inc.2 ⟨hex, heE⟩⟩

/-- Count internal edges of an edge restriction by filtering the original finite set. -/
theorem card_internalEdges_restrict (S : Finset V(G)) :
    ((G.restrict E₀).internalEdges S).card =
      ((G.internalEdges S).filter (fun e ↦ e.1 ∈ E₀)).card := by
  rw [← map_internalEdges_restrict, Finset.card_map]

/-- Count incident edges of an edge restriction by filtering the original finite set. -/
theorem card_incidentEdges_restrict (S : Finset V(G)) :
    ((G.restrict E₀).incidentEdges S).card =
      ((G.incidentEdges S).filter (fun e ↦ e.1 ∈ E₀)).card := by
  rw [← map_incidentEdges_restrict, Finset.card_map]

/-- The retained and omitted internal-edge counts add to the original internal-edge count. -/
theorem card_internalEdges_restrict_add_card_filter (S : Finset V(G)) :
    ((G.restrict E₀).internalEdges S).card +
        ((G.internalEdges S).filter (fun e ↦ e.1 ∉ E₀)).card =
      (G.internalEdges S).card := by
  rw [card_internalEdges_restrict]
  exact Finset.card_filter_add_card_filter_not _

/-- The retained and omitted incident-edge counts add to the original incident-edge count. -/
theorem card_incidentEdges_restrict_add_card_filter (S : Finset V(G)) :
    ((G.restrict E₀).incidentEdges S).card +
        ((G.incidentEdges S).filter (fun e ↦ e.1 ∉ E₀)).card =
      (G.incidentEdges S).card := by
  rw [card_incidentEdges_restrict]
  exact Finset.card_filter_add_card_filter_not _

end Restriction

variable (F : Set β) [Fintype E(G)] [Fintype E(G.deleteEdges F)]
variable [DecidablePred (· ∈ F)]

-- Mathlib deliberately makes the edge sets of deleteEdges F and restrict Fᶜ definitionally
-- equal, so they share the edge Fintype. Their vertex sets are both definitionally V(G).

/-- The internal edges remaining after deletion are exactly the original internal edges not
selected for deletion, with their original identities. -/
@[simp]
theorem map_internalEdges_deleteEdges (S : Finset V(G)) :
    ((G.deleteEdges F).internalEdges S).map
        (Set.embeddingOfSubset _ _ (deleteEdges_le (G := G) (F := F)).edgeSet_mono) =
      (G.internalEdges S).filter (fun e ↦ e.1 ∉ F) := by
  classical
  let : Fintype E(G.restrict Fᶜ) := ‹Fintype E(G.deleteEdges F)›
  erw [← G.map_internalEdges_restrict Fᶜ S]
  apply congrArg (Finset.map _)
  ext e
  erw [mem_internalEdges, mem_internalEdges]
  simp only [restrict_isLink, deleteEdges_isLink, Set.mem_compl_iff, and_comm]
  rfl

/-- The incident edges remaining after deletion are exactly the original incident edges not
selected for deletion, with their original identities. -/
@[simp]
theorem map_incidentEdges_deleteEdges (S : Finset V(G)) :
    ((G.deleteEdges F).incidentEdges S).map
        (Set.embeddingOfSubset _ _ (deleteEdges_le (G := G) (F := F)).edgeSet_mono) =
      (G.incidentEdges S).filter (fun e ↦ e.1 ∉ F) := by
  classical
  let : Fintype E(G.restrict Fᶜ) := ‹Fintype E(G.deleteEdges F)›
  erw [← G.map_incidentEdges_restrict Fᶜ S]
  apply congrArg (Finset.map _)
  ext e
  erw [mem_incidentEdges, mem_incidentEdges]
  simp only [restrict_inc, deleteEdges_inc, Set.mem_compl_iff]
  rfl

/-- Count internal edges after deletion by filtering the original finite set. -/
theorem card_internalEdges_deleteEdges (S : Finset V(G)) :
    ((G.deleteEdges F).internalEdges S).card =
      ((G.internalEdges S).filter (fun e ↦ e.1 ∉ F)).card := by
  rw [← map_internalEdges_deleteEdges, Finset.card_map]

/-- Count incident edges after deletion by filtering the original finite set. -/
theorem card_incidentEdges_deleteEdges (S : Finset V(G)) :
    ((G.deleteEdges F).incidentEdges S).card =
      ((G.incidentEdges S).filter (fun e ↦ e.1 ∉ F)).card := by
  rw [← map_incidentEdges_deleteEdges, Finset.card_map]

/-- The surviving and deleted internal-edge counts add to the original internal-edge count. -/
theorem card_internalEdges_deleteEdges_add_card_filter (S : Finset V(G)) :
    ((G.deleteEdges F).internalEdges S).card +
        ((G.internalEdges S).filter (fun e ↦ e.1 ∈ F)).card =
      (G.internalEdges S).card := by
  classical
  let : Fintype E(G.restrict Fᶜ) := ‹Fintype E(G.deleteEdges F)›
  rw [card_internalEdges_deleteEdges]
  have h := G.card_internalEdges_restrict_add_card_filter Fᶜ S
  erw [card_internalEdges_restrict] at h
  simpa only [Set.mem_compl_iff, not_not] using h

/-- The surviving and deleted incident-edge counts add to the original incident-edge count. -/
theorem card_incidentEdges_deleteEdges_add_card_filter (S : Finset V(G)) :
    ((G.deleteEdges F).incidentEdges S).card +
        ((G.incidentEdges S).filter (fun e ↦ e.1 ∈ F)).card =
      (G.incidentEdges S).card := by
  classical
  let : Fintype E(G.restrict Fᶜ) := ‹Fintype E(G.deleteEdges F)›
  rw [card_incidentEdges_deleteEdges]
  have h := G.card_incidentEdges_restrict_add_card_filter Fᶜ S
  erw [card_incidentEdges_restrict] at h
  simpa only [Set.mem_compl_iff, not_not] using h

end Graph
