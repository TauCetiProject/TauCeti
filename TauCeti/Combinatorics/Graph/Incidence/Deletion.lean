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
Both formulas specialize the same edge-filtering argument for subgraphs.
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

-- Keep the target vertex finset explicit: callers can use their native vertex carrier without
-- transporting a vertex map underneath internalEdges or incidentEdges.
private theorem map_internalEdges_of_le {H : Graph α β} [Fintype E(G)] [Fintype E(H)]
    [DecidablePred (· ∈ E(H))]
    (h : H ≤ G) (fV : V(G) ↪ V(H)) (hfV : ∀ x, (fV x).1 = x.1)
    (S : Finset V(G)) (T : Finset V(H)) (hT : T = S.map fV) :
    (H.internalEdges T).map
        (Set.embeddingOfSubset _ _ h.edgeSet_mono) =
      (G.internalEdges S).filter (fun e ↦ e.1 ∈ E(H)) := by
  classical
  rw [hT]
  ext e
  simp only [Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := (mem_internalEdges _).1 hd
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨y, hyS, rfl⟩ := Finset.mem_map.1 hy
    exact ⟨(mem_internalEdges _).2
      ⟨x, hxS, y, hyS,
        by simpa only [hfV, Set.embeddingOfSubset_apply_coe] using hxy.mono h⟩, d.2⟩
  · rintro ⟨he, heH⟩
    refine ⟨⟨e.1, heH⟩, ?_, rfl⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := (mem_internalEdges _).1 he
    exact (mem_internalEdges _).2
      ⟨_, Finset.mem_map.2 ⟨x, hx, rfl⟩, _, Finset.mem_map.2 ⟨y, hy, rfl⟩,
        by simpa only [hfV] using (h.isLink_iff heH).2 hxy⟩

private theorem map_incidentEdges_of_le {H : Graph α β} [Fintype E(G)] [Fintype E(H)]
    [DecidablePred (· ∈ E(H))]
    (h : H ≤ G) (fV : V(G) ↪ V(H)) (hfV : ∀ x, (fV x).1 = x.1)
    (S : Finset V(G)) (T : Finset V(H)) (hT : T = S.map fV) :
    (H.incidentEdges T).map
        (Set.embeddingOfSubset _ _ h.edgeSet_mono) =
      (G.incidentEdges S).filter (fun e ↦ e.1 ∈ E(H)) := by
  classical
  rw [hT]
  ext e
  simp only [Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨x, hx, hdx⟩ := (mem_incidentEdges _).1 hd
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_map.1 hx
    exact ⟨(mem_incidentEdges _).2
      ⟨x, hxS, by simpa only [hfV, Set.embeddingOfSubset_apply_coe] using hdx.mono h⟩, d.2⟩
  · rintro ⟨he, heH⟩
    refine ⟨⟨e.1, heH⟩, ?_, rfl⟩
    obtain ⟨x, hx, hex⟩ := (mem_incidentEdges _).1 he
    exact (mem_incidentEdges _).2
      ⟨_, Finset.mem_map.2 ⟨x, hx, rfl⟩,
        by simpa only [hfV] using (h.inc_congr heH).2 hex⟩

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
  simpa using G.map_internalEdges_of_le (restrict_le (E₀ := E₀))
    (Function.Embedding.refl _) (fun _ ↦ rfl) S S Finset.map_refl.symm

/-- The incident edges of an edge restriction are the original incident edges in the
retained set, with their original identities. -/
@[simp]
theorem map_incidentEdges_restrict (S : Finset V(G)) :
    ((G.restrict E₀).incidentEdges S).map
        (Set.embeddingOfSubset _ _ (restrict_le (G := G) (E₀ := E₀)).edgeSet_mono) =
      (G.incidentEdges S).filter (fun e ↦ e.1 ∈ E₀) := by
  classical
  simpa using G.map_incidentEdges_of_le (restrict_le (E₀ := E₀))
    (Function.Embedding.refl _) (fun _ ↦ rfl) S S Finset.map_refl.symm

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

/-- The internal edges remaining after deletion are exactly the original internal edges not
selected for deletion, with their original identities. -/
@[simp]
theorem map_internalEdges_deleteEdges (S : Finset V(G)) :
    ((G.deleteEdges F).internalEdges S).map
        (Set.embeddingOfSubset _ _ (deleteEdges_le (G := G) (F := F)).edgeSet_mono) =
      (G.internalEdges S).filter (fun e ↦ e.1 ∉ F) := by
  classical
  simpa using G.map_internalEdges_of_le (deleteEdges_le (F := F))
    (Function.Embedding.refl _) (fun _ ↦ rfl) S S Finset.map_refl.symm

/-- The incident edges remaining after deletion are exactly the original incident edges not
selected for deletion, with their original identities. -/
@[simp]
theorem map_incidentEdges_deleteEdges (S : Finset V(G)) :
    ((G.deleteEdges F).incidentEdges S).map
        (Set.embeddingOfSubset _ _ (deleteEdges_le (G := G) (F := F)).edgeSet_mono) =
      (G.incidentEdges S).filter (fun e ↦ e.1 ∉ F) := by
  classical
  simpa using G.map_incidentEdges_of_le (deleteEdges_le (F := F))
    (Function.Embedding.refl _) (fun _ ↦ rfl) S S Finset.map_refl.symm

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
  rw [card_internalEdges_deleteEdges, add_comm]
  exact Finset.card_filter_add_card_filter_not _

/-- The surviving and deleted incident-edge counts add to the original incident-edge count. -/
theorem card_incidentEdges_deleteEdges_add_card_filter (S : Finset V(G)) :
    ((G.deleteEdges F).incidentEdges S).card +
        ((G.incidentEdges S).filter (fun e ↦ e.1 ∈ F)).card =
      (G.incidentEdges S).card := by
  rw [card_incidentEdges_deleteEdges, add_comm]
  exact Finset.card_filter_add_card_filter_not _

end Graph
