/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Project
-/
module

public import TauCeti.Combinatorics.Graph.Incidence.Basic

/-!
# Internal and incident edges after deletion

Deleting edges retains the actual vertex type, including isolated vertices. The finite sets of
internal and incident edges therefore compare on the same vertex set. Mapping surviving edge
identities into the original edge type identifies each set with the filter removing deleted edges.
The resulting counting identities split the original count into surviving and deleted identities,
counting parallel edges separately and loops once. No finiteness of the vertex set or ambient
vertex and edge types is needed.
-/

public section

namespace Graph

open Function

universe u v

variable {α : Type u} {β : Type v} (G : Graph α β) (F : Set β)
variable [Fintype E(G)] [Fintype E(G.deleteEdges F)]
variable [DecidablePred (· ∈ F)]

/-- The internal edges remaining after deletion are exactly the original internal edges not
selected for deletion, with their original identities. -/
@[simp]
theorem map_internalEdges_deleteEdges (S : Finset V(G)) :
    ((G.deleteEdges F).internalEdges S).map
        ((Embedding.refl β).subtypeMap (deleteEdges_le (G := G) (F := F)).edgeSet_mono) =
      (G.internalEdges S).filter (fun e ↦ e.1 ∉ F) := by
  classical
  ext e
  simp only [Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := (mem_internalEdges _).1 hd
    exact ⟨(mem_internalEdges _).2 ⟨x, hx, y, hy, hxy.1⟩, d.2.2⟩
  · rintro ⟨he, heF⟩
    refine ⟨⟨e.1, e.2, heF⟩, ?_, rfl⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := (mem_internalEdges _).1 he
    exact (mem_internalEdges _).2 ⟨x, hx, y, hy, hxy, heF⟩

/-- The incident edges remaining after deletion are exactly the original incident edges not
selected for deletion, with their original identities. -/
@[simp]
theorem map_incidentEdges_deleteEdges (S : Finset V(G)) :
    ((G.deleteEdges F).incidentEdges S).map
        ((Embedding.refl β).subtypeMap (deleteEdges_le (G := G) (F := F)).edgeSet_mono) =
      (G.incidentEdges S).filter (fun e ↦ e.1 ∉ F) := by
  classical
  ext e
  simp only [Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨x, hx, hdx⟩ := (mem_incidentEdges _).1 hd
    exact ⟨(mem_incidentEdges _).2 ⟨x, hx, (deleteEdges_inc.1 hdx).1⟩, d.2.2⟩
  · rintro ⟨he, heF⟩
    refine ⟨⟨e.1, e.2, heF⟩, ?_, rfl⟩
    obtain ⟨x, hx, hex⟩ := (mem_incidentEdges _).1 he
    exact (mem_incidentEdges _).2 ⟨x, hx, deleteEdges_inc.2 ⟨hex, heF⟩⟩

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
