/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.Graph.Incidence.Basic
public import TauCeti.Combinatorics.Graph.Union

/-!
# Internal and incident edges of compatible unions

For a finite set of ambient vertices, the internal edges of a compatible union are exactly the
union of the internal edges in each graph; the same holds for incident edges. The edge sets are
mapped into the common ambient edge type, retaining their identities. Consequently their counts
add when the two graphs have disjoint edge sets, even if they share vertices.

Only the actual edge sets must be finite. Neither the ambient types nor the actual vertex sets
need be finite. Loops count once and parallel edges count separately.
-/

public section

open Finset

universe u v

namespace Graph.Compatible

variable {α : Type u} {β : Type v} {G H : Graph α β}
variable [Fintype E(G)] [Fintype E(H)]

open Classical in
/-- Internal edge identities of a compatible union come from the internal edges in its two
inputs, with the vertex set restricted to the actual vertices of each graph. -/
@[simp]
theorem map_internalEdges_union (h : G.Compatible H) [Fintype E(h.union)] (S : Finset α) :
    (h.union.internalEdges (S.subtype (· ∈ V(h.union)))).map (.subtype _) =
      (G.internalEdges (S.subtype (· ∈ V(G)))).map (.subtype _) ∪
        (H.internalEdges (S.subtype (· ∈ V(H)))).map (.subtype _) := by
  ext e
  simp only [mem_union, mem_map_internalEdges_subtype, h.union_isLink, and_or_left, exists_or]

open Classical in
/-- Incident edge identities of a compatible union come from the incident edges in its two
inputs. An edge incident to several selected vertices still occurs only once. -/
@[simp]
theorem map_incidentEdges_union (h : G.Compatible H) [Fintype E(h.union)] (S : Finset α) :
    (h.union.incidentEdges (S.subtype (· ∈ V(h.union)))).map (.subtype _) =
      (G.incidentEdges (S.subtype (· ∈ V(G)))).map (.subtype _) ∪
        (H.incidentEdges (S.subtype (· ∈ V(H)))).map (.subtype _) := by
  ext e
  simp only [mem_union, mem_map_incidentEdges_subtype, h.union_inc_iff, and_or_left, exists_or]

open Classical in
/-- Internal-edge counts add over a compatible union with disjoint edge sets. The graphs may
share vertices, and edges internal to the selected set are counted once each. -/
theorem card_internalEdges_union (h : G.Compatible H) [Fintype E(h.union)]
    (hE : Disjoint E(G) E(H)) (S : Finset α) :
    (h.union.internalEdges (S.subtype (· ∈ V(h.union)))).card =
      (G.internalEdges (S.subtype (· ∈ V(G)))).card +
        (H.internalEdges (S.subtype (· ∈ V(H)))).card := by
  rw [← card_map (Function.Embedding.subtype _), h.map_internalEdges_union S,
    card_union_of_disjoint, card_map, card_map]
  refine disjoint_left.mpr ?_
  intro e heG heH
  obtain ⟨eG, -, rfl⟩ := mem_map.mp heG
  obtain ⟨eH, -, heH⟩ := mem_map.mp heH
  have heq : eH.1 = eG.1 := heH
  exact hE.notMem_of_mem_left eG.2 (heq ▸ eH.2)

open Classical in
/-- Incident-edge counts add over a compatible union with disjoint edge sets, including when a
selected vertex belongs to both inputs. -/
theorem card_incidentEdges_union (h : G.Compatible H) [Fintype E(h.union)]
    (hE : Disjoint E(G) E(H)) (S : Finset α) :
    (h.union.incidentEdges (S.subtype (· ∈ V(h.union)))).card =
      (G.incidentEdges (S.subtype (· ∈ V(G)))).card +
        (H.incidentEdges (S.subtype (· ∈ V(H)))).card := by
  rw [← card_map (Function.Embedding.subtype _), h.map_incidentEdges_union S,
    card_union_of_disjoint, card_map, card_map]
  refine disjoint_left.mpr ?_
  intro e heG heH
  obtain ⟨eG, -, rfl⟩ := mem_map.mp heG
  obtain ⟨eH, -, heH⟩ := mem_map.mp heH
  have heq : eH.1 = eG.1 := heH
  exact hE.notMem_of_mem_left eG.2 (heq ▸ eH.2)

end Graph.Compatible
