/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Combinatorics.Graph.Incidence.Basic
public import TauCeti.Combinatorics.Graph.Union

/-!
# Internal and incident edges of compatible unions

For a finite ambient vertex set `S`, restrict `S` to each graph's actual vertices using
`Finset.preimage`. Mapping the resulting internal or incident edges to their ambient edge
identities puts the three edge sets in a common carrier. They then commute with compatible
unions. When the two graphs have disjoint edge sets, their counts add, even if vertices are
shared. Loops count once and parallel edges retain their separate identities.

Only actual edge sets must be finite; neither vertex sets nor ambient types need be finite.
-/

public section

namespace Graph.Compatible

variable {α β : Type*} {G H : Graph α β}
variable (h : G.Compatible H)
variable [Fintype E(G)] [Fintype E(H)] [Fintype E(h.union)]

/-- Internal edge identities commute with compatible union, restricting the same ambient
vertex set to each graph. -/
@[simp]
theorem map_internalEdges_union [DecidableEq β] (S : Finset α) :
    (h.union.internalEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).map
        (Function.Embedding.subtype _) =
      (G.internalEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).map
          (Function.Embedding.subtype _) ∪
        (H.internalEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).map
          (Function.Embedding.subtype _) := by
  ext e
  simp only [Finset.mem_union, mem_map_internalEdges_preimage, h.union_isLink]
  aesop

/-- Incident edge identities commute with compatible union, restricting the same ambient
vertex set to each graph. -/
@[simp]
theorem map_incidentEdges_union [DecidableEq β] (S : Finset α) :
    (h.union.incidentEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).map
        (Function.Embedding.subtype _) =
      (G.incidentEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).map
          (Function.Embedding.subtype _) ∪
        (H.incidentEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).map
          (Function.Embedding.subtype _) := by
  ext e
  simp only [Finset.mem_union, mem_map_incidentEdges_preimage, h.union_inc_iff]
  aesop

/-- Counts of internal edges add when the input edge identities are disjoint.
No disjointness of the vertex sets is required. -/
theorem card_internalEdges_union (hd : Disjoint E(G) E(H)) (S : Finset α) :
    (h.union.internalEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).card =
      (G.internalEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).card +
        (H.internalEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).card := by
  classical
  have hd' : Disjoint
      ((G.internalEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).map
        (Function.Embedding.subtype _))
      ((H.internalEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).map
        (Function.Embedding.subtype _)) := by
    apply Finset.disjoint_left.mpr
    intro e heG heH
    obtain ⟨x, hx, y, hy, hG⟩ := (mem_map_internalEdges_preimage G S e).mp heG
    obtain ⟨z, hz, w, hw, hH⟩ := (mem_map_internalEdges_preimage H S e).mp heH
    exact Set.disjoint_left.mp hd hG.edge_mem hH.edge_mem
  simpa only [Finset.card_map] using
    congrArg Finset.card (h.map_internalEdges_union S) |>.trans (Finset.card_union_of_disjoint hd')

/-- Counts of incident edges add when the input edge identities are disjoint.
A loop or an edge incident with two selected vertices still contributes only once. -/
theorem card_incidentEdges_union (hd : Disjoint E(G) E(H)) (S : Finset α) :
    (h.union.incidentEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).card =
      (G.incidentEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).card +
        (H.incidentEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).card := by
  classical
  have hd' : Disjoint
      ((G.incidentEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).map
        (Function.Embedding.subtype _))
      ((H.incidentEdges (S.preimage Subtype.val Subtype.val_injective.injOn)).map
        (Function.Embedding.subtype _)) := by
    apply Finset.disjoint_left.mpr
    intro e heG heH
    obtain ⟨x, hx, hG⟩ := (mem_map_incidentEdges_preimage G S e).mp heG
    obtain ⟨y, hy, hH⟩ := (mem_map_incidentEdges_preimage H S e).mp heH
    exact Set.disjoint_left.mp hd hG.edge_mem hH.edge_mem
  simpa only [Finset.card_map] using
    congrArg Finset.card (h.map_incidentEdges_union S) |>.trans (Finset.card_union_of_disjoint hd')

end Graph.Compatible
