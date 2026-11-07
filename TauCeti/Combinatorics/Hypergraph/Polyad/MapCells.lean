/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Basic
import TauCeti.Data.Fintype.CardEmbedding

/-!
# Mapping the vertex cells of polyads

A map between the parts of two lower skeletons induces a map of polyad data, preserving the
three pair-color labels. An injective map of cells gives an injective map of polyads. This
construction does not assert that supports are preserved: moving vertices between matched
cells changes supports even when the pair coloring is unchanged.

The `mapCells_ofTriple` identity identifies the triples whose polyad data are preserved. It is
used to charge support changes during vertex-partition rebalancing to the moved vertices.
-/

public section

open Finset

namespace TauCeti.Polyad3

variable {κ V : Type*} [Fintype V] [DecidableEq V]
  {S T U : PairSkeleton3 κ V}

/-- Replace the three cells of a polyad using a map of partition parts, retaining its three
pair-color labels. No compatibility between the two skeletons' pair colorings is required. -/
def mapCells (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) : Polyad3 T :=
  ofData (f ⟨P.c₀, P.hc₀⟩) (f ⟨P.c₁, P.hc₁⟩) (f ⟨P.c₂, P.hc₂⟩)
    (f ⟨P.c₀, P.hc₀⟩).2 (f ⟨P.c₁, P.hc₁⟩).2 (f ⟨P.c₂, P.hc₂⟩).2
    P.color₀₁ P.color₀₂ P.color₁₂

/-- The role-zero cell after mapping cells. -/
@[simp]
theorem mapCells_c₀ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) :
    (P.mapCells f).c₀ = (f ⟨P.c₀, P.hc₀⟩ : Finset V) := by simp [mapCells]

/-- The role-one cell after mapping cells. -/
@[simp]
theorem mapCells_c₁ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) :
    (P.mapCells f).c₁ = (f ⟨P.c₁, P.hc₁⟩ : Finset V) := by simp [mapCells]

/-- The role-two cell after mapping cells. -/
@[simp]
theorem mapCells_c₂ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) :
    (P.mapCells f).c₂ = (f ⟨P.c₂, P.hc₂⟩ : Finset V) := by simp [mapCells]

/-- Mapping cells preserves the color on roles zero and one. -/
@[simp]
theorem mapCells_color₀₁ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) :
    (P.mapCells f).color₀₁ = P.color₀₁ := by simp [mapCells]

/-- Mapping cells preserves the color on roles zero and two. -/
@[simp]
theorem mapCells_color₀₂ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) :
    (P.mapCells f).color₀₂ = P.color₀₂ := by simp [mapCells]

/-- Mapping cells preserves the color on roles one and two. -/
@[simp]
theorem mapCells_color₁₂ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) :
    (P.mapCells f).color₁₂ = P.color₁₂ := by simp [mapCells]

/-- Mapping cells by the identity leaves a polyad unchanged. -/
@[simp]
theorem mapCells_id (P : Polyad3 S) : P.mapCells (T := S) id = P := by
  ext <;> simp

/-- Successive maps of cells compose. -/
@[simp]
theorem mapCells_mapCells (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts)
    (g : T.vertexPart.parts → U.vertexPart.parts) :
    (P.mapCells f).mapCells g = P.mapCells (g ∘ f) := by
  ext <;> simp

/-- An injective map of cells gives an injective map of polyads. -/
theorem mapCells_injective {f : S.vertexPart.parts → T.vertexPart.parts}
    (hf : Function.Injective f) : Function.Injective (fun P : Polyad3 S ↦ P.mapCells f) := by
  intro P Q h
  have h₀ := congrArg c₀ h
  have h₁ := congrArg c₁ h
  have h₂ := congrArg c₂ h
  simp only [mapCells_c₀, mapCells_c₁, mapCells_c₂] at h₀ h₁ h₂
  apply ext_data (congrArg Subtype.val (hf (Subtype.ext h₀)))
    (congrArg Subtype.val (hf (Subtype.ext h₁)))
    (congrArg Subtype.val (hf (Subtype.ext h₂)))
  · simpa using congrArg color₀₁ h
  · simpa using congrArg color₀₂ h
  · simpa using congrArg color₁₂ h

/-- If the cells containing a triple map to its new cells and its pair colors are unchanged,
its polyad maps to its new polyad. -/
theorem mapCells_ofTriple (f : S.vertexPart.parts → T.vertexPart.parts)
    (hcolors : ∀ p, S.pairColors.color p = T.pairColors.color p)
    (x : {x : Fin 3 → V // Function.Injective x})
    (hcells : ∀ i, (f ⟨S.vertexPart.part (x.1 i),
      S.vertexPart.part_mem.2 (Finset.mem_univ _)⟩ : Finset V) = T.vertexPart.part (x.1 i)) :
    (ofTriple S x).mapCells f = ofTriple T x := by
  apply ext_data
  · simpa using hcells 0
  · simpa using hcells 1
  · simpa using hcells 2
  · simpa using hcolors (coordPair x 0 1 (by decide))
  · simpa using hcolors (coordPair x 0 2 (by decide))
  · simpa using hcolors (coordPair x 1 2 (by decide))

open Classical in
/-- If vertices outside `B` stay in their matched cells and pair colors are unchanged, at
most `3 |B| |V|²` triples change their polyad data under the matching. -/
theorem card_ofTriple_ne_mapCells_le (f : S.vertexPart.parts → T.vertexPart.parts)
    (hcolors : ∀ p, S.pairColors.color p = T.pairColors.color p) (B : Finset V)
    (hcells : ∀ v ∉ B, (f ⟨S.vertexPart.part v,
      S.vertexPart.part_mem.2 (mem_univ _)⟩ : Finset V) = T.vertexPart.part v) :
    #{x | ofTriple T x ≠ (ofTriple S x).mapCells f} ≤
      3 * #B * Fintype.card V ^ 2 := by
  calc _ ≤ #{x : {x : Fin 3 → V // Function.Injective x} | ∃ i, x.1 i ∈ B} := by
          refine card_le_card fun x hx ↦ mem_filter.2 ⟨mem_univ _, ?_⟩
          by_contra! h
          exact (mem_filter.1 hx).2
            (mapCells_ofTriple f hcolors x (fun i ↦ hcells _ (h i))).symm
    _ ≤ _ := card_filter_injective_exists_mem_le B

end TauCeti.Polyad3
