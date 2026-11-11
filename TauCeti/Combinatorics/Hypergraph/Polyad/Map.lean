/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Basic
import TauCeti.Data.Fintype.CardEmbedding

/-!
# Mapping the cells and colors of polyads

Maps of partition parts and pair colors induce a map of polyad data. If both maps are
injective, so is the induced map of polyads. This construction does not assert that supports
are preserved: moving vertices between matched cells changes supports even when the pair
coloring is unchanged.

The `map_ofTriple` identity identifies the triples whose polyad data are preserved. It is
used to charge support changes during vertex-partition rebalancing to the moved vertices.
Coarse parents of polyads specialize the same construction to the refinement-parent map.
-/

public section

open Finset

namespace TauCeti.Polyad3

variable {κ κ' κ'' V : Type*} [Fintype V] [DecidableEq V]
  {S : PairSkeleton3 κ V} {T : PairSkeleton3 κ' V} {U : PairSkeleton3 κ'' V}

/-- Map the three cells and pair-color labels of a polyad. No compatibility between the two
skeletons' pair colorings is required. -/
def map (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ') :
    Polyad3 T :=
  ofData (f ⟨P.c₀, P.hc₀⟩) (f ⟨P.c₁, P.hc₁⟩) (f ⟨P.c₂, P.hc₂⟩)
    (f ⟨P.c₀, P.hc₀⟩).2 (f ⟨P.c₁, P.hc₁⟩).2 (f ⟨P.c₂, P.hc₂⟩).2
    (g P.color₀₁) (g P.color₀₂) (g P.color₁₂)

/-- The role-zero cell after mapping. -/
@[simp]
theorem map_c₀ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ') :
    (P.map f g).c₀ = (f ⟨P.c₀, P.hc₀⟩ : Finset V) := by simp [map]

/-- The role-one cell after mapping. -/
@[simp]
theorem map_c₁ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ') :
    (P.map f g).c₁ = (f ⟨P.c₁, P.hc₁⟩ : Finset V) := by simp [map]

/-- The role-two cell after mapping. -/
@[simp]
theorem map_c₂ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ') :
    (P.map f g).c₂ = (f ⟨P.c₂, P.hc₂⟩ : Finset V) := by simp [map]

/-- The color on roles zero and one after mapping. -/
@[simp]
theorem map_color₀₁ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ') :
    (P.map f g).color₀₁ = g P.color₀₁ := by simp [map]

/-- The color on roles zero and two after mapping. -/
@[simp]
theorem map_color₀₂ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ') :
    (P.map f g).color₀₂ = g P.color₀₂ := by simp [map]

/-- The color on roles one and two after mapping. -/
@[simp]
theorem map_color₁₂ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ') :
    (P.map f g).color₁₂ = g P.color₁₂ := by simp [map]

/-- Mapping cells and colors by the identity leaves a polyad unchanged. -/
@[simp]
theorem map_id (P : Polyad3 S) : P.map (T := S) id id = P := by
  ext <;> simp

/-- Successive maps of cells and colors compose. -/
@[simp]
theorem map_map (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ')
    (f' : T.vertexPart.parts → U.vertexPart.parts) (g' : κ' → κ'') :
    (P.map f g).map f' g' = P.map (f' ∘ f) (g' ∘ g) := by
  ext <;> simp

/-- Injective maps of cells and colors give an injective map of polyads. -/
theorem map_injective {f : S.vertexPart.parts → T.vertexPart.parts} {g : κ → κ'}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (fun P : Polyad3 S ↦ P.map f g) := by
  intro P Q h
  have h₀ := congrArg c₀ h
  have h₁ := congrArg c₁ h
  have h₂ := congrArg c₂ h
  simp only [map_c₀, map_c₁, map_c₂] at h₀ h₁ h₂
  exact ext_data (congrArg Subtype.val (hf (Subtype.ext h₀)))
    (congrArg Subtype.val (hf (Subtype.ext h₁)))
    (congrArg Subtype.val (hf (Subtype.ext h₂)))
    (hg (by simpa using congrArg color₀₁ h))
    (hg (by simpa using congrArg color₀₂ h)) (hg (by simpa using congrArg color₁₂ h))

/-- If the cells containing a triple map to its new cells and its pair colors map to its new
colors, its polyad maps to its new polyad. -/
theorem map_ofTriple (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ')
    (hcolors : ∀ p, g (S.pairColors.color p) = T.pairColors.color p)
    (x : {x : Fin 3 → V // Function.Injective x})
    (hcells : ∀ i, (f ⟨S.vertexPart.part (x.1 i),
      S.vertexPart.part_mem.2 (Finset.mem_univ _)⟩ : Finset V) = T.vertexPart.part (x.1 i)) :
    (ofTriple S x).map f g = ofTriple T x := by
  apply ext_data
  · simpa using hcells 0
  · simpa using hcells 1
  · simpa using hcells 2
  · simpa using hcolors (coordPair x 0 1 (by decide))
  · simpa using hcolors (coordPair x 0 2 (by decide))
  · simpa using hcolors (coordPair x 1 2 (by decide))

/-- If vertices outside `B` stay in their matched cells and pair colors map to the new colors,
at most `3 |B| |V|²` triples change their polyad data under the matching. -/
theorem card_ofTriple_ne_map_le [DecidableEq κ']
    (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ')
    (hcolors : ∀ p, g (S.pairColors.color p) = T.pairColors.color p) (B : Finset V)
    (hcells : ∀ v ∉ B, (f ⟨S.vertexPart.part v,
      S.vertexPart.part_mem.2 (mem_univ _)⟩ : Finset V) = T.vertexPart.part v) :
    #{x | ofTriple T x ≠ (ofTriple S x).map f g} ≤
      3 * #B * Fintype.card V ^ 2 := by
  calc _ ≤ #{x : {x : Fin 3 → V // Function.Injective x} | ∃ i, x.1 i ∈ B} := by
          refine card_le_card fun x hx ↦ mem_filter.2 ⟨mem_univ _, ?_⟩
          by_contra! h
          exact (mem_filter.1 hx).2
            (map_ofTriple f g hcolors x (fun i ↦ hcells _ (h i))).symm
    _ ≤ _ := card_filter_injective_exists_mem_le B

end TauCeti.Polyad3
