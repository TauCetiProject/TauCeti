/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.KSheaf

/-!
# Basic facts about K-presheaves

This file collects general facts about Mathlib's K-presheaves (`TopCat.KPresheaf`) with values in
an arbitrary category.

## Main results

* `TopCat.KPresheaf.commSq_map`: the restriction maps of a K-presheaf along a bicartesian square
  of compact sets form a commutative square.
* `TopCat.KPresheaf.mono_coe_functor_op_comp_map`: the diagram of `coconeOfCompacts K` sends a
  morphism between compact neighbourhoods of `K` to the corresponding restriction map.
-/

public section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.KPresheaf

variable {X : TopCat} {A : Type*} [Category* A] (F : KPresheaf A X)

/-- The diagram `(Set.mono_coe K.compactNhds).functor.op ⋙ F` of the cocone `F.coconeOfCompacts K`
sends a morphism `f : L ⟶ M` between compact neighbourhoods of `K` (so `M ⊆ L`) to the restriction
map `F.map (opHomOfLE _)` from `L` to `M`. -/
theorem mono_coe_functor_op_comp_map {K : Compacts X} {L M : (K.compactNhds)ᵒᵖ} (f : L ⟶ M) :
    ((Set.mono_coe K.compactNhds).functor.op ⋙ F).map f =
      F.map (opHomOfLE (show M.unop.val ≤ L.unop.val from leOfHom f.unop)) :=
  rfl

variable [T2Space X]

/-- The restriction maps of a K-presheaf along a bicartesian square `K₁ = K₂ ⊓ K₃`,
`K₄ = K₂ ⊔ K₃` of compact sets form a commutative square. -/
theorem commSq_map {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    CommSq (F.map (opHomOfLE h.le₂₄)) (F.map (opHomOfLE h.le₃₄)) (F.map (opHomOfLE h.le₁₂))
      (F.map (opHomOfLE h.le₁₃)) :=
  ⟨by simp only [← F.map_comp]; rfl⟩

end TopCat.KPresheaf
