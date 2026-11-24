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
-/

public section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.KPresheaf

variable {X : TopCat} [T2Space X] {A : Type*} [Category* A] (F : KPresheaf A X)

/-- The restriction maps of a K-presheaf along a bicartesian square `K₁ = K₂ ⊓ K₃`,
`K₄ = K₂ ⊔ K₃` of compact sets form a commutative square. -/
theorem commSq_map {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    CommSq (F.map (opHomOfLE h.le₂₄)) (F.map (opHomOfLE h.le₃₄)) (F.map (opHomOfLE h.le₁₂))
      (F.map (opHomOfLE h.le₁₃)) :=
  ⟨by simp only [← F.map_comp]; rfl⟩

end TopCat.KPresheaf
