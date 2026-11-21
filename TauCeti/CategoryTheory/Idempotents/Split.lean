/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Sums of orthogonal split idempotents

An idempotent `e` of `X` splits when `e = r ≫ i` for morphisms `i : Y ⟶ X` and `r : X ⟶ Y` with
`i ≫ r = 𝟙 Y`, as in Mathlib's `CategoryTheory.IsIdempotentComplete`. In a preadditive category
with binary biproducts, the sum of two orthogonal split idempotents splits through the biproduct
of their images.

## Main results

* `TauCeti.exists_split_add_of_comp_eq_zero`: the sum of two orthogonal split idempotents splits.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- **Orthogonal split idempotents have a split sum**: if `e₁` and `e₂` split and `e₁ ≫ e₂ = 0 =
e₂ ≫ e₁`, then `e₁ + e₂` splits, through the biproduct of the two images. -/
theorem exists_split_add_of_comp_eq_zero {X : C} {e₁ e₂ : X ⟶ X}
    (h₁ : ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e₁)
    (h₂ : ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e₂)
    (h₁₂ : e₁ ≫ e₂ = 0) (h₂₁ : e₂ ≫ e₁ = 0) :
    ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e₁ + e₂ := by
  obtain ⟨Y₁, i₁, r₁, hi₁, rfl⟩ := h₁
  obtain ⟨Y₂, i₂, r₂, hi₂, rfl⟩ := h₂
  have h₁₂' : i₁ ≫ r₂ = 0 := by
    simpa [reassoc_of% hi₁, hi₂] using i₁ ≫= h₁₂ =≫ r₂
  have h₂₁' : i₂ ≫ r₁ = 0 := by
    simpa [reassoc_of% hi₂, hi₁] using i₂ ≫= h₂₁ =≫ r₁
  refine ⟨Y₁ ⊞ Y₂, biprod.desc i₁ i₂, biprod.lift r₁ r₂, ?_, by simp⟩
  ext <;> simp [hi₁, hi₂, h₁₂', h₂₁']

end TauCeti
