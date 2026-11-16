/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Tensor products of commuting squares in a monoidal category

The interchange law `MonoidalCategory.tensorHom_comp_tensorHom` turns a pair of commuting squares
`f₁ ≫ g₁ = f₁' ≫ g₁'` and `f₂ ≫ g₂ = f₂' ≫ g₂'` in a monoidal category into the commuting square
`(f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁' ⊗ₘ f₂') ≫ (g₁' ⊗ₘ g₂')`. Packaging this as a single lemma avoids
repeating `tensorHom_comp_tensorHom` in both directions, especially when the intermediate objects
match only up to definitional equality so `rw` does not apply directly.

## Main results

* `TauCeti.tensorHom_comp_tensorHom_eq`: the tensor product of two commuting squares commutes.
-/

public section

namespace TauCeti

open CategoryTheory MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- The tensor product of two commuting squares in a monoidal category commutes: if
`f₁ ≫ g₁ = f₁' ≫ g₁'` and `f₂ ≫ g₂ = f₂' ≫ g₂'`, then
`(f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁' ⊗ₘ f₂') ≫ (g₁' ⊗ₘ g₂')`. -/
@[reassoc]
lemma tensorHom_comp_tensorHom_eq {X₁ Y₁ Z₁ W₁ X₂ Y₂ Z₂ W₂ : C}
    {f₁ : X₁ ⟶ Y₁} {g₁ : Y₁ ⟶ W₁} {f₁' : X₁ ⟶ Z₁} {g₁' : Z₁ ⟶ W₁}
    {f₂ : X₂ ⟶ Y₂} {g₂ : Y₂ ⟶ W₂} {f₂' : X₂ ⟶ Z₂} {g₂' : Z₂ ⟶ W₂}
    (h₁ : f₁ ≫ g₁ = f₁' ≫ g₁') (h₂ : f₂ ≫ g₂ = f₂' ≫ g₂') :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁' ⊗ₘ f₂') ≫ (g₁' ⊗ₘ g₂') := by
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, h₁, h₂]

end TauCeti
