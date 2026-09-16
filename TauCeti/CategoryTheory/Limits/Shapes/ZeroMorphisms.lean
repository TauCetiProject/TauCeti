/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Vanishing of maps induced on quotients

In a category with zero morphisms, a composite of two maps induced on quotients vanishes as soon as
the final quotient map kills the morphism inducing the first one.  This is the complex condition
for sequences of quotients such as `coker f ⟶ coker (f ≫ g) ⟶ coker g`.
-/

public section

open CategoryTheory Limits

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {Y Z Q₁ Q₂ Q₃ : C} {g : Y ⟶ Z}
  {π₁ : Y ⟶ Q₁} {π₂ : Z ⟶ Q₂} {π₃ : Z ⟶ Q₃} {u : Q₁ ⟶ Q₂} {v : Q₂ ⟶ Q₃}

/-- If `π₁`, `π₂` and `π₃` are quotient maps making `u` and `v` the maps induced on quotients by
`g` and by the identity, and `π₃` kills the image of `g`, then `u ≫ v = 0`. -/
theorem comp_eq_zero_of_epi (hπ₁ : Epi π₁) (w₃ : g ≫ π₃ = 0) (hu : π₁ ≫ u = g ≫ π₂)
    (hv : π₂ ≫ v = π₃) : u ≫ v = 0 := by
  have := hπ₁
  rw [← cancel_epi π₁, ← Category.assoc, hu, Category.assoc, hv, w₃, comp_zero]

end TauCeti
