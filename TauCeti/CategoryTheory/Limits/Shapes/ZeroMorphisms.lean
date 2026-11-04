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

/-- Let `u` and `v` be the maps induced by `g` and by the identity on the targets of `π₁`, `π₂` and
`π₃`, in the sense that `π₁ ≫ u = g ≫ π₂` and `π₂ ≫ v = π₃`. If `π₁` is an epimorphism and
`g ≫ π₃ = 0`, then `u ≫ v = 0`. -/
theorem comp_eq_zero_of_epi (hπ₁ : Epi π₁) (w₃ : g ≫ π₃ = 0) (hu : π₁ ≫ u = g ≫ π₂)
    (hv : π₂ ≫ v = π₃) : u ≫ v = 0 :=
  hπ₁.left_cancellation _ _ (by simp [reassoc_of% hu, hv, w₃])

end TauCeti
