/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Quadratic characters under level changes

Being quadratic is preserved by lifting a Dirichlet character to a multiple of its level. That a
finite product of quadratic characters is quadratic holds for arbitrary multiplicative characters
(`MulChar.isQuadratic_prod`, in `TauCeti.NumberTheory.MulChar.Basic`).

## Main results

* `DirichletCharacter.isQuadratic_changeLevel`: lifting a quadratic character to a multiple of
  its level leaves it quadratic.
-/

public section

namespace DirichletCharacter

/-- Lifting a quadratic character to a multiple of its level leaves it quadratic. -/
theorem isQuadratic_changeLevel {R : Type*} [CommRing R]
    {n m : ℕ} {χ : DirichletCharacter R n} (hχ : χ.IsQuadratic) (h : n ∣ m) :
    (changeLevel h χ).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · rw [← ha.unit_spec, changeLevel_eq_cast_of_dvd]
    exact hχ _
  · exact Or.inl (MulChar.map_nonunit _ ha)

end DirichletCharacter
