/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Quadratic characters under products and level changes

Being quadratic is preserved by the two operations that assemble one Dirichlet character out of
several: multiplying finitely many characters, and lifting a character to a multiple of its level.

## Main results

* `MulChar.isQuadratic_prod`: a finite product of quadratic characters is quadratic.
* `DirichletCharacter.isQuadratic_changeLevel`: lifting a quadratic character to a multiple of
  its level leaves it quadratic.
-/

public section

namespace MulChar

/-- The product of two quadratic characters is quadratic. -/
theorem IsQuadratic.mul {M R : Type*} [CommMonoid M] [CommRing R] {χ ψ : MulChar M R}
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) : (χ * ψ).IsQuadratic := by
  intro a
  rw [mul_apply]
  rcases hχ a with h | h | h <;> rcases hψ a with h' | h' | h' <;> simp [h, h']

/-- A finite product of quadratic characters is quadratic. -/
theorem isQuadratic_prod {M R ι : Type*} [CommMonoid M] [CommRing R]
    {s : Finset ι} {χ : ι → MulChar M R} (hχ : ∀ i ∈ s, (χ i).IsQuadratic) :
    (∏ i ∈ s, χ i).IsQuadratic := by
  refine Finset.prod_induction χ IsQuadratic (fun _ _ ↦ IsQuadratic.mul) (fun a ↦ ?_) hχ
  by_cases ha : IsUnit a
  · exact Or.inr (Or.inl (one_apply ha))
  · exact Or.inl (map_nonunit 1 ha)

end MulChar

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
