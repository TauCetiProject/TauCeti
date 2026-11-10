/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.MulChar.Basic

/-!
# Quadratic Dirichlet characters under level changes and products

Being quadratic is preserved by lifting a Dirichlet character to a multiple of its level, and
reflected by it when the target level is nonzero. Together with the fact that a product of
quadratic multiplicative characters is quadratic (`MulChar.IsQuadratic.mul`, in
`TauCeti.NumberTheory.MulChar.Basic`), this shows that the product `χ.mul ψ` of characters of
different levels, taken at their common level, is quadratic.

## Main results

* `MulChar.IsQuadratic.changeLevel`: lifting a quadratic Dirichlet character to a multiple of its
  level leaves it quadratic.
* `DirichletCharacter.isQuadratic_changeLevel_iff`: at a nonzero target level, a lifted
  character is quadratic exactly when the original character is quadratic.
* `DirichletCharacter.isQuadratic_mul`: the common-level product of two quadratic characters is
  quadratic.
-/

public section

/-- Lifting a quadratic Dirichlet character to a multiple of its level leaves it quadratic. -/
theorem MulChar.IsQuadratic.changeLevel {R : Type*} [CommRing R]
    {n m : ℕ} {χ : DirichletCharacter R n} (hχ : χ.IsQuadratic) (h : n ∣ m) :
    (DirichletCharacter.changeLevel h χ).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · rw [← ha.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd]
    exact hχ _
  · exact Or.inl (MulChar.map_nonunit _ ha)

namespace DirichletCharacter

/-- Lifting to a nonzero multiple of the level preserves and reflects being quadratic. -/
@[simp]
theorem isQuadratic_changeLevel_iff {R : Type*} [CommRing R]
    {n m : ℕ} [NeZero m] {χ : DirichletCharacter R n} (h : n ∣ m) :
    (changeLevel h χ).IsQuadratic ↔ χ.IsQuadratic := by
  refine ⟨?_, fun hχ ↦ hχ.changeLevel h⟩
  intro hχ a
  by_cases ha : IsUnit a
  · obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective h ha.unit
    have hv := hχ (u : ZMod m)
    rw [changeLevel_eq_cast_of_dvd] at hv
    rw [← ha.unit_spec, ← hu, ZMod.unitsMap_val]
    exact hv
  · exact Or.inl (MulChar.map_nonunit χ ha)

/-- The product of two quadratic characters, taken at the least common multiple of their levels,
is quadratic. -/
theorem isQuadratic_mul {R : Type*} [CommRing R] {n m : ℕ} {χ : DirichletCharacter R n}
    {ψ : DirichletCharacter R m} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) :
    (χ.mul ψ).IsQuadratic := by
  rw [DirichletCharacter.mul]
  exact (hχ.changeLevel _).mul (hψ.changeLevel _)

end DirichletCharacter
