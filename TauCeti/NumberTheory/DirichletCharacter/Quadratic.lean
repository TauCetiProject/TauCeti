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

/-- A finite product of quadratic characters is quadratic. -/
theorem isQuadratic_prod {M R ι : Type*} [CommMonoid M] [CommRing R]
    {s : Finset ι} {χ : ι → MulChar M R} (hχ : ∀ i ∈ s, (χ i).IsQuadratic) :
    (∏ i ∈ s, χ i).IsQuadratic := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro a
    by_cases ha : IsUnit a
    · exact Or.inr (Or.inl (MulChar.one_apply ha))
    · exact Or.inl (MulChar.map_nonunit 1 ha)
  | @insert i s hi ih =>
    intro a
    rw [Finset.prod_insert hi, MulChar.mul_apply]
    have hs := ih (fun j hj ↦ hχ j (Finset.mem_insert_of_mem hj)) a
    rcases hχ i (Finset.mem_insert_self i s) a with hi0 | hi1 | hi2
    · exact Or.inl (by simp [hi0])
    · simpa [hi1] using hs
    · rcases hs with hs0 | hs1 | hs2
      · exact Or.inl (by simp [hi2, hs0])
      · exact Or.inr (Or.inr (by simp [hi2, hs1]))
      · exact Or.inr (Or.inl (by simp [hi2, hs2]))

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
