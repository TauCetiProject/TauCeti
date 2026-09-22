/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Quadratic characters under products and level changes

A multiplicative character into an integral domain is quadratic exactly when its square is the
trivial character (`MulChar.isQuadratic_iff_sq_eq_one`). Being quadratic is therefore preserved
by the two operations that assemble one Dirichlet character out of several: multiplying finitely
many characters, and lifting a character to a multiple of its level.

## Main results

* `MulChar.isQuadratic_prod`: a finite product of quadratic characters is quadratic.
* `DirichletCharacter.isQuadratic_changeLevel`: lifting a quadratic character to a multiple of
  its level leaves it quadratic.
-/

public section

namespace MulChar

/-- A finite product of quadratic characters is quadratic. -/
theorem isQuadratic_prod {M R ι : Type*} [CommMonoid M] [CommRing R] [NoZeroDivisors R]
    [Nontrivial R] {s : Finset ι} {χ : ι → MulChar M R} (hχ : ∀ i ∈ s, (χ i).IsQuadratic) :
    (∏ i ∈ s, χ i).IsQuadratic := by
  rw [isQuadratic_iff_sq_eq_one, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i hi ↦ (hχ i hi).sq_eq_one

end MulChar

namespace DirichletCharacter

/-- Lifting a quadratic character to a multiple of its level leaves it quadratic. -/
theorem isQuadratic_changeLevel {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    {n m : ℕ} {χ : DirichletCharacter R n} (hχ : χ.IsQuadratic) (h : n ∣ m) :
    (changeLevel h χ).IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one, ← map_pow, hχ.sq_eq_one, map_one]

end DirichletCharacter
