/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Catalan
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.LinearCombination

/-!
# An integral square root of `1 + 4X`

The series `TauCeti.sqrtOneAddFour` has constant coefficient `1`, square `1 + 4X`, and
coefficient `2 * (-1)^n * catalan n` at `X^(n+1)`. In particular, the square root has
integer coefficients despite the denominators in the binomial expansion of `(1 + 4X)^(1/2)`.
This is the universal series used to construct integral square roots of polynomials that
are squares modulo `4`.

The construction uses Mathlib's `PowerSeries.catalanSeries` and its quadratic identity.
The integrality argument is that of V. Dimitrov, *A proof of the Schinzel–Zassenhaus
conjecture on polynomials*, arXiv:1912.12545v1, §2, equation (3).
-/

public section

open PowerSeries

namespace TauCeti

/-- The integral square root of `1 + 4X` with constant coefficient `1`, written using
Catalan numbers as `1 + 2X * C(-X)`. -/
noncomputable def sqrtOneAddFour : ℤ⟦X⟧ :=
  1 + 2 * X * rescale (-1) (catalanSeries.map (Nat.castRingHom ℤ))

/-- The constant coefficient fixes the choice of sign of the square root. -/
@[simp]
theorem constantCoeff_sqrtOneAddFour : constantCoeff sqrtOneAddFour = 1 := by
  simp [sqrtOneAddFour]

/-- The nonconstant coefficients of the integral square root are signed Catalan numbers. -/
@[simp]
theorem coeff_succ_sqrtOneAddFour (n : ℕ) :
    coeff (n + 1) sqrtOneAddFour = 2 * (-1 : ℤ) ^ n * catalan n := by
  rw [sqrtOneAddFour, map_add, coeff_one, ite_eq_right (Nat.succ_ne_zero n), zero_add,
    mul_assoc, mul_comm X, ← mul_assoc, coeff_succ_mul_X]
  simp [mul_assoc]

/-- The Catalan series gives a square root of `1 + 4X` over the integers. -/
@[simp]
theorem sqrtOneAddFour_sq : sqrtOneAddFour ^ 2 = 1 + 4 * X := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
    catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_one, map_X] at h
  have hneg := congrArg (rescale (-1 : ℤ)) h
  simp only [map_add, map_mul, map_pow, map_one, rescale_neg_one_X] at hneg
  rw [sqrtOneAddFour]
  linear_combination -4 * X * hneg

/-- The integral square root with constant coefficient `1` is unique. -/
theorem existsUnique_sq_eq_one_add_four_X :
    ∃! S : ℤ⟦X⟧, constantCoeff S = 1 ∧ S ^ 2 = 1 + 4 * X := by
  refine ⟨sqrtOneAddFour, ⟨constantCoeff_sqrtOneAddFour, sqrtOneAddFour_sq⟩, ?_⟩
  rintro S ⟨hS, hsq⟩
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hsq.trans sqrtOneAddFour_sq.symm) with h | h
  · exact h
  · have hc := congrArg constantCoeff h
    simp [hS] at hc

-- The first coefficients distinguish this series from the square root of `1 - 4X`.
example : coeff 1 sqrtOneAddFour = 2 := by
  simp

example : coeff 2 sqrtOneAddFour = -2 := by
  simp

example : coeff 3 sqrtOneAddFour = 4 := by
  simp [catalan_two]

example : coeff 4 sqrtOneAddFour = -10 := by
  simp [catalan_three]

end TauCeti
