/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Coefficients of shifted and monomial-factor products of polynomials

Multiplication by `X ^ l` shifts a polynomial's coefficients by `l`. When its degree is
bounded by `n`, the shifted coefficients vanish outside the window from `l` to `l + n`.
This identity identifies bounded coefficient rows with coefficients of shifted polynomials.

Over an ordered semiring, multiplying a polynomial whose coefficients are nonnegative by
`1 + C a * X ^ k` (`0 ≤ a`) adds a nonnegative shifted multiple of its coefficients, so no
coefficient decreases (`Polynomial.coeff_le_coeff_mul_one_add_C_mul_X_pow`).
-/

public section

namespace Polynomial

/-- The coefficients of `X ^ l * p` vanish outside the window from `l` to `l + n`
when `p.natDegree ≤ n`. -/
theorem coeff_X_pow_mul_of_natDegree_le {R : Type*} [Semiring R]
    {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) (l d : ℕ) :
    (X ^ l * p).coeff d = if l ≤ d ∧ d ≤ l + n then p.coeff (d - l) else 0 := by
  grind [coeff_X_pow_mul', coeff_eq_zero_of_natDegree_lt]

/-- Multiplying a polynomial with nonnegative coefficients by `1 + C a * X ^ k` (`0 ≤ a`) does not
decrease any coefficient. -/
theorem coeff_le_coeff_mul_one_add_C_mul_X_pow {R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] {p : R[X]} (hp : ∀ d, 0 ≤ p.coeff d) {a : R} (ha : 0 ≤ a) (k d : ℕ) :
    p.coeff d ≤ (p * (1 + C a * X ^ k)).coeff d := by
  rw [mul_add, mul_one, coeff_add]
  refine le_add_of_nonneg_right ?_
  rw [← mul_assoc]
  by_cases hd : k ≤ d
  · have hshift : (p * C a * X ^ k).coeff d = (p * C a).coeff (d - k) := by
      conv_lhs => rw [← Nat.sub_add_cancel hd]
      exact coeff_mul_X_pow (p * C a) k (d - k)
    rw [hshift, coeff_mul_C]
    exact mul_nonneg (hp (d - k)) ha
  · rw [coeff_mul_X_pow' (p * C a) k d, ite_eq_right hd]

end Polynomial
