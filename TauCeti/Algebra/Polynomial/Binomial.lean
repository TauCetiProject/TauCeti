/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Coefficients of powers of linear polynomials

The binomial coefficient formula for `(a + b X)^n` allows coefficient calculations without
expanding a polynomial into a finite sum at each use.
-/

public section

namespace TauCeti

open Polynomial Finset

/-- The coefficient of `X^k` in `(a + b X)^n`, including coefficients above the degree. -/
theorem coeff_C_add_C_mul_X_pow {R : Type*} [CommSemiring R] (a b : R) (n k : ℕ) :
    ((C a + C b * X) ^ n).coeff k = (n.choose k : R) * a ^ (n - k) * b ^ k := by
  rw [add_comm, add_pow, finsetSum_coeff]
  simp only [mul_pow, ← C_pow, coeff_mul_natCast, coeff_mul_C, coeff_C_mul, coeff_X_pow]
  rw [sum_eq_single k]
  · simp [mul_comm, mul_assoc]
  · intro i hi hik
    simp [Ne.symm hik]
  · intro hk
    have hnk : n < k := by simpa using hk
    simp [Nat.choose_eq_zero_of_lt hnk]

end TauCeti
