/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Coefficients of powers of linear polynomials

The binomial coefficient formula for `(a + b X)^n` allows coefficient calculations without
expanding a polynomial into a finite sum at each use. Substituting `a + b X` into a polynomial
therefore re-expands its coefficients by the same binomial scalars.
-/

public section

namespace TauCeti

open Polynomial

/-- The coefficient of `X^k` in `(a + b X)^n`, including coefficients above the degree. -/
@[simp]
theorem coeff_C_add_C_mul_X_pow {R : Type*} [CommSemiring R] (a b : R) (n k : ℕ) :
    ((C a + C b * X) ^ n).coeff k = (n.choose k : R) * a ^ (n - k) * b ^ k := by
  rw [add_comm, add_pow, finsetSum_coeff]
  simp only [mul_pow, ← C_pow, coeff_mul_natCast, coeff_mul_C, coeff_C_mul, coeff_X_pow]
  simp +contextual [mul_comm, mul_assoc, Nat.choose_eq_zero_of_lt]

end TauCeti

namespace Polynomial

/-- Substituting `a + b X` into a polynomial of degree below `N` re-expands its coefficients:
the coefficient of `X^j` is `∑_{k < N} P_k (k choose j) a^(k - j) b^j`. -/
theorem coeff_comp_C_add_C_mul_X {R : Type*} [CommSemiring R] (P : R[X]) {N : ℕ}
    (hP : P.natDegree < N) (a b : R) (j : ℕ) :
    (P.comp (C a + C b * X)).coeff j =
      ∑ k ∈ Finset.range N, P.coeff k * ((k.choose j : R) * a ^ (k - j) * b ^ j) := by
  conv_lhs => rw [P.as_sum_range' N hP]
  simp [sum_comp, TauCeti.coeff_C_add_C_mul_X_pow]

end Polynomial
