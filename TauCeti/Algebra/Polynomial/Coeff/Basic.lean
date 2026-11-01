/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Coefficients of shifted polynomials with a degree bound

Multiplication by `X ^ l` shifts a polynomial's coefficients by `l`. When its degree is
bounded by `n`, the shifted coefficients vanish outside the window from `l` to `l + n`.
This identity identifies bounded coefficient rows with coefficients of shifted polynomials.

The polynomials `∑_{j < N} c_j X ^ (N - j)` have no constant term.
-/

public section

namespace TauCeti

open Polynomial

/-- The coefficients of `X ^ l * p` vanish outside the window from `l` to `l + n`
when `p.natDegree ≤ n`. -/
theorem _root_.Polynomial.coeff_X_pow_mul_of_natDegree_le {R : Type*} [Semiring R]
    {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) (l d : ℕ) :
    (X ^ l * p).coeff d = if l ≤ d ∧ d ≤ l + n then p.coeff (d - l) else 0 := by
  rw [coeff_X_pow_mul']
  by_cases h : l ≤ d
  · by_cases h' : d ≤ l + n
    · simp [h, h']
    · have hz : p.coeff (d - l) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [h, h', hz]
  · simp [h]

/-- The polynomial `∑_{j < N} c_j X ^ (N - j)` has no constant term. -/
theorem _root_.Polynomial.coeff_zero_sum_C_mul_X_pow_sub {R : Type*} [Semiring R] (N : ℕ)
    (c : ℕ → R) : (∑ j ∈ Finset.range N, C (c j) * X ^ (N - j)).coeff 0 = 0 := by
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  have := Finset.mem_range.1 hj
  rw [coeff_C_mul_X_pow, ite_eq_right_iff]
  omega

end TauCeti
