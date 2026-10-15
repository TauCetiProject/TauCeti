/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.IntervalCases

/-!
# Rescaled Chebyshev polynomials near `X = 2`

The rescaled Chebyshev polynomials satisfy `Cₙ(u + u⁻¹) = uⁿ + u⁻ⁿ` and
`(u - u⁻¹) Sₙ(u + u⁻¹) = uⁿ⁺¹ - u⁻ⁿ⁻¹`, so `X = 2` corresponds to `u = 1`. This file records
their leading Taylor coefficients at `2`, over a field of characteristic zero, and the resulting
expansions in powers of `X - 2`. They follow from the Taylor coefficients of `Tₙ` and `Uₙ` at `1`,
since `Cₙ(2X) = 2Tₙ(X)` and `Sₙ(2X) = Uₙ(X)`.

## Main results

* `Polynomial.Chebyshev.exists_C_sub_two_eq`:
  `Cₙ - 2 = n² (X - 2) + n² (n² - 1) / 12 · (X - 2)² + O((X - 2)³)`.
* `Polynomial.Chebyshev.exists_S_eq`:
  `Sₙ = (n + 1) + (n + 2) (n + 1) n / 6 · (X - 2) + O((X - 2)²)`.
-/

public section

namespace Polynomial.Chebyshev

variable {R : Type*}

variable [Field R] [CharZero R]

/-- The linear Taylor coefficient of `Cₙ` at `2`. -/
theorem taylor_two_C_coeff_one (n : ℤ) : (taylor 2 (C R n)).coeff 1 = (n : R) ^ 2 := by
  have h₁ := congrArg derivative (C_comp_two_mul_X R n)
  simp only [derivative_comp, derivative_mul, derivative_ofNat, derivative_X, zero_mul, zero_add,
    mul_one] at h₁
  have e₁ := congrArg (eval 1) h₁
  simp only [eval_mul, eval_comp, eval_ofNat, eval_X, mul_one, derivative_T_eval_one] at e₁
  rw [taylor_coeff_one]
  linear_combination e₁ / 2

/-- The quadratic Taylor coefficient of `Cₙ` at `2`. -/
theorem taylor_two_C_coeff_two (n : ℤ) :
    (taylor 2 (C R n)).coeff 2 = (n : R) ^ 2 * ((n : R) ^ 2 - 1) / 12 := by
  have h₁ := congrArg derivative (C_comp_two_mul_X R n)
  have h₂ := congrArg derivative h₁
  simp only [derivative_comp, derivative_mul, derivative_ofNat, derivative_X, zero_mul, zero_add,
    mul_one] at h₁ h₂
  have e₂ := congrArg (eval 1) h₂
  simp only [eval_mul, eval_comp, eval_ofNat, eval_X, mul_one] at e₂
  have hT := iterate_derivative_T_eval_one (R := R) n 2
  have hH := congrArg (fun f ↦ (f (C R n)).eval 2) (factorial_smul_hasseDeriv (R := R) 2)
  simp [Finset.prod_range_succ] at hT hH
  rw [taylor_coeff]
  linear_combination hH / 2 + e₂ / 8 + hT / 12

/-- The linear Taylor coefficient of `Sₙ` at `2`. -/
theorem taylor_two_S_coeff_one (n : ℤ) :
    (taylor 2 (S R n)).coeff 1 = ((n : R) + 2) * ((n : R) + 1) * n / 6 := by
  have h₁ := congrArg derivative (S_comp_two_mul_X R n)
  simp only [derivative_comp, derivative_mul, derivative_ofNat, derivative_X, zero_mul, zero_add,
    mul_one] at h₁
  have e₁ := congrArg (eval 1) h₁
  simp only [eval_mul, eval_comp, eval_ofNat, eval_X, mul_one] at e₁
  have hU := derivative_U_eval_one (R := R) n
  rw [taylor_coeff_one]
  linear_combination e₁ / 2 + hU / 6

/-- The expansion `Cₙ - 2 = n² w + n² (n² - 1) / 12 · w² + O(w³)` in `w = X - 2`. -/
theorem exists_C_sub_two_eq (n : ℤ) : ∃ r : R[X],
    C R n - Polynomial.C 2 =
      Polynomial.C ((n : R) ^ 2) * (X - Polynomial.C 2) +
        Polynomial.C ((n : R) ^ 2 * ((n : R) ^ 2 - 1) / 12) * (X - Polynomial.C 2) ^ 2 +
          (X - Polynomial.C 2) ^ 3 * r := by
  have h₀ : (taylor 2 (C R n)).coeff 0 = 2 := by rw [taylor_coeff_zero, C_eval_two]
  have h₁ := taylor_two_C_coeff_one (R := R) n
  have h₂ := taylor_two_C_coeff_two (R := R) n
  obtain ⟨r, hr⟩ : X ^ 3 ∣ taylor 2 (C R n) - Polynomial.C 2 - Polynomial.C ((n : R) ^ 2) * X -
      Polynomial.C ((n : R) ^ 2 * ((n : R) ^ 2 - 1) / 12) * X ^ 2 := by
    rw [X_pow_dvd_iff]
    intro k hk
    interval_cases k <;>
      simp only [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, h₀, h₁, h₂] <;> norm_num
  refine ⟨taylor (-2) r, taylor_injective (2 : R) ?_⟩
  simp only [map_sub, map_add, taylor_mul, taylor_pow, taylor_C, taylor_X, taylor_taylor,
    add_neg_cancel, taylor_zero, add_sub_cancel_right]
  linear_combination hr

/-- The expansion `Sₙ = (n + 1) + (n + 2) (n + 1) n / 6 · w + O(w²)` in `w = X - 2`. -/
theorem exists_S_eq (n : ℤ) : ∃ r : R[X],
    S R n = Polynomial.C ((n : R) + 1) +
      Polynomial.C (((n : R) + 2) * ((n : R) + 1) * n / 6) * (X - Polynomial.C 2) +
        (X - Polynomial.C 2) ^ 2 * r := by
  have h₀ : (taylor 2 (S R n)).coeff 0 = n + 1 := by rw [taylor_coeff_zero, S_eval_two]
  have h₁ := taylor_two_S_coeff_one (R := R) n
  obtain ⟨r, hr⟩ : X ^ 2 ∣ taylor 2 (S R n) - Polynomial.C ((n : R) + 1) -
      Polynomial.C (((n : R) + 2) * ((n : R) + 1) * n / 6) * X := by
    rw [X_pow_dvd_iff]
    intro k hk
    interval_cases k <;>
      simp only [coeff_sub, coeff_C_mul, coeff_C, coeff_X, h₀, h₁] <;> norm_num
  refine ⟨taylor (-2) r, taylor_injective (2 : R) ?_⟩
  simp only [map_sub, map_add, taylor_mul, taylor_pow, taylor_C, taylor_X, taylor_taylor,
    add_neg_cancel, taylor_zero, add_sub_cancel_right]
  linear_combination hr + map_add Polynomial.C (n : R) 1

end Polynomial.Chebyshev
