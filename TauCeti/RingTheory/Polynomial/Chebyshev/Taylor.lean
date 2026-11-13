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
import TauCeti.Algebra.Polynomial.Derivative

/-!
# Rescaled Chebyshev polynomials near `X = 2`

The rescaled Chebyshev polynomials satisfy `Cₙ(u + u⁻¹) = uⁿ + u⁻ⁿ` and
`(u - u⁻¹) Sₙ(u + u⁻¹) = uⁿ⁺¹ - u⁻ⁿ⁻¹`, so `X = 2` corresponds to `u = 1`. This file records
their leading Taylor coefficients at `2` and the resulting expansions in powers of `X - 2`. They
follow from the Taylor coefficients of `Tₙ` and `Uₙ` at `1`, since `Cₙ(2X) = 2Tₙ(X)` and
`Sₙ(2X) = Uₙ(X)`.

The coefficients are computed over an arbitrary commutative ring, in a form that avoids
division. The closed forms with denominators `12` and `6`, and the expansions, are stated over a
field of characteristic other than `2` and `3`.

## Main results

* `Polynomial.Chebyshev.exists_C_sub_two_eq`:
  `Cₙ - 2 = n² (X - 2) + n² (n² - 1) / 12 · (X - 2)² + O((X - 2)³)`.
* `Polynomial.Chebyshev.exists_S_eq`:
  `Sₙ = (n + 1) + (n + 2) (n + 1) n / 6 · (X - 2) + O((X - 2)²)`.
-/

public section

namespace Polynomial.Chebyshev

variable {R : Type*}

section CommRing

variable [CommRing R]

/-- The Taylor coefficients of `Cₙ` at `2` are the images of those over `ℤ`. The factor `2` in
`Cₙ(2X) = 2Tₙ(X)` cannot be cancelled in a general ring, so the coefficients of `Cₙ` are computed
over `ℤ`. -/
private theorem taylor_two_C_coeff_eq_intCast (n : ℤ) (k : ℕ) :
    (taylor 2 (C R n)).coeff k = ((taylor 2 (C ℤ n)).coeff k : ℤ) := by
  rw [← eq_intCast (Int.castRingHom R), ← coeff_map, map_taylor, map_C, map_ofNat]

/-- Differentiating `Cₙ(2X) = 2Tₙ(X)` `k` times at `X = 1` gives `2ᵏ Cₙ⁽ᵏ⁾(2) = 2 Tₙ⁽ᵏ⁾(1)`. -/
private theorem two_pow_mul_iterate_derivative_C_eval_two (n : ℤ) (k : ℕ) :
    2 ^ k * (derivative^[k] (C R n)).eval 2 = 2 * (derivative^[k] (T R n)).eval 1 := by
  -- The chain rule at `X = 1`, with the constant `Polynomial.C 2` written as the polynomial `2`.
  have h := eval_iterate_derivative_comp_C_mul_X (C R n) 2 1 k
  rw [map_ofNat Polynomial.C 2, mul_one, C_comp_two_mul_X] at h
  -- Write the factor `2` of `2Tₙ` as `Polynomial.C 2` to pull it out of the derivative.
  rw [← h, ← map_ofNat Polynomial.C 2, iterate_derivative_C_mul, eval_C_mul]

/-- Differentiating `Sₙ(2X) = Uₙ(X)` `k` times at `X = 1` gives `2ᵏ Sₙ⁽ᵏ⁾(2) = Uₙ⁽ᵏ⁾(1)`. -/
private theorem two_pow_mul_iterate_derivative_S_eval_two (n : ℤ) (k : ℕ) :
    2 ^ k * (derivative^[k] (S R n)).eval 2 = (derivative^[k] (U R n)).eval 1 := by
  -- The chain rule at `X = 1`, with the constant `Polynomial.C 2` written as the polynomial `2`.
  have h := eval_iterate_derivative_comp_C_mul_X (S R n) 2 1 k
  rw [map_ofNat Polynomial.C 2, mul_one, S_comp_two_mul_X] at h
  exact h.symm

/-- The linear Taylor coefficient of `Cₙ` at `2`. -/
theorem taylor_two_C_coeff_one (n : ℤ) : (taylor 2 (C R n)).coeff 1 = (n : R) ^ 2 := by
  have h : (taylor 2 (C ℤ n)).coeff 1 = n ^ 2 := by
    have h₁ := two_pow_mul_iterate_derivative_C_eval_two (R := ℤ) n 1
    rw [Function.iterate_one, derivative_T_eval_one, Int.cast_id] at h₁
    rw [taylor_coeff_one]
    linarith
  rw [taylor_two_C_coeff_eq_intCast, h, Int.cast_pow]

/-- Twelve times the quadratic Taylor coefficient of `Cₙ` at `2`. -/
theorem twelve_mul_taylor_two_C_coeff_two (n : ℤ) :
    12 * (taylor 2 (C R n)).coeff 2 = (n : R) ^ 2 * ((n : R) ^ 2 - 1) := by
  have h : 12 * (taylor 2 (C ℤ n)).coeff 2 = n ^ 2 * (n ^ 2 - 1) := by
    have h₂ := two_pow_mul_iterate_derivative_C_eval_two (R := ℤ) n 2
    have hT := iterate_derivative_T_eval_one (R := ℤ) n 2
    have hH := congrArg (fun f ↦ (f (C ℤ n)).eval 2) (factorial_smul_hasseDeriv (R := ℤ) 2)
    -- Unfold `derivative^[2]` and evaluate the numerals `2 ^ 2`, `2!` and the products.
    simp [Finset.prod_range_succ] at h₂ hT hH
    rw [taylor_coeff]
    linarith
  rw [taylor_two_C_coeff_eq_intCast]
  exact_mod_cast congrArg (Int.cast : ℤ → R) h

/-- Six times the linear Taylor coefficient of `Sₙ` at `2`. -/
theorem six_mul_taylor_two_S_coeff_one (n : ℤ) :
    6 * (taylor 2 (S R n)).coeff 1 = ((n : R) + 2) * ((n : R) + 1) * n := by
  have h₁ := two_pow_mul_iterate_derivative_S_eval_two (R := R) n 1
  rw [Function.iterate_one] at h₁
  rw [taylor_coeff_one]
  linear_combination 3 * h₁ + derivative_U_eval_one (R := R) n

end CommRing

section Field

variable [Field R] [NeZero (2 : R)] [NeZero (3 : R)]

/-- The quadratic Taylor coefficient of `Cₙ` at `2`. -/
theorem taylor_two_C_coeff_two (n : ℤ) :
    (taylor 2 (C R n)).coeff 2 = (n : R) ^ 2 * ((n : R) ^ 2 - 1) / 12 := by
  have h : (12 : R) ≠ 0 := by
    rw [show (12 : R) = 2 * 2 * 3 by norm_num]
    exact mul_ne_zero (mul_ne_zero two_ne_zero two_ne_zero) three_ne_zero
  exact eq_div_of_mul_eq h ((mul_comm ..).trans (twelve_mul_taylor_two_C_coeff_two n))

/-- The linear Taylor coefficient of `Sₙ` at `2`. -/
theorem taylor_two_S_coeff_one (n : ℤ) :
    (taylor 2 (S R n)).coeff 1 = ((n : R) + 2) * ((n : R) + 1) * n / 6 := by
  have h : (6 : R) ≠ 0 := by
    rw [show (6 : R) = 2 * 3 by norm_num]
    exact mul_ne_zero two_ne_zero three_ne_zero
  exact eq_div_of_mul_eq h ((mul_comm ..).trans (six_mul_taylor_two_S_coeff_one n))

/-- The expansion `Cₙ - 2 = n² w + n² (n² - 1) / 12 · w² + O(w³)` in `w = X - 2`. -/
theorem exists_C_sub_two_eq (n : ℤ) : ∃ r : R[X],
    C R n - Polynomial.C 2 =
      Polynomial.C ((n : R) ^ 2) * (X - Polynomial.C 2) +
        Polynomial.C ((n : R) ^ 2 * ((n : R) ^ 2 - 1) / 12) * (X - Polynomial.C 2) ^ 2 +
          (X - Polynomial.C 2) ^ 3 * r := by
  have h₀ : (taylor 2 (C R n)).coeff 0 = 2 := by rw [taylor_coeff_zero, C_eval_two]
  have h₁ := taylor_two_C_coeff_one (R := R) n
  have h₂ := taylor_two_C_coeff_two (R := R) n
  obtain ⟨r, hr⟩ : (X - Polynomial.C 2) ^ 3 ∣ C R n - Polynomial.C 2 -
      Polynomial.C ((n : R) ^ 2) * (X - Polynomial.C 2) -
        Polynomial.C ((n : R) ^ 2 * ((n : R) ^ 2 - 1) / 12) * (X - Polynomial.C 2) ^ 2 := by
    rw [X_sub_C_pow_dvd_iff, ← taylor_apply, X_pow_dvd_iff]
    intro k hk
    simp only [map_sub, taylor_mul, taylor_pow, taylor_C, taylor_X, add_sub_cancel_right]
    interval_cases k <;>
      simp only [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, h₀, h₁, h₂] <;>
      norm_num
  exact ⟨r, by linear_combination hr⟩

/-- The expansion `Sₙ = (n + 1) + (n + 2) (n + 1) n / 6 · w + O(w²)` in `w = X - 2`. -/
theorem exists_S_eq (n : ℤ) : ∃ r : R[X],
    S R n = Polynomial.C ((n : R) + 1) +
      Polynomial.C (((n : R) + 2) * ((n : R) + 1) * n / 6) * (X - Polynomial.C 2) +
        (X - Polynomial.C 2) ^ 2 * r := by
  have h₀ : (taylor 2 (S R n)).coeff 0 = n + 1 := by rw [taylor_coeff_zero, S_eval_two]
  have h₁ := taylor_two_S_coeff_one (R := R) n
  obtain ⟨r, hr⟩ : (X - Polynomial.C 2) ^ 2 ∣ S R n - Polynomial.C ((n : R) + 1) -
      Polynomial.C (((n : R) + 2) * ((n : R) + 1) * n / 6) * (X - Polynomial.C 2) := by
    rw [X_sub_C_pow_dvd_iff, ← taylor_apply, X_pow_dvd_iff]
    intro k hk
    simp only [map_sub, taylor_mul, taylor_C, taylor_X, add_sub_cancel_right]
    interval_cases k <;>
      simp only [coeff_sub, coeff_C_mul, coeff_C, coeff_X, h₀, h₁] <;> norm_num
  exact ⟨r, by linear_combination hr⟩

end Field

end Polynomial.Chebyshev
