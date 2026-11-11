/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The periods of `exp (π i ·)` and `exp (2 π i ·)`, and branches of the logarithm

Mathlib characterises equality of complex exponentials by `Complex.exp_eq_exp_iff_exists_int`:
`exp x = exp y` if and only if `x - y ∈ 2 π i ℤ`. This file records the forms of the sufficient
condition used for the factors `exp (π i x)` of theta series and modular forms, where the
period is `2` in the variable `x`, and for the additive character `e(x) = exp (2 π i x)`, where
the period is `1`.

Two logarithms of the same number differ by `2 π i k` for an integer `k`, so dividing them by
`2 π i` and using them as coefficients of a vector `v` changes the result by `k • v`. Near
`z₀ ^ m`, the expression `log z₀ + (1 / m) log (t / z₀ ^ m)` is a logarithm of an `m`-th root of
`t`; it is continuous in `t` near `z₀ ^ m`, unlike the principal root.

## Main declarations

* `Complex.exp_pi_mul_I_mul_eq_of_sub_eq`: `exp (π i a) = exp (π i b)` whenever `a - b` is an
  even integer.
* `Complex.exp_two_pi_mul_I_mul_add_intCast`: `exp (2 π i (z + k)) = exp (2 π i z)` for an
  integer `k`.
* `Complex.norm_exp_two_pi_mul_I_mul_ofReal`: `‖exp (2 π i x)‖ = 1` for real `x`.
* `Complex.exists_div_two_pi_I_smul_eq_add_zsmul`: if `exp a = exp b`, then
  `(a / 2πi) • v = (b / 2πi) • v + k • v` for an integer `k`.
* `Complex.exp_log_add_inv_mul_log_div_pow`: `exp (log z₀ + (1 / m) log (t / z₀ ^ m))` is an
  `m`-th root of every `t ≠ 0`.
-/

public section

open Real

namespace Complex

/-- `exp (π i a) = exp (π i b)` whenever `a - b` is an even integer. -/
theorem exp_pi_mul_I_mul_eq_of_sub_eq {a b : ℂ} {m : ℤ} (h : a - b = 2 * m) :
    cexp (π * I * a) = cexp (π * I * b) :=
  exp_eq_exp_iff_exists_int.mpr ⟨m, by linear_combination (π * I) * h⟩

/-- `e(z + k) = e(z)` for `e(z) = exp (2 π i z)` and an integer `k`. -/
@[simp]
theorem exp_two_pi_mul_I_mul_add_intCast (z : ℂ) (k : ℤ) :
    cexp (2 * π * I * (z + k)) = cexp (2 * π * I * z) := by
  rw [mul_add, exp_add, mul_comm (2 * π * I) (k : ℂ), exp_int_mul_two_pi_mul_I, mul_one]

/-- `‖e(x)‖ = 1` for `e(x) = exp (2 π i x)` and real `x`. -/
@[simp]
theorem norm_exp_two_pi_mul_I_mul_ofReal (x : ℝ) : ‖cexp (2 * π * I * x)‖ = 1 := by
  simp [norm_exp]

/-- Two logarithms of the same number, divided by `2πi`, differ by an integer; so the vectors
`(a / 2πi) • v` and `(b / 2πi) • v` differ by an integer multiple of `v`. -/
theorem exists_div_two_pi_I_smul_eq_add_zsmul {E : Type*} [AddCommGroup E] [Module ℂ E]
    {a b : ℂ} (h : exp a = exp b) (v : E) :
    ∃ k : ℤ, (a / (2 * π * I)) • v = (b / (2 * π * I)) • v + k • v := by
  obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.1 h
  refine ⟨k, ?_⟩
  have h2 : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
  rw [hk, ← Int.cast_smul_eq_zsmul ℂ, ← add_smul, add_div, mul_div_cancel_right₀ _ h2]

/-- A branch of the `m`-th root near `z₀ ^ m`: `exp (log z₀ + (1 / m) log (t / z₀ ^ m))` is an
`m`-th root of every `t ≠ 0`. -/
theorem exp_log_add_inv_mul_log_div_pow {m : ℕ} [NeZero m] {z₀ t : ℂ} (hz₀ : z₀ ≠ 0)
    (ht : t ≠ 0) : exp (log z₀ + (m : ℂ)⁻¹ * log (t / z₀ ^ m)) ^ m = t := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  rw [← exp_nat_mul, mul_add, ← mul_assoc, mul_inv_cancel₀ hm, one_mul, exp_add,
    exp_nat_mul, exp_log hz₀, exp_log (div_ne_zero ht (pow_ne_zero m hz₀)),
    mul_div_cancel₀ _ (pow_ne_zero m hz₀)]

end Complex
