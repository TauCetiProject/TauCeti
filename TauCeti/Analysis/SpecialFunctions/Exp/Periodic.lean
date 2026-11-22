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
the period is `1`. Conversely, if `exp (π x i)` is an integer for a real number `x`, then `x` is
an integer, and the parity of `x` is the sign of `exp (π x i)`.

Two logarithms of the same number differ by `2 π i k` for an integer `k`, so dividing them by
`2 π i` and using them as coefficients of a vector `v` changes the result by `k • v`. Near
`z₀ ^ m`, the expression `log z₀ + (1 / m) log (t / z₀ ^ m)` is a logarithm of an `m`-th root of
`t`; it is continuous in `t` near `z₀ ^ m`, unlike the principal root.

## Main declarations

* `Complex.exp_pi_mul_I_mul_eq_of_sub_eq`: `exp (π i a) = exp (π i b)` whenever `a - b` is an
  even integer.
* `Complex.exists_int_eq_of_exp_pi_mul_I_eq`: if `exp (π x i)` is an integer for real `x`, then
  `x` is an integer `k` and `exp (π x i) = (-1) ^ k`.
* `Complex.exp_add_int_mul_pi_mul_I`: `exp (z + k * (π * I)) = (-1) ^ k * exp z` for an
  integer `k`.
* `Complex.neg_one_zpow_mul_exp_add_int_mul_pi_mul_I`: `(-1) ^ k * exp (z + k * (π * I)) = exp z`
  for an integer `k`.
* `Complex.exp_two_pi_mul_I_mul_add_intCast`: `exp (2 π i (z + k)) = exp (2 π i z)` for an
  integer `k`.
* `Complex.norm_exp_two_pi_mul_I_mul_ofReal`: `‖exp (2 π i x)‖ = 1` for real `x`.
* `Complex.norm_exp_two_pi_mul_ofReal_mul_I`: the same with the factors ordered `2 π x i`.
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

/-- If `exp (π x i)` is an integer `u` for a real number `x`, then `x` is an integer `k` with
`(-1) ^ k = u`. -/
theorem exists_int_eq_of_exp_pi_mul_I_eq {x : ℝ} {u : ℤ} (h : cexp (↑(π * x) * I) = u) :
    ∃ k : ℤ, x = k ∧ (k.negOnePow : ℤ) = u := by
  have hsin : Real.sin (π * x) = 0 := by
    rw [← exp_ofReal_mul_I_im, h, intCast_im]
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hsin
  have hx : x = k := by
    have := Real.pi_pos.ne'
    field_simp at hk
    linarith
  refine ⟨k, hx, ?_⟩
  have h2 : cexp (↑(π * x) * I) = (k.negOnePow : ℤ) := by
    rw [hx, show (↑(π * (k : ℝ)) : ℂ) * I = k * (π * I) by push_cast; ring, exp_intCast_mul,
      exp_pi_mul_I, Int.cast_negOnePow ℂ k]
  exact_mod_cast h2.symm.trans h

/-- `exp (z + k * (π * I)) = (-1) ^ k * exp z` for an integer `k`. -/
theorem exp_add_int_mul_pi_mul_I (z : ℂ) (k : ℤ) :
    cexp (z + k * (π * I)) = (-1 : ℂ) ^ k * cexp z :=
  k.cast_negOnePow ℂ ▸ exp_antiperiodic.add_int_mul_eq k

/-- `(-1) ^ k * exp (z + k * (π * I)) = exp z` for an integer `k`. -/
@[simp]
theorem neg_one_zpow_mul_exp_add_int_mul_pi_mul_I (z : ℂ) (k : ℤ) :
    (-1 : ℂ) ^ k * cexp (z + k * (π * I)) = cexp z := by
  rw [exp_add_int_mul_pi_mul_I, ← mul_assoc, ← mul_zpow, neg_one_mul, neg_neg, one_zpow,
    one_mul]

/-- `e(z + k) = e(z)` for `e(z) = exp (2 π i z)` and an integer `k`. -/
@[simp]
theorem exp_two_pi_mul_I_mul_add_intCast (z : ℂ) (k : ℤ) :
    cexp (2 * π * I * (z + k)) = cexp (2 * π * I * z) := by
  rw [mul_add, exp_add, mul_comm (2 * π * I) (k : ℂ), exp_int_mul_two_pi_mul_I, mul_one]

/-- `‖e(x)‖ = 1` for `e(x) = exp (2 π i x)` and real `x`. -/
@[simp]
theorem norm_exp_two_pi_mul_I_mul_ofReal (x : ℝ) : ‖cexp (2 * π * I * x)‖ = 1 := by
  simp [norm_exp]

/-- `‖exp (2 π x i)‖ = 1` for real `x`: `norm_exp_two_pi_mul_I_mul_ofReal` with the factors in
the order of the holonomies `exp (2 π θ i)` of flat lines. -/
theorem norm_exp_two_pi_mul_ofReal_mul_I (x : ℝ) : ‖cexp (2 * π * x * I)‖ = 1 := by
  rw [mul_right_comm, norm_exp_two_pi_mul_I_mul_ofReal]

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
  rw [← exp_natCast_mul, mul_add, ← mul_assoc, mul_inv_cancel₀ hm, one_mul, exp_add,
    exp_natCast_mul, exp_log hz₀, exp_log (div_ne_zero ht (pow_ne_zero m hz₀)),
    mul_div_cancel₀ _ (pow_ne_zero m hz₀)]

end Complex
