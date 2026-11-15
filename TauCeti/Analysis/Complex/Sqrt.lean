/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The principal square root and the slit plane

The principal square root has nonnegative real part, and its real part is strictly positive
exactly on the slit plane. These facts control the branches in algebraic transformations
involving sums of principal roots. The file also records the values `√i = e^{π i / 4}` and
`√(-i τ) = (√i)⁻¹ √τ` for `τ` in the open upper half-plane.
-/

public section

open scoped Real

namespace Complex

/-- The square of the principal square root is the original complex number. -/
@[simp]
theorem sq_sqrt (z : ℂ) : sqrt z ^ 2 = z :=
  cpow_ofNat_inv_pow z 2

/-- The principal square root vanishes only at zero. -/
@[simp]
theorem sqrt_eq_zero_iff {z : ℂ} : sqrt z = 0 ↔ z = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ sqrt_zero⟩
  rw [← sq_sqrt z, h, zero_pow two_ne_zero]

/-- The principal square root of `i` is `e^{π i / 4}`. -/
theorem sqrt_I_eq_exp : sqrt I = exp (π * I / 4) := by
  rw [sqrt_eq_exp I_ne_zero, log_I]
  congr 1
  ring

/-- In the open upper half-plane, the principal root of `-i τ` is `(√i)⁻¹ √τ`: both have
argument `(arg τ - π / 2) / 2`. -/
theorem sqrt_neg_I_mul {τ : ℂ} (hτ : 0 < τ.im) : sqrt (-I * τ) = (sqrt I)⁻¹ * sqrt τ := by
  have hτ₀ : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have hlog : log (-I * τ) = log (-I) + log τ := by
    refine (log_mul_eq_add_log_iff (neg_ne_zero.2 I_ne_zero) hτ₀).2 ?_
    rw [arg_neg_I]
    have h₀ : 0 ≤ arg τ := arg_nonneg_iff.2 hτ.le
    constructor <;> linarith [arg_le_pi τ, Real.pi_pos]
  rw [sqrt_eq_exp (mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ₀), sqrt_eq_exp I_ne_zero,
    sqrt_eq_exp hτ₀, hlog, log_neg_I, log_I, ← exp_neg, ← exp_add]
  congr 1
  ring

/-- The principal square root has nonnegative real part. -/
@[simp]
theorem sqrt_re_nonneg (z : ℂ) : 0 ≤ (sqrt z).re := by
  rw [sqrt, cpow_inv_two_re]
  positivity

/-- The principal square root has nonnegative imaginary part when the input does. -/
theorem sqrt_im_nonneg {z : ℂ} (h : 0 ≤ z.im) : 0 ≤ (sqrt z).im := by
  rw [sqrt, cpow_inv_two_im_eq_sqrt h]
  exact Real.sqrt_nonneg _

/-- The principal square root has positive real part exactly on the slit plane. -/
@[simp]
theorem sqrt_re_pos_iff (z : ℂ) : 0 < (sqrt z).re ↔ z ∈ slitPlane := by
  rw [sqrt, cpow_inv_two_re, Real.sqrt_pos, div_pos_iff_of_pos_right (by norm_num),
    mem_slitPlane_iff_not_le_zero, ← neg_re_eq_norm]
  have h := (neg_le_abs z.re).trans (abs_re_le_norm z)
  constructor
  · intro hz heq
    linarith
  · intro hz
    have hlt := lt_of_le_of_ne h hz
    linarith

/-- A sum of principal square roots has positive real part exactly when at least one
input lies in the slit plane. -/
@[simp]
theorem sqrt_add_sqrt_re_pos_iff (x y : ℂ) :
    0 < (sqrt x).re + (sqrt y).re ↔ x ∈ slitPlane ∨ y ∈ slitPlane := by
  rw [← sqrt_re_pos_iff x, ← sqrt_re_pos_iff y]
  have hx := sqrt_re_nonneg x
  have hy := sqrt_re_nonneg y
  constructor
  · intro h
    by_contra! hn
    linarith
  · rintro (h | h) <;> linarith

end Complex
