/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The principal square root and the slit plane

The principal square root has nonnegative real part, and its real part is strictly positive
exactly on the slit plane. These facts control the branches in algebraic transformations
involving sums of principal roots. The file also records the values `√i = e^{π i / 4}`,
`√(-i τ) = (√i)⁻¹ √τ` for `τ` in the open upper half-plane, and `√(-w) = i √w` for `w` in the
open lower half-plane, the splitting `√(r z) = √r √z`
for real `r ≥ 0` and the identification of the real square root of `x ≥ 0` with the complex
half-power `x ^ (1 / 2)`, records that the real square root of a nonnegative real, cast to `ℂ`,
squares back to it, and packages the principal square root of a nonzero complex number as a unit,
`Complex.sqrtUnit`. A complex unit of absolute value one has a square root of absolute value one,
`Complex.exists_sq_eq_and_star_mul_self_eq_one`.

The real square root of a positive real, cast to `ℂ`, is nonzero, and that of a nonnegative
real `x` squares to `x` (`Complex.sq_ofReal_sqrt`), so its inverse squares to `x⁻¹`
(`Complex.inv_ofReal_sqrt_mul_self`). Together with `1 + i ≠ 0` (`Complex.one_add_I_ne_zero`),
these at `x = 2` are the arithmetic facts behind `e^{π i / 4} = (1 + i) / √2`. It also follows
that `i√x` squares to `-x` (`Complex.I_mul_ofReal_sqrt_sq`).
-/

public section

open scoped Real

namespace Complex

/-- The real square root of a nonnegative real, cast to `ℂ`, squares back to it:
`(√x : ℂ) * √x = x`. -/
@[simp]
theorem mul_self_ofReal_sqrt {x : ℝ} (hx : 0 ≤ x) : (√x : ℂ) * √x = x := by
  exact_mod_cast Real.mul_self_sqrt hx

/-- The square of the principal square root is the original complex number. -/
@[simp]
theorem sq_sqrt (z : ℂ) : sqrt z ^ 2 = z :=
  cpow_ofNat_inv_pow z 2

/-- The principal square root vanishes only at zero. -/
@[simp]
theorem sqrt_eq_zero_iff {z : ℂ} : sqrt z = 0 ↔ z = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ sqrt_zero⟩
  rw [← sq_sqrt z, h, zero_pow two_ne_zero]

/-- The real square root of a nonnegative real number is its principal complex half-power. -/
theorem ofReal_sqrt_eq_cpow {x : ℝ} (hx : 0 ≤ x) : (√x : ℂ) = (x : ℂ) ^ (1 / 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow hx]
  norm_num

/-- The principal square root splits across a nonnegative real factor: `√(r z) = √r √z`. -/
theorem sqrt_ofReal_mul {r : ℝ} (hr : 0 ≤ r) (z : ℂ) : sqrt (r * z) = sqrt r * sqrt z :=
  TauCeti.ofReal_mul_cpow hr z 2⁻¹

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

/-- In the open lower half-plane (`w.im < 0`), `√(-w) = i √w`. -/
theorem sqrt_neg_of_im_neg {w : ℂ} (hw : w.im < 0) : sqrt (-w) = I * sqrt w := by
  have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw
  have hlog : log (-w) = log w + π * I := by
    apply Complex.ext
    · simp [log_re]
    · simp [log_im, arg_neg_eq_arg_add_pi_of_im_neg hw]
  have hpi : (π : ℂ) * I / 2 = π / 2 * I := by ring
  rw [_root_.sqrt_eq_exp (neg_ne_zero.mpr hw0), _root_.sqrt_eq_exp hw0, hlog, add_div, exp_add,
    hpi, exp_pi_div_two_mul_I, mul_comm _ I]

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

/-- The principal half-power `z ^ (1 / 2)` has positive real part exactly on the slit plane. -/
theorem cpow_one_half_re_pos_iff (z : ℂ) : 0 < (z ^ (1 / 2 : ℂ)).re ↔ z ∈ slitPlane := by
  simpa only [sqrt, one_div] using sqrt_re_pos_iff z

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

/-- The principal square root of a nonzero complex number, as a unit. -/
noncomputable def sqrtUnit {z : ℂ} (hz : z ≠ 0) : ℂˣ :=
  Units.mk0 (sqrt z) (sqrt_eq_zero_iff.not.2 hz)

/-- The value of `Complex.sqrtUnit` is the principal square root. -/
@[simp]
theorem val_sqrtUnit {z : ℂ} (hz : z ≠ 0) : (sqrtUnit hz : ℂ) = sqrt z :=
  Units.val_mk0 _

/-- The unit principal square root of `z` squares to `z`. -/
theorem sqrtUnit_mul_self {z : ℂ} (hz : z ≠ 0) : (sqrtUnit hz : ℂ) * sqrtUnit hz = z := by
  rw [← _root_.sq, val_sqrtUnit, sq_sqrt]

/-- A complex unit of absolute value one is `s ^ 2` for a unit `s` of absolute value one, that is,
with `conj s * s = 1`. -/
theorem exists_sq_eq_and_star_mul_self_eq_one {z : ℂˣ} (hz : normSq z = 1) :
    ∃ s : ℂˣ, s ^ 2 = z ∧ star s * s = 1 := by
  refine ⟨sqrtUnit z.ne_zero, Units.ext (by simp), Units.ext ?_⟩
  simp only [Units.val_mul, Units.coe_star, val_sqrtUnit, Units.val_one, star_def]
  rw [← normSq_eq_conj_mul_self, ofReal_eq_one,
    ← pow_eq_one_iff_of_nonneg (normSq_nonneg _) two_ne_zero, ← map_pow, sq_sqrt, hz]

/-- The real square root of a positive real, cast to `ℂ`, is nonzero. -/
theorem ofReal_sqrt_ne_zero {x : ℝ} (hx : 0 < x) : (√x : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr hx).ne'

/-- The real square root of a nonnegative real, cast to `ℂ`, squares back to it:
`(√x : ℂ) ^ 2 = x`. -/
theorem sq_ofReal_sqrt {x : ℝ} (hx : 0 ≤ x) : (√x : ℂ) ^ 2 = x := by
  exact_mod_cast Real.sq_sqrt hx

/-- The inverse of the real square root of a nonnegative real `x`, cast to `ℂ`, times itself is
`x⁻¹`. -/
theorem inv_ofReal_sqrt_mul_self {x : ℝ} (hx : 0 ≤ x) : (√x : ℂ)⁻¹ * (√x : ℂ)⁻¹ = (x : ℂ)⁻¹ := by
  rw [← mul_inv, mul_self_ofReal_sqrt hx]

/-- For a nonnegative real `x`, `i√x` is a square root of `-x`: `(i√x) ^ 2 = -x`. -/
theorem I_mul_ofReal_sqrt_sq {x : ℝ} (hx : 0 ≤ x) : (I * √x) ^ 2 = -x := by
  rw [mul_pow, I_sq, sq_ofReal_sqrt hx]
  ring

/-- The complex number `1 + i` is nonzero. -/
theorem one_add_I_ne_zero : 1 + I ≠ 0 := fun h ↦ by
  simpa using congrArg re h

end Complex
