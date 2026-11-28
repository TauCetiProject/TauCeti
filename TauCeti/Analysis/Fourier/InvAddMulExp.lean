/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.Complex.PowerSeries.FourierCoeff
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Fourier coefficients of `1 / (b + c e^{iθ})`

For complex numbers `b`, `c` with `‖b‖ ≠ ‖c‖` and an integer `n`, this file computes

`∫₀^{2π} e^{inθ} / (b + c e^{iθ}) dθ`,

which is `2π` times the `(-n)`-th Fourier coefficient of `θ ↦ 1 / (b + c e^{iθ})`:

* if `‖c‖ < ‖b‖`, it is `2π (-c)^{-n} b^{n-1}` for `n ≤ 0` and `0` for `n ≥ 1`;
* if `‖b‖ < ‖c‖`, it is `0` for `n ≤ 0` and `2π (-b)^{n-1} c^{-n}` for `n ≥ 1`.

With `b = a` and `c = r > 0` these are the inner integrals of the kernel `G_w` of liquid type
weights in the dimer model: `(2π)⁻¹ ∫₀^{2π} e^{inθ} / (a + r e^{iθ}) dθ` is
`[|a| > r] (-r)^{-n} a^{n-1}` for `n ≤ 0` and `[|a| < r] (-a)^{n-1} r^{-n}` for `n ≥ 1`.

## Proof

For `‖c‖ < ‖b‖` the function `z ↦ 1 / (b + c z)` is holomorphic on the closed unit disc, so by
Cauchy's theorem `∫₀^{2π} e^{imθ} / (b + c e^{iθ}) dθ = 0` for `m ≥ 1`
(`DiffContOnCl.intervalIntegral_circleMap_zpow_smul_eq_zero`). For `n = -N ≤ 0` the integral is
`2π` times the `N`-th Fourier coefficient of `θ ↦ 1 / (b + c e^{iθ})`, which is the `N`-th Taylor
coefficient `b⁻¹ (-c / b)^N` of `z ↦ 1 / (b + c z)`, read off from the geometric series
`1 / (b + c z) = Σ_k b⁻¹ (-c z / b)^k` (`DiffContOnCl.fourierCoeffOn_circleMap_eq_of_hasSum`).
The case `‖b‖ < ‖c‖` follows from these two by the substitution `θ ↦ -θ`, which exchanges the
roles of `b` and `c` and of `n` and `1 - n`.

## Main results

* `TauCeti.integral_exp_div_add_of_norm_lt_of_nonpos`,
  `TauCeti.integral_exp_div_add_of_norm_lt_of_pos`,
  `TauCeti.integral_exp_div_add_of_lt_norm_of_nonpos`,
  `TauCeti.integral_exp_div_add_of_lt_norm_of_pos`: the four cases above.
* `TauCeti.integral_inv_add_mul_exp_neg`: `∫₀^{2π} 1 / (b + c e^{−iθ}) dθ = 2π / b` for
  `‖c‖ < ‖b‖`, by the substitution `θ ↦ 2π − θ` in the case `n = 0`.
-/

public section

open Complex Metric Set intervalIntegral
open scoped Real

namespace TauCeti

/-- For `‖c‖ < ‖b‖` the denominator `b + c z` does not vanish on the closed unit disc. -/
private theorem add_mul_ne_zero {b c z : ℂ} (hcb : ‖c‖ < ‖b‖) (hz : ‖z‖ ≤ 1) :
    b + c * z ≠ 0 := by
  intro h
  have hb : b = -(c * z) := eq_neg_of_add_eq_zero_left h
  have : ‖b‖ ≤ ‖c‖ := by
    rw [hb, norm_neg, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg c) hz
  exact this.not_gt hcb

/-- For `‖c‖ < ‖b‖` the function `z ↦ 1 / (b + c z)` is holomorphic on the closed unit disc. -/
private theorem diffContOnCl_inv_add {b c : ℂ} (hcb : ‖c‖ < ‖b‖) :
    DiffContOnCl ℂ (fun z => (b + c * z)⁻¹) (ball (0 : ℂ) 1) := by
  refine DifferentiableOn.diffContOnCl fun z hz => ?_
  rw [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall, dist_zero_right] at hz
  exact (((differentiableAt_const b).add ((differentiableAt_const c).mul
    differentiableAt_id)).inv (add_mul_ne_zero hcb hz)).differentiableWithinAt

/-- On the unit circle, `e^{inθ} / (b + c e^{iθ})` is `w ^ n * (b + c w)⁻¹` at `w = e^{iθ}`. -/
private theorem exp_div_add_eq (b c : ℂ) (n : ℤ) (θ : ℝ) :
    exp (n * θ * I) / (b + c * exp (θ * I)) =
      circleMap 0 1 θ ^ n * (b + c * circleMap 0 1 θ)⁻¹ := by
  rw [circleMap_zero, ofReal_one, one_mul, div_eq_mul_inv, mul_assoc, exp_intCast_mul]

/-- For `‖c‖ < ‖b‖` and `n ≥ 1`, `∫₀^{2π} e^{inθ} / (b + c e^{iθ}) dθ = 0`. -/
theorem integral_exp_div_add_of_norm_lt_of_pos {b c : ℂ} (hcb : ‖c‖ < ‖b‖) {n : ℤ}
    (hn : 0 < n) :
    ∫ θ in (0 : ℝ)..2 * π, exp (n * θ * I) / (b + c * exp (θ * I)) = 0 := by
  simp_rw [exp_div_add_eq]
  simpa using (diffContOnCl_inv_add hcb).intervalIntegral_circleMap_zpow_smul_eq_zero one_pos hn

/-- For `‖c‖ < ‖b‖` and `n ≤ 0`, `∫₀^{2π} e^{inθ} / (b + c e^{iθ}) dθ = 2π (-c)^{-n} b^{n-1}`. -/
theorem integral_exp_div_add_of_norm_lt_of_nonpos {b c : ℂ} (hcb : ‖c‖ < ‖b‖) {n : ℤ}
    (hn : n ≤ 0) :
    ∫ θ in (0 : ℝ)..2 * π, exp (n * θ * I) / (b + c * exp (θ * I)) =
      2 * π * (-c) ^ (-n) * b ^ (n - 1) := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = -N := ⟨(-n).toNat, by omega⟩
  have hb : b ≠ 0 := norm_pos_iff.1 ((norm_nonneg c).trans_lt hcb)
  -- The `N`-th Taylor coefficient of `z ↦ (b + c z)⁻¹ = Σ b⁻¹ (-c z / b)ᵏ` is `b⁻¹ (-c / b)ᴺ`.
  have hcoeff := (diffContOnCl_inv_add hcb).fourierCoeffOn_circleMap_eq_of_hasSum
    (a := fun k => b⁻¹ * (-c / b) ^ k) (fun z hz => ?_) N
  · simp_rw [exp_div_add_eq]
    rw [intervalIntegral_circleMap_zpow_mul (fun w => (b + c * w)⁻¹), neg_neg, hcoeff]
    have hpow : b ^ (-(N : ℤ) - 1) = (b ^ (N + 1))⁻¹ := by
      rw [← zpow_natCast, ← zpow_neg]
      push_cast
      ring_nf
    rw [zpow_natCast, hpow, div_pow, pow_succ]
    field_simp
  · have hq : ‖-c * z / b‖ < 1 := by
      rw [mem_ball_zero_iff] at hz
      rw [norm_div, div_lt_one (norm_pos_iff.2 hb), norm_mul, norm_neg]
      exact (mul_le_of_le_one_right (norm_nonneg c) hz.le).trans_lt hcb
    convert (hasSum_geometric_of_norm_lt_one hq).mul_left b⁻¹ using 1
    · ext k
      rw [smul_eq_mul, mul_div_assoc, mul_pow, div_pow, div_pow]
      ring
    · have h1q : 1 - -c * z / b = (b + c * z) / b := by field_simp; ring
      rw [h1q, inv_div, mul_div_assoc', inv_mul_cancel₀ hb, one_div]

/-- The integrand `e^{inθ} / (b + c e^{iθ})` has period `2π`. -/
private theorem periodic_exp_div_add (b c : ℂ) (n : ℤ) :
    Function.Periodic (fun θ : ℝ => exp (n * θ * I) / (b + c * exp (θ * I))) (2 * π) := by
  simp_rw [exp_div_add_eq]
  exact (periodic_circleMap 0 1).comp fun w => w ^ n * (b + c * w)⁻¹

/-- The substitution `θ ↦ -θ` exchanges `b` and `c` and sends `n` to `1 - n`. -/
private theorem integral_exp_div_add_swap (b c : ℂ) (n : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (n * θ * I) / (b + c * exp (θ * I)) =
      ∫ θ in (0 : ℝ)..2 * π, exp ((1 - n : ℤ) * θ * I) / (c + b * exp (θ * I)) := by
  rw [← (periodic_exp_div_add b c n).intervalIntegral_comp_neg]
  congr 1
  ext θ
  have hw0 : exp (θ * I) ≠ 0 := exp_ne_zero _
  have h1 : exp (((-θ : ℝ) : ℂ) * I) = (exp (θ * I))⁻¹ := by
    rw [← exp_neg]
    push_cast
    ring_nf
  have h2 : exp (n * ((-θ : ℝ) : ℂ) * I) = (exp (θ * I) ^ n)⁻¹ := by
    rw [← exp_intCast_mul, ← exp_neg]
    push_cast
    ring_nf
  have h3 : exp ((1 - n : ℤ) * θ * I) = exp (θ * I) / exp (θ * I) ^ n := by
    rw [← exp_intCast_mul, ← exp_sub]
    push_cast
    ring_nf
  rw [h1, h2, h3]
  rcases eq_or_ne (c + b * exp (θ * I)) 0 with h | h
  · have h' : b + c * (exp (θ * I))⁻¹ = 0 := by
      rw [show b + c * (exp (θ * I))⁻¹ = (c + b * exp (θ * I)) / exp (θ * I) by field_simp; ring,
        h, zero_div]
    rw [h, h', div_zero, div_zero]
  · have hp : exp (θ * I) ^ n ≠ 0 := zpow_ne_zero n hw0
    field_simp
    rw [add_comm (b * _) c, div_self h]

/-- For `‖b‖ < ‖c‖` and `n ≤ 0`, `∫₀^{2π} e^{inθ} / (b + c e^{iθ}) dθ = 0`. -/
theorem integral_exp_div_add_of_lt_norm_of_nonpos {b c : ℂ} (hbc : ‖b‖ < ‖c‖) {n : ℤ}
    (hn : n ≤ 0) :
    ∫ θ in (0 : ℝ)..2 * π, exp (n * θ * I) / (b + c * exp (θ * I)) = 0 := by
  rw [integral_exp_div_add_swap]
  exact integral_exp_div_add_of_norm_lt_of_pos hbc (by omega)

/-- For `‖b‖ < ‖c‖` and `n ≥ 1`, `∫₀^{2π} e^{inθ} / (b + c e^{iθ}) dθ = 2π (-b)^{n-1} c^{-n}`. -/
theorem integral_exp_div_add_of_lt_norm_of_pos {b c : ℂ} (hbc : ‖b‖ < ‖c‖) {n : ℤ}
    (hn : 0 < n) :
    ∫ θ in (0 : ℝ)..2 * π, exp (n * θ * I) / (b + c * exp (θ * I)) =
      2 * π * (-b) ^ (n - 1) * c ^ (-n) := by
  rw [integral_exp_div_add_swap, integral_exp_div_add_of_norm_lt_of_nonpos hbc (by omega)]
  congr 2 <;> ring_nf


/-- For `‖c‖ < ‖b‖`, `∫₀^{2π} 1 / (b + c e^{−iθ}) dθ = 2π / b`. -/
theorem integral_inv_add_mul_exp_neg {b c : ℂ} (hcb : ‖c‖ < ‖b‖) :
    ∫ θ in (0 : ℝ)..2 * π, (b + c * exp (-(θ * I)))⁻¹ = 2 * π / b := by
  have h := integral_exp_div_add_of_norm_lt_of_nonpos hcb (n := 0) le_rfl
  simp only [Int.cast_zero, zero_mul, exp_zero, one_div, neg_zero, mul_one, zero_sub, zpow_zero,
    zpow_neg_one] at h
  have h2 := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => (b + c * exp (-(θ * I)))⁻¹) (2 * π) (a := 0) (b := 2 * π)
  simp only [sub_self, sub_zero] at h2
  rw [← h2, div_eq_mul_inv, ← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [show -(((2 * π - θ : ℝ) : ℂ) * I) = θ * I + (-1 : ℤ) * (2 * π * I) by push_cast; ring,
    exp_add, exp_int_mul_two_pi_mul_I, mul_one]

end TauCeti
