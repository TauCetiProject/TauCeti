/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Cesàro averages of unitary characters on the real line

For a real frequency `u`, the unitary character `t ↦ exp (i t u)` has unit modulus everywhere, so
its Cesàro average `T⁻¹ ∫₀ᵀ exp (i t u) dt` is uniformly bounded by `1`. For nonzero `u`, direct
integration gives the oscillatory cancellation bound `‖∫ₐᵇ exp (i t u) dt‖ ≤ 2 / |u|`, hence the
Cesàro average converges to `0` as `T → ∞`, whereas at `u = 0` it is identically `1` for `T ≠ 0`.

This is the spectral-side kernel behind the continuous-time mean ergodic theorem and Wiener's
lemma on atomic masses of spectral measures.

## Main results

* `TauCeti.norm_intervalIntegral_exp_mul_I_le_div`: oscillatory bound
  `‖∫ t in a..b, exp (t * u * I)‖ ≤ 2 / |u|` for `u ≠ 0`.
* `TauCeti.norm_inv_mul_intervalIntegral_exp_mul_I_le`: uniform bound
  `‖T⁻¹ * ∫ t in 0..T, exp (t * u * I)‖ ≤ 1`.
* `TauCeti.tendsto_inv_mul_intervalIntegral_exp_mul_I`: convergence of the Cesàro average to
  `1` if `u = 0` and `0` otherwise.
-/

public section

open Filter MeasureTheory
open scoped Topology

namespace TauCeti

/-- Oscillatory cancellation for a nonzero-frequency unitary character: the integral of
`t ↦ exp (i t u)` over any interval `[a, b]` has norm at most `2 / |u|`. -/
theorem norm_intervalIntegral_exp_mul_I_le_div {u : ℝ} (hu : u ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b, Complex.exp (t * u * Complex.I)‖ ≤ 2 / |u| := by
  have hc : (u : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hu) Complex.I_ne_zero
  have hint :
      (∫ t in a..b, Complex.exp (t * u * Complex.I)) =
        (Complex.exp ((u : ℂ) * Complex.I * b) - Complex.exp ((u : ℂ) * Complex.I * a)) /
          ((u : ℂ) * Complex.I) := by
    have hcongr :
        (fun t : ℝ ↦ Complex.exp (t * u * Complex.I)) =
          fun t : ℝ ↦ Complex.exp (((u : ℂ) * Complex.I) * t) := by
      ext t
      congr 1
      ring
    rw [hcongr, integral_exp_mul_complex hc]
  have hnorm_exp (x : ℝ) : ‖Complex.exp ((u : ℂ) * Complex.I * x)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hint, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  gcongr
  calc
    ‖Complex.exp ((u : ℂ) * Complex.I * b) - Complex.exp ((u : ℂ) * Complex.I * a)‖
        ≤ ‖Complex.exp ((u : ℂ) * Complex.I * b)‖ + ‖Complex.exp ((u : ℂ) * Complex.I * a)‖ :=
      norm_sub_le _ _
    _ = 2 := by rw [hnorm_exp b, hnorm_exp a]; norm_num

/-- The Cesàro average `T⁻¹ ∫₀ᵀ exp (i t u) dt` has norm at most `1` for every real `T` and `u`. -/
theorem norm_inv_mul_intervalIntegral_exp_mul_I_le (T u : ℝ) :
    ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * u * Complex.I)‖ ≤ 1 := by
  rcases eq_or_ne T 0 with rfl | hT
  · simp
  · have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) T, ‖Complex.exp (t * u * Complex.I)‖ ≤ (1 : ℝ) := by
      intro t _
      rw [Complex.norm_exp]
      simp
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [sub_zero, one_mul] at hint
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    calc
      |T|⁻¹ * ‖∫ t in (0 : ℝ)..T, Complex.exp (t * u * Complex.I)‖
          ≤ |T|⁻¹ * |T| := by gcongr
      _ = 1 := inv_mul_cancel₀ (abs_ne_zero.mpr hT)

/-- **Cesàro average of a unitary character.** As `T → ∞`, the average
`T⁻¹ ∫₀ᵀ exp (i t u) dt` converges to `1` when `u = 0` and to `0` when `u ≠ 0`. -/
theorem tendsto_inv_mul_intervalIntegral_exp_mul_I (u : ℝ) :
    Tendsto (fun T : ℝ ↦ (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * u * Complex.I))
      atTop (𝓝 (if u = 0 then 1 else 0)) := by
  split_ifs with hu
  · subst hu
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simp [Complex.ofReal_ne_zero.mpr hT.ne']
  · refine squeeze_zero_norm' ?_
      (by simpa using (tendsto_inv_atTop_zero.const_mul (2 / |u|)) :
        Tendsto (fun T : ℝ ↦ (2 / |u|) * T⁻¹) atTop (𝓝 0))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_intervalIntegral_exp_mul_I_le_div hu 0 T)
      (inv_nonneg.mpr hT.le)

end TauCeti
