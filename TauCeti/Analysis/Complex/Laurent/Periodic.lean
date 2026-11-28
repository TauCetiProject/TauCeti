/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.Complex.Laurent.Series
import TauCeti.Analysis.Complex.Laurent.Expansion
import TauCeti.Analysis.Complex.Periodic
import TauCeti.Analysis.Complex.PowerSeries.FourierCoeff

/-!
# Circle Laurent coefficients and expansions of periodic cusp functions

For an `h`-periodic function `f : ℂ → ℂ` (`0 < h`), the unit-circle Laurent coefficients of its
cusp function `Function.Periodic.cuspFunction h f` equal the interval Fourier coefficients
`fourierCoeffOn` of `t ↦ f t` on `[0, h]` (`circleLaurentCoeff_cuspFunction_eq_fourierCoeffOn`).
When `f` is entire, `cuspFunction h f` admits a convergent Laurent series on `ℂ \ {0}` with
coefficients `fourierCoeffOn hh (fun t : ℝ => f t)` (`hasLaurentSeriesOnAnnulus_cuspFunction`).
-/

public section

open Complex Metric
open scoped Real ENNReal

namespace TauCeti

/-- For any `h`-periodic function `f : ℂ → ℂ` (`0 < h`), the `m`-th circle Laurent coefficient of
its cusp function `Function.Periodic.cuspFunction h f` on the unit circle equals the `m`-th
Fourier coefficient `fourierCoeffOn` of the real restriction `t ↦ f t` on `[0, h]`. -/
theorem circleLaurentCoeff_cuspFunction_eq_fourierCoeffOn {h : ℝ} (hh : 0 < h)
    {f : ℂ → ℂ} (hf : Function.Periodic f h) (m : ℤ) :
    circleLaurentCoeff (Function.Periodic.cuspFunction h f) 0 1 m =
      fourierCoeffOn hh (fun t : ℝ => f t) m := by
  rw [circleLaurentCoeff_def, circleIntegral_sub_zpow_sub_one_smul _ 0 one_ne_zero (-m),
    smul_smul, smul_eq_mul]
  have hcoef : (2 * π * I : ℂ)⁻¹ * I = ((2 * π)⁻¹ : ℝ) := by
    have h2pi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
    push_cast
    field_simp [h2pi, I_ne_zero]
  rw [hcoef, ← Complex.real_smul]
  have hsub := (intervalIntegral.smul_integral_comp_mul_left
    (f := fun θ : ℝ =>
      circleMap 0 1 θ ^ (-m) • Function.Periodic.cuspFunction h f (circleMap 0 1 θ))
    (a := (0 : ℝ)) (b := h) (2 * π / h)).symm
  have hmul_h : (2 * π / h) * h = 2 * π := by field_simp [hh.ne']
  rw [mul_zero, hmul_h] at hsub
  rw [hsub, smul_smul, fourierCoeffOn_eq_integral]
  have hscalar : ((2 * π)⁻¹ * (2 * π / h) : ℝ) = 1 / h := by
    field_simp [Real.two_pi_pos.ne', hh.ne']
  rw [hscalar, sub_zero]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hcmap : circleMap 0 1 ((2 * π / h) * t) = Function.Periodic.qParam h (t : ℂ) := by
    rw [circleMap, Function.Periodic.qParam]
    simp only [zero_add, one_mul, ofReal_one]
    congr 1
    push_cast
    ring
  rw [hcmap, Function.Periodic.eq_cuspFunction hh.ne' hf, Periodic.qParam_zpow]
  simp only [fourier_coe_apply, smul_eq_mul]

/-- For an entire `h`-periodic function `f : ℂ → ℂ` (`0 < h`), its cusp function
`Function.Periodic.cuspFunction h f` expands on the punctured plane `ℂ \ {0}` in a convergent
Laurent series whose coefficients are the interval Fourier coefficients
`fourierCoeffOn hh (fun t : ℝ => f t)`. -/
theorem hasLaurentSeriesOnAnnulus_cuspFunction {h : ℝ} (hh : 0 < h) {f : ℂ → ℂ}
    (hd : Differentiable ℂ f) (hf : Function.Periodic f h) :
    HasLaurentSeriesOnAnnulus (Function.Periodic.cuspFunction h f)
      (fourierCoeffOn hh (fun t : ℝ => f t)) 0 0 ⊤ := by
  have hdiff : DifferentiableOn ℂ (Function.Periodic.cuspFunction h f)
      (eball 0 ⊤ \ closedBall 0 0) := by
    intro w hw
    have hw0 : w ≠ 0 := fun h => hw.right (by simp [h])
    have hq : Function.Periodic.qParam h (Function.Periodic.invQParam h w) = w :=
      Function.Periodic.qParam_right_inv hh.ne' hw0
    rw [← hq]
    exact (Function.Periodic.differentiableAt_cuspFunction hh.ne' hf (hd _)).differentiableWithinAt
  have hL := hdiff.hasLaurentSeriesOnAnnulus le_rfl zero_lt_one ENNReal.ofReal_lt_top
  have hcoeff : circleLaurentCoeff (Function.Periodic.cuspFunction h f) 0 1 =
      fourierCoeffOn hh (fun t : ℝ => f t) :=
    funext fun m => circleLaurentCoeff_cuspFunction_eq_fourierCoeffOn hh hf m
  rwa [hcoeff] at hL

end TauCeti
