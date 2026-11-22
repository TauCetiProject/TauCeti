/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.Complex.Laurent.Basic
import TauCeti.Analysis.Complex.Periodic
import TauCeti.Analysis.Complex.PowerSeries.FourierCoeff

/-!
# Circle Laurent coefficients of periodic cusp functions

For an `h`-periodic function `f : ℂ → ℂ` (`0 < h`), the unit-circle Laurent coefficients of its
cusp function `Function.Periodic.cuspFunction h f` equal the interval Fourier coefficients
`fourierCoeffOn` of `t ↦ f t` on `[0, h]` (`circleLaurentCoeff_cuspFunction_eq_fourierCoeffOn`).
-/

public section

open Complex
open scoped Real

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
  have hscale : 2 * π / h ≠ 0 := div_ne_zero Real.two_pi_pos.ne' hh.ne'
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun θ : ℝ => circleMap 0 1 θ ^ (-m) • Function.Periodic.cuspFunction h f (circleMap 0 1 θ))
    (a := (0 : ℝ)) (b := h) hscale
  have hmul_h : (2 * π / h) * h = 2 * π := by field_simp [hh.ne']
  simp only [mul_zero, hmul_h, smul_eq_mul] at hsub ⊢
  have hsub' :
      (∫ θ in (0 : ℝ)..2 * π,
        circleMap 0 1 θ ^ (-m) * Function.Periodic.cuspFunction h f (circleMap 0 1 θ)) =
      (2 * π / h) • ∫ t in (0 : ℝ)..h,
        circleMap 0 1 ((2 * π / h) * t) ^ (-m) *
          Function.Periodic.cuspFunction h f (circleMap 0 1 ((2 * π / h) * t)) := by
    rw [hsub, smul_smul, mul_inv_cancel₀ hscale, one_smul]
  rw [hsub', smul_smul, fourierCoeffOn_eq_integral]
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

end TauCeti
