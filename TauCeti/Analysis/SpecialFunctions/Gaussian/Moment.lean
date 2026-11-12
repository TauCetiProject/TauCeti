/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The second moment of the Gaussian

This file computes `∫ x² exp(-b x²) dx = √π / (2 b √b)` over the real line for `b > 0`
(`TauCeti.integral_sq_mul_exp_neg_mul_sq`). Together with Mathlib's `integral_gaussian`,
`∫ exp(-b x²) dx = √(π / b)`, it evaluates the squared `L²` norms of a Gaussian and of its
derivative.

The integrand is even, so the integral is twice the integral over `(0, ∞)`, which Mathlib's
`integral_rpow_mul_exp_neg_mul_rpow` evaluates as `b^{-3/2} Γ(3/2) / 2`, and `Γ(3/2) = √π / 2`.
-/

public section

open Real

namespace TauCeti

/-- The second moment of the Gaussian: `∫ x² exp(-b x²) dx = √π / (2 b √b)` for `b > 0`. -/
theorem integral_sq_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) = √π / (2 * b * √b) := by
  have h := integral_comp_abs (f := fun y ↦ y ^ 2 * Real.exp (-b * y ^ 2))
  simp only [sq_abs] at h
  have h2 := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) two_pos (by norm_num) hb
  simp only [Real.rpow_two] at h2
  have hΓ : Real.Gamma ((2 + 1) / 2) = √π / 2 := by
    rw [show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have hb' : b ^ (-(2 + 1) / 2 : ℝ) = (b * √b)⁻¹ := by
    rw [show (-(2 + 1) / 2 : ℝ) = -(1 + 1 / 2) by norm_num, Real.rpow_neg hb.le,
      Real.rpow_add hb, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [h, h2, hΓ, hb']
  have : 0 < √b := Real.sqrt_pos.mpr hb
  field_simp

end TauCeti
