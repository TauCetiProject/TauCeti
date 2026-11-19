/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian integral in power form

The integral of a Gaussian with positive rate can be expressed using a negative half-power
of the rate.
-/

public section

open MeasureTheory Real

namespace TauCeti

/-- The Gaussian integral with positive rate, in negative half-power form. -/
theorem integral_exp_neg_mul_sq_eq_rpow {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, exp (-(b * x ^ 2))) = b ^ (-(1 : ℝ) / 2) * sqrt π := by
  have hGaussian : (∫ x : ℝ, exp (-(b * x ^ 2))) = sqrt (π / b) := by
    simpa only [neg_mul] using integral_gaussian b
  rw [hGaussian, Real.sqrt_div Real.pi_pos.le, Real.sqrt_eq_rpow b,
    neg_div, Real.rpow_neg hb.le]
  ring

end TauCeti
