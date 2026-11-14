/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TauCeti.MeasureTheory.Integral.Gamma

/-!
# Moments of the Gaussian

This file computes the moments of the Gaussian `exp(-b x²)`, `b > 0`, over the real line. The
absolute moment of every real order `q > -1` is
`∫ |x| ^ q exp(-b x²) dx = b ^ (-(q + 1) / 2) Γ((q + 1) / 2)`
(`TauCeti.integral_abs_rpow_mul_exp_neg_mul_sq`), the case `p = 2` of the two-sided Gamma integral
`TauCeti.integral_abs_rpow_mul_exp_neg_mul_abs_rpow`.

At even integer orders, Mathlib's `Real.Gamma_nat_add_half` turns this into
`∫ x ^ (2k) exp(-b x²) dx = (2k - 1)‼ √π / ((2b) ^ k √b)`
(`TauCeti.integral_pow_two_mul_mul_exp_neg_mul_sq`), and the second moment is
`∫ x² exp(-b x²) dx = √π / (2 b √b)` (`TauCeti.integral_sq_mul_exp_neg_mul_sq`). Together with
Mathlib's `integral_gaussian`, `∫ exp(-b x²) dx = √(π / b)`, the second moment evaluates the
squared `L²` norms of a Gaussian and of its derivative.
-/

public section

open Real
open scoped Nat

namespace TauCeti

/-- The absolute moments of the Gaussian: for `b > 0` and `q > -1`,
`∫ |x| ^ q exp(-b x²) dx = b ^ (-(q + 1) / 2) Γ((q + 1) / 2)`. -/
theorem integral_abs_rpow_mul_exp_neg_mul_sq {b q : ℝ} (hb : 0 < b) (hq : -1 < q) :
    ∫ x : ℝ, |x| ^ q * Real.exp (-b * x ^ 2) =
      b ^ (-(q + 1) / 2) * Real.Gamma ((q + 1) / 2) := by
  have h := integral_abs_rpow_mul_exp_neg_mul_abs_rpow two_pos hq hb
  simp only [Real.rpow_two, sq_abs] at h
  rw [h]
  ring

/-- The even moments of the Gaussian: for `b > 0`,
`∫ x ^ (2k) exp(-b x²) dx = (2k - 1)‼ √π / ((2b) ^ k √b)`. -/
theorem integral_pow_two_mul_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (k : ℕ) :
    ∫ x : ℝ, x ^ (2 * k) * Real.exp (-b * x ^ 2) =
      (2 * k - 1 : ℕ)‼ * √π / ((2 * b) ^ k * √b) := by
  have h := integral_abs_rpow_mul_exp_neg_mul_sq hb (q := ((2 * k : ℕ) : ℝ))
    (by have := (2 * k : ℕ).cast_nonneg (α := ℝ); linarith)
  simp only [Real.rpow_natCast, (even_two_mul k).pow_abs] at h
  have hq : ((2 * k : ℕ) + 1 : ℝ) / 2 = k + 1 / 2 := by push_cast; ring
  have hb' : b ^ (-(((2 * k : ℕ) : ℝ) + 1) / 2) = (b ^ k * √b)⁻¹ := by
    rw [neg_div, hq, Real.rpow_neg hb.le, Real.rpow_add hb, Real.rpow_natCast,
      ← Real.sqrt_eq_rpow]
  rw [h, hq, Real.Gamma_nat_add_half, hb']
  have : 0 < √b := Real.sqrt_pos.mpr hb
  field_simp
  ring

/-- The second moment of the Gaussian: `∫ x² exp(-b x²) dx = √π / (2 b √b)` for `b > 0`. -/
theorem integral_sq_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) = √π / (2 * b * √b) := by
  simpa using integral_pow_two_mul_mul_exp_neg_mul_sq hb 1

end TauCeti
