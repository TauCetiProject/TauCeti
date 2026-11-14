/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Logarithmic power moments on the unit interval

For `r > -1` and `k : ℕ`, the substitution `t = exp (-u)` identifies the logarithmic moment
`∫ t in 0..1, t ^ r * (-log t) ^ k` with Euler's Gamma integral
`∫ u in Ioi 0, u ^ k * exp (-((r + 1) * u)) = k! / (r + 1) ^ (k + 1)`.

These moments evaluate the radial integral representation of positive-weight polylogarithms term
by term against the Taylor series of `-log (1 - t z)`.

## Main declarations

* `TauCeti.intervalIntegrable_rpow_mul_neg_log_pow`: `t ↦ t ^ r * (-log t) ^ k` is interval
  integrable on `[0, 1]` for `r > -1`.
* `TauCeti.integral_rpow_mul_neg_log_pow`:
  `∫ t in 0..1, t ^ r * (-log t) ^ k = k! / (r + 1) ^ (k + 1)` for `r > -1`.
* `TauCeti.integral_pow_mul_neg_log_pow`: the natural-power specialization
  `∫ t in 0..1, t ^ m * (-log t) ^ k = k! / (m + 1) ^ (k + 1)`.
* `TauCeti.integral_neg_log_pow` and `TauCeti.integral_log_pow`: the unweighted logarithmic
  moments `∫ t in 0..1, (-log t) ^ k = k!` and `∫ t in 0..1, (log t) ^ k = (-1) ^ k * k!`.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- For `r > -1` and `k : ℕ`, the logarithmic moment integrand `t ↦ t ^ r * (-log t) ^ k` is
interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_rpow_mul_neg_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ r * (-Real.log t) ^ k) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one,
    show Ioo (0 : ℝ) 1 = Real.exp '' Iio 0 by rw [Real.image_exp_Iio, Real.exp_zero],
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Iio
      (fun u _ ↦ (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
  have hgam :
      IntegrableOn (fun u : ℝ ↦ u ^ (k : ℝ) * Real.exp (-(r + 1) * u ^ (1 : ℝ))) (Ioi (-0)) := by
    rw [neg_zero]
    exact integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith [Nat.cast_nonneg (α := ℝ) k])
      zero_lt_one (by linarith)
  refine hgam.comp_neg_Iio.congr_fun (fun u _ ↦ ?_) measurableSet_Iio
  dsimp only
  rw [smul_eq_mul, abs_of_pos (Real.exp_pos _), Real.rpow_one, Real.rpow_natCast,
    ← Real.exp_mul, Real.log_exp]
  rw [mul_comm ((-u) ^ k), ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Every natural-power logarithmic moment integrand `t ↦ t ^ m * (-log t) ^ k` is interval
integrable on `[0, 1]`. -/
theorem intervalIntegrable_pow_mul_neg_log_pow (m k : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ m * (-Real.log t) ^ k) volume 0 1 := by
  simpa using intervalIntegrable_rpow_mul_neg_log_pow
    (r := (m : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) m]) k

/-- For `r > -1` and `k : ℕ`, `∫ t in 0..1, t ^ r * (-log t) ^ k = k! / (r + 1) ^ (k + 1)`. -/
theorem integral_rpow_mul_neg_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) :
    ∫ t : ℝ in 0..1, t ^ r * (-Real.log t) ^ k = (k.factorial : ℝ) / (r + 1) ^ (k + 1) := by
  have hr1 : 0 < r + 1 := by linarith
  rw [intervalIntegral.integral_of_le zero_le_one,
    show Ioc (0 : ℝ) 1 = Real.exp '' Iic 0 by rw [Real.image_exp_Iic, Real.exp_zero],
    integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
      (fun u _ ↦ (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn,
    show Iic (0 : ℝ) = Iic (-0) by simp, ← integral_comp_neg_Ioi]
  have hcongr : ∫ u : ℝ in Ioi 0,
      |Real.exp (-u)| • (Real.exp (-u) ^ r * (-Real.log (Real.exp (-u))) ^ k) =
      ∫ u : ℝ in Ioi 0, u ^ (((k + 1 : ℕ) : ℝ) - 1) * Real.exp (-((r + 1) * u)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
    rw [smul_eq_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_mul, Real.log_exp, neg_neg,
      Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast]
    rw [mul_comm (u ^ k), ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hcongr, Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hr1, Real.rpow_natCast,
    Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial, one_div, inv_pow, div_eq_mul_inv,
    mul_comm]

/-- For `m, k : ℕ`, `∫ t in 0..1, t ^ m * (-log t) ^ k = k! / (m + 1) ^ (k + 1)`. -/
theorem integral_pow_mul_neg_log_pow (m k : ℕ) :
    ∫ t : ℝ in 0..1, t ^ m * (-Real.log t) ^ k = (k.factorial : ℝ) / (m + 1 : ℝ) ^ (k + 1) := by
  simpa using integral_rpow_mul_neg_log_pow
    (r := (m : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) m]) k

/-- For `k : ℕ`, `∫ t in 0..1, (-log t) ^ k = k!`. -/
theorem integral_neg_log_pow (k : ℕ) :
    ∫ t : ℝ in 0..1, (-Real.log t) ^ k = k.factorial := by
  simpa using integral_pow_mul_neg_log_pow 0 k

/-- For `k : ℕ`, `∫ t in 0..1, (log t) ^ k = (-1) ^ k * k!`. -/
theorem integral_log_pow (k : ℕ) :
    ∫ t : ℝ in 0..1, Real.log t ^ k = (-1 : ℝ) ^ k * k.factorial := by
  have h : (fun t : ℝ ↦ Real.log t ^ k) = fun t : ℝ ↦ (-1 : ℝ) ^ k * (-Real.log t) ^ k := by
    ext t
    rw [← mul_pow]
    ring_nf
  rw [h, intervalIntegral.integral_const_mul, integral_neg_log_pow]

end TauCeti
