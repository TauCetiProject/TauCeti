/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Logarithmic power moments on the unit interval

For `r > -1` and `s > -1`, the substitution `t = exp (-u)` identifies the logarithmic moment
`∫ t in 0..1, t ^ r * (-log t) ^ s` with Euler's Gamma integral
`∫ u in Ioi 0, u ^ s * exp (-((r + 1) * u)) = Gamma (s + 1) / (r + 1) ^ (s + 1)`.
Specializing `s` to a natural exponent `k : ℕ` yields the factorial moments
`∫ t in 0..1, t ^ r * (-log t) ^ k = k! / (r + 1) ^ (k + 1)` and their signed counterparts
`∫ t in 0..1, t ^ r * (log t) ^ k = (-1) ^ k * k! / (r + 1) ^ (k + 1)`, while interval
integrability of `t ↦ t ^ r * (log t) ^ k` (`r > -1`, `k : ℕ`) extends from `[0, 1]` to every
interval `a..b`.

These moments evaluate the radial integral representation of positive-weight polylogarithms term
by term against the Taylor series of `-log (1 - t z)`.

## Main declarations

* `TauCeti.intervalIntegrable_rpow_mul_neg_log_rpow` and
  `TauCeti.intervalIntegrable_neg_log_rpow`: `t ↦ t ^ r * (-log t) ^ s` and `t ↦ (-log t) ^ s`
  are interval integrable on `[0, 1]` for `r > -1` and `s > -1`.
* `TauCeti.integral_rpow_mul_neg_log_rpow` and `TauCeti.integral_neg_log_rpow`:
  `∫ t in 0..1, t ^ r * (-log t) ^ s = Gamma (s + 1) / (r + 1) ^ (s + 1)` and
  `∫ t in 0..1, (-log t) ^ s = Gamma (s + 1)` for `r > -1` and `s > -1`.
* `TauCeti.intervalIntegrable_rpow_mul_log_pow`,
  `TauCeti.intervalIntegrable_rpow_mul_neg_log_pow`,
  `TauCeti.intervalIntegrable_pow_mul_log_pow`, and
  `TauCeti.intervalIntegrable_pow_mul_neg_log_pow`: `t ↦ t ^ r * (log t) ^ k` and
  `t ↦ t ^ r * (-log t) ^ k` (`r > -1`, `k : ℕ`), with natural-power specializations, are
  interval integrable on every interval `a..b`.
* `TauCeti.integral_rpow_mul_neg_log_pow` and `TauCeti.integral_rpow_mul_log_pow`:
  `∫ t in 0..1, t ^ r * (-log t) ^ k = k! / (r + 1) ^ (k + 1)` and
  `∫ t in 0..1, t ^ r * (log t) ^ k = (-1) ^ k * k! / (r + 1) ^ (k + 1)` for `r > -1`.
* `TauCeti.integral_pow_mul_neg_log_pow` and `TauCeti.integral_pow_mul_log_pow`: the
  natural-power specializations `k! / (m + 1) ^ (k + 1)` and
  `(-1) ^ k * k! / (m + 1) ^ (k + 1)`.
* `TauCeti.integral_neg_log_pow` and `TauCeti.integral_log_pow`: the unweighted logarithmic
  moments `∫ t in 0..1, (-log t) ^ k = k!` and `∫ t in 0..1, (log t) ^ k = (-1) ^ k * k!`.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- For `r > -1` and `s > -1`, the logarithmic Gamma-moment integrand
`t ↦ t ^ r * (-log t) ^ s` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_rpow_mul_neg_log_rpow {r s : ℝ} (hr : -1 < r) (hs : -1 < s) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ r * (-Real.log t) ^ s) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one,
    show Ioo (0 : ℝ) 1 = Real.exp '' Iio 0 by rw [Real.image_exp_Iio, Real.exp_zero],
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Iio
      (fun u _ ↦ (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
  have hgam :
      IntegrableOn (fun u : ℝ ↦ u ^ s * Real.exp (-(r + 1) * u ^ (1 : ℝ))) (Ioi (-0)) := by
    rw [neg_zero]
    exact integrableOn_rpow_mul_exp_neg_mul_rpow hs zero_lt_one (by linarith)
  refine hgam.comp_neg_Iio.congr_fun (fun u _ ↦ ?_) measurableSet_Iio
  simp only [smul_eq_mul, abs_of_pos (Real.exp_pos _), Real.rpow_one, ← Real.exp_mul, Real.log_exp]
  rw [← mul_assoc, ← Real.exp_add, mul_comm _ ((-u) ^ s)]
  congr 2
  ring

/-- For `s > -1`, `t ↦ (-log t) ^ s` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_neg_log_rpow {s : ℝ} (hs : -1 < s) :
    IntervalIntegrable (fun t : ℝ ↦ (-Real.log t) ^ s) volume 0 1 := by
  simpa using intervalIntegrable_rpow_mul_neg_log_rpow (r := 0) (by norm_num) hs

/-- For `r > -1` and `s > -1`,
`∫ t in 0..1, t ^ r * (-log t) ^ s = Gamma (s + 1) / (r + 1) ^ (s + 1)`. -/
theorem integral_rpow_mul_neg_log_rpow {r s : ℝ} (hr : -1 < r) (hs : -1 < s) :
    ∫ t : ℝ in 0..1, t ^ r * (-Real.log t) ^ s = Real.Gamma (s + 1) / (r + 1) ^ (s + 1) := by
  have hr1 : 0 < r + 1 := by linarith
  have hs1 : 0 < s + 1 := by linarith
  rw [intervalIntegral.integral_of_le zero_le_one,
    show Ioc (0 : ℝ) 1 = Real.exp '' Iic 0 by rw [Real.image_exp_Iic, Real.exp_zero],
    integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
      (fun u _ ↦ (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn,
    show Iic (0 : ℝ) = Iic (-0) by simp, ← integral_comp_neg_Ioi]
  have hcongr : ∫ u : ℝ in Ioi 0,
      |Real.exp (-u)| • (Real.exp (-u) ^ r * (-Real.log (Real.exp (-u))) ^ s) =
      ∫ u : ℝ in Ioi 0, u ^ (s + 1 - 1) * Real.exp (-((r + 1) * u)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
    simp only [smul_eq_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_mul, Real.log_exp, neg_neg,
      add_sub_cancel_right]
    rw [← mul_assoc, ← Real.exp_add, mul_comm _ (u ^ s)]
    congr 2
    ring
  rw [hcongr, Real.integral_rpow_mul_exp_neg_mul_Ioi hs1 hr1, one_div, Real.inv_rpow hr1.le,
    mul_comm, ← div_eq_mul_inv]

/-- For `s > -1`, `∫ t in 0..1, (-log t) ^ s = Gamma (s + 1)`. -/
theorem integral_neg_log_rpow {s : ℝ} (hs : -1 < s) :
    ∫ t : ℝ in 0..1, (-Real.log t) ^ s = Real.Gamma (s + 1) := by
  simpa using integral_rpow_mul_neg_log_rpow (r := 0) (by norm_num) hs

/-- For `r > -1` and `k : ℕ`, `t ↦ t ^ r * (log t) ^ k` is interval integrable on every interval
`a..b`. -/
theorem intervalIntegrable_rpow_mul_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) {a b : ℝ} :
    IntervalIntegrable (fun t : ℝ ↦ t ^ r * Real.log t ^ k) volume a b := by
  have h01 : IntervalIntegrable (fun t : ℝ ↦ t ^ r * Real.log t ^ k) volume 0 1 := by
    have hk : -1 < (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
    refine ((intervalIntegrable_rpow_mul_neg_log_rpow hr hk).const_mul ((-1 : ℝ) ^ k)).congr
      fun t _ ↦ ?_
    rw [Real.rpow_natCast, mul_left_comm, ← mul_pow, neg_one_mul, neg_neg]
  have hnonneg : ∀ c : ℝ, 0 ≤ c →
      IntervalIntegrable (fun t : ℝ ↦ t ^ r * Real.log t ^ k) volume 0 c := by
    intro c hc
    rcases le_or_gt c 1 with hc1 | hc1
    · exact h01.mono_set
        (by rw [uIcc_of_le hc, uIcc_of_le zero_le_one]; exact Icc_subset_Icc_right hc1)
    · refine h01.trans (ContinuousOn.intervalIntegrable ?_)
      rw [uIcc_of_le hc1.le]
      exact ((continuousOn_id' (Icc 1 c)).rpow_const fun t ht ↦ Or.inl (by linarith [ht.1])).mul
        ((Real.continuousOn_log.mono fun t ht ↦ by simp; linarith [ht.1]).pow k)
  have hzero : ∀ c : ℝ,
      IntervalIntegrable (fun t : ℝ ↦ t ^ r * Real.log t ^ k) volume 0 c := by
    intro c
    rcases le_total 0 c with hc | hc
    · exact hnonneg c hc
    · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
      refine ((hnonneg (-c) (by linarith)).const_mul (Real.cos (r * Real.pi))).congr fun t ht ↦ ?_
      rw [uIoc_of_le (by linarith)] at ht
      simp only [Real.rpow_def_of_neg (neg_lt_zero.mpr ht.1), Real.log_neg_eq_log,
        ← Real.rpow_def_of_pos ht.1]
      ring
  exact (hzero a).symm.trans (hzero b)

/-- For `r > -1` and `k : ℕ`, `t ↦ t ^ r * (-log t) ^ k` is interval integrable on every interval
`a..b`. -/
theorem intervalIntegrable_rpow_mul_neg_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) {a b : ℝ} :
    IntervalIntegrable (fun t : ℝ ↦ t ^ r * (-Real.log t) ^ k) volume a b := by
  refine ((intervalIntegrable_rpow_mul_log_pow hr k).const_mul ((-1 : ℝ) ^ k)).congr fun t _ ↦ ?_
  rw [mul_left_comm, ← mul_pow, neg_one_mul]

/-- Every natural-power logarithmic integrand `t ↦ t ^ m * (log t) ^ k` is interval integrable on
every interval `a..b`. -/
theorem intervalIntegrable_pow_mul_log_pow (m k : ℕ) {a b : ℝ} :
    IntervalIntegrable (fun t : ℝ ↦ t ^ m * Real.log t ^ k) volume a b := by
  simpa using intervalIntegrable_rpow_mul_log_pow
    (r := (m : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) m]) k

/-- Every natural-power logarithmic integrand `t ↦ t ^ m * (-log t) ^ k` is interval integrable on
every interval `a..b`. -/
theorem intervalIntegrable_pow_mul_neg_log_pow (m k : ℕ) {a b : ℝ} :
    IntervalIntegrable (fun t : ℝ ↦ t ^ m * (-Real.log t) ^ k) volume a b := by
  simpa using intervalIntegrable_rpow_mul_neg_log_pow
    (r := (m : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) m]) k

/-- For `r > -1` and `k : ℕ`, `∫ t in 0..1, t ^ r * (-log t) ^ k = k! / (r + 1) ^ (k + 1)`. -/
theorem integral_rpow_mul_neg_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) :
    ∫ t : ℝ in 0..1, t ^ r * (-Real.log t) ^ k = (k.factorial : ℝ) / (r + 1) ^ (k + 1) := by
  have hk : -1 < (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have h := integral_rpow_mul_neg_log_rpow hr hk
  simp_rw [Real.rpow_natCast] at h
  rwa [Real.Gamma_nat_eq_factorial, ← Nat.cast_add_one, Real.rpow_natCast] at h

/-- For `r > -1` and `k : ℕ`,
`∫ t in 0..1, t ^ r * (log t) ^ k = (-1) ^ k * k! / (r + 1) ^ (k + 1)`. -/
theorem integral_rpow_mul_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) :
    ∫ t : ℝ in 0..1, t ^ r * Real.log t ^ k =
      (-1 : ℝ) ^ k * (k.factorial : ℝ) / (r + 1) ^ (k + 1) := by
  have h : (fun t : ℝ ↦ t ^ r * Real.log t ^ k) =
      fun t : ℝ ↦ (-1 : ℝ) ^ k * (t ^ r * (-Real.log t) ^ k) := by
    ext t
    rw [mul_left_comm, ← mul_pow, neg_one_mul, neg_neg]
  rw [h, intervalIntegral.integral_const_mul, integral_rpow_mul_neg_log_pow hr k, mul_div_assoc]

/-- For `m, k : ℕ`, `∫ t in 0..1, t ^ m * (-log t) ^ k = k! / (m + 1) ^ (k + 1)`. -/
theorem integral_pow_mul_neg_log_pow (m k : ℕ) :
    ∫ t : ℝ in 0..1, t ^ m * (-Real.log t) ^ k = (k.factorial : ℝ) / (m + 1 : ℝ) ^ (k + 1) := by
  simpa using integral_rpow_mul_neg_log_pow
    (r := (m : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) m]) k

/-- For `m, k : ℕ`, `∫ t in 0..1, t ^ m * (log t) ^ k = (-1) ^ k * k! / (m + 1) ^ (k + 1)`. -/
theorem integral_pow_mul_log_pow (m k : ℕ) :
    ∫ t : ℝ in 0..1, t ^ m * Real.log t ^ k =
      (-1 : ℝ) ^ k * (k.factorial : ℝ) / (m + 1 : ℝ) ^ (k + 1) := by
  simpa using integral_rpow_mul_log_pow
    (r := (m : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) m]) k

/-- For `k : ℕ`, `∫ t in 0..1, (-log t) ^ k = k!`. -/
theorem integral_neg_log_pow (k : ℕ) :
    ∫ t : ℝ in 0..1, (-Real.log t) ^ k = k.factorial := by
  simpa using integral_pow_mul_neg_log_pow 0 k

/-- For `k : ℕ`, `∫ t in 0..1, (log t) ^ k = (-1) ^ k * k!`. -/
theorem integral_log_pow (k : ℕ) :
    ∫ t : ℝ in 0..1, Real.log t ^ k = (-1 : ℝ) ^ k * k.factorial := by
  simpa using integral_pow_mul_log_pow 0 k

end TauCeti
