/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Limits
import TauCeti.Analysis.SpecialFunctions.Log.Bounds

/-!
# Integrals involving exponentials and `1 / t`

This file records integrability and interval-integral identities for `(e^u - 1) / u`,
`(1 - e^{-t}) / t`, `e^{-t} / t`, `e^u / u`, and `log t * e^{-t}`.

## Main declarations

* `Real.intervalIntegrable_exp_sub_one_div`: `(e^u - 1) / u` is interval integrable on `[a, b]`.
* `Real.intervalIntegrable_one_sub_exp_neg_div`: `(1 - e^{-t}) / t` is interval integrable on
  `[a, b]`.
* `Real.intervalIntegrable_exp_neg_div`: `e^{-t} / t` is interval integrable on `[a, b]` for
  `0 < a`, `0 < b`.
* `Real.integrableOn_Ioi_exp_neg_div`: `e^{-t} / t` is integrable on `(a, ∞)` for `a > 0`.
* `Real.integrableOn_Iic_exp_div`: `e^u / u` is integrable on `(-∞, y]` for `y < 0`.
* `Real.integrableOn_Ioi_log_mul_exp_neg`: `log t * e^{-t}` is integrable on `(0, ∞)`.
* `Real.integral_one_sub_exp_neg_div_eq_sub_integral`: integration by parts relating
  `∫ t in 0..z, (1 - e^{-t}) / t` and `∫ t in 0..z, log t * e^{-t}` for `z ≥ 0`.
* `Real.integral_exp_neg_div_eq_add_integral`: integration by parts relating
  `∫ t in 1..b, e^{-t} / t` and `∫ t in 1..b, log t * e^{-t}` for `b > 0`.
* `Real.integral_one_sub_exp_neg_div_eq_log_sub`: for `a, b > 0`,
  `∫ t in a..b, (1 - e^{-t}) / t = log b - log a - ∫ t in a..b, e^{-t} / t`.
* `Real.integral_exp_div_eq_log_sub_add`: for `a, b > 0`,
  `∫ u in a..b, e^u / u = log b - log a + ∫ u in a..b, (e^u - 1) / u`.
* `Real.integral_neg_exp_div`: reflection identity
  `∫ u in (-b)..(-a), e^u / u = -∫ t in a..b, e^{-t} / t`.
* `Real.summable_pow_div_mul_factorial`,
  `Real.hasDerivAt_tsum_pow_div_mul_factorial`, `Real.integral_exp_sub_one_div_eq_tsum`,
  `Real.integral_one_sub_exp_neg_div_eq`: power series for `(e^u - 1) / u`, its termwise
  antiderivative `∑' y ^ (n + 1) / ((n + 1) * (n + 1)!)`, and the integrals of `(e^u - 1) / u`
  and `(1 - e^{-t}) / t`.
-/

public section

open Filter MeasureTheory Set
open scoped Nat Topology

namespace Real

/-- `(e^u - 1) / u` is interval integrable on every interval `[a, b]`. -/
theorem intervalIntegrable_exp_sub_one_div (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦ (exp u - 1) / u) volume a b := by
  refine (continuous_update_exp_sub_one_div_zero.intervalIntegrable a b).congr_ae ?_
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [ae_restrict_of_ae hne] with u hu
  simp [hu]

/-- `(1 - e^{-t}) / t` is interval integrable on every interval `[a, b]`. -/
theorem intervalIntegrable_one_sub_exp_neg_div (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ (1 - exp (-t)) / t) volume a b := by
  refine (continuous_update_one_sub_exp_neg_div_zero.intervalIntegrable a b).congr_ae ?_
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [ae_restrict_of_ae hne] with t ht
  simp [ht]

/-- `e^{-t} / t` is interval integrable between any two positive endpoints `a, b > 0`. -/
theorem intervalIntegrable_exp_neg_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ ↦ exp (-t) / t) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine (continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id fun t ht ↦ ?_
  rw [mem_uIcc] at ht
  rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact (ha.trans_le h1).ne'
  · exact (hb.trans_le h1).ne'

/-- For every `a > 0`, `t ↦ exp (-t) / t` is integrable on `(a, ∞)`. -/
theorem integrableOn_Ioi_exp_neg_div {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ exp (-t) / t) (Ioi a) := by
  have hexp : IntegrableOn (fun t : ℝ ↦ a⁻¹ * exp (-t)) (Ioi a) :=
    (integrableOn_exp_neg_Ioi a).const_mul a⁻¹
  refine hexp.mono' ?_ ?_
  · exact ((continuous_exp.comp continuous_neg).measurable.div
      measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ha.trans ht
    rw [norm_eq_abs, abs_of_pos (div_pos (exp_pos _) ht0)]
    calc exp (-t) / t = t⁻¹ * exp (-t) := by rw [div_eq_mul_inv, mul_comm]
      _ ≤ a⁻¹ * exp (-t) := by gcongr; exact ht.le

/-- For every `y < 0`, `u ↦ exp u / u` is integrable on `(-∞, y]`. -/
theorem integrableOn_Iic_exp_div {y : ℝ} (hy : y < 0) :
    IntegrableOn (fun u : ℝ ↦ exp u / u) (Iic y) := by
  have hexp : IntegrableOn (fun u : ℝ ↦ (-y)⁻¹ * exp u) (Iic y) :=
    (integrableOn_exp_Iic y).const_mul (-y)⁻¹
  refine hexp.mono' ?_ ?_
  · exact (continuous_exp.measurable.div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
    have hu0 : u < 0 := hu.trans_lt hy
    rw [norm_eq_abs, abs_div, abs_of_pos (exp_pos u), abs_of_neg hu0, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (inv_anti₀ (neg_pos.mpr hy) (neg_le_neg (mem_Iic.mp hu))) (exp_pos u).le

/-- The integrand `log t * exp (-t)` is integrable on `(0, ∞)`. -/
theorem integrableOn_Ioi_log_mul_exp_neg :
    IntegrableOn (fun t : ℝ ↦ log t * exp (-t)) (Ioi 0) := by
  have h01 : IntegrableOn (fun t : ℝ ↦ log t * exp (-t)) (Ioc 0 1) := by
    have hrpow : IntegrableOn (fun t : ℝ ↦ √2 * t ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
      ((intervalIntegral.intervalIntegrable_rpow'
        (by norm_num : (-1 : ℝ) < -(1 / 2))).1).const_mul _
    refine hrpow.mono' ?_ ?_
    · exact (measurable_log.mul
        (continuous_exp.comp continuous_neg).measurable).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have hlog : |log t| = -log t := abs_of_nonpos (log_nonpos ht0.le ht.2)
      have h1 : -log t ≤ √(2 / t) := neg_log_le_sqrt_two_div ht0.le
      have h2 : exp (-t) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr ht0.le)
      rw [norm_eq_abs, abs_mul, hlog, abs_of_pos (exp_pos _)]
      calc -log t * exp (-t) ≤ √(2 / t) * 1 := mul_le_mul h1 h2 (exp_pos _).le (sqrt_nonneg _)
        _ = √2 * t ^ (-(1 / 2 : ℝ)) := by
            rw [mul_one, sqrt_div (by positivity), rpow_neg ht0.le, ← sqrt_eq_rpow, div_eq_mul_inv]
  have h1inf : IntegrableOn (fun t : ℝ ↦ log t * exp (-t)) (Ioi 1) := by
    have htail : IntegrableOn (fun t : ℝ ↦ exp (-t) * t) (Ioi 1) := by
      refine ((GammaIntegral_convergent (by norm_num : (0 : ℝ) < 2)).mono_set
        (Ioi_subset_Ioi zero_le_one)).congr_fun (fun t _ ↦ by norm_num) measurableSet_Ioi
    refine htail.mono' ?_ ?_
    · exact (measurable_log.mul
        (continuous_exp.comp continuous_neg).measurable).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_eq_abs, abs_mul, abs_of_pos (log_pos ht), abs_of_pos (exp_pos _)]
      calc log t * exp (-t) ≤ t * exp (-t) :=
            mul_le_mul_of_nonneg_right (log_le_self (zero_lt_one.trans ht).le) (exp_pos _).le
        _ = exp (-t) * t := mul_comm _ _
  simpa only [Ioc_union_Ioi_eq_Ioi zero_le_one] using h01.union h1inf

/-- Integration by parts on `[0, z]` relating `∫ t in 0..z, (1 - e^{-t}) / t` and
`∫ t in 0..z, log t * e^{-t}`. -/
theorem integral_one_sub_exp_neg_div_eq_sub_integral {z : ℝ} (hz : 0 ≤ z) :
    ∫ t in (0 : ℝ)..z, (1 - exp (-t)) / t =
      (1 - exp (-z)) * log z - ∫ t in (0 : ℝ)..z, log t * exp (-t) := by
  rcases hz.eq_or_lt with rfl | hz_pos
  · simp
  let f (t : ℝ) : ℝ := (1 - exp (-t)) * log t
  let f' (t : ℝ) : ℝ := exp (-t) * log t + (1 - exp (-t)) / t
  have hderiv : ∀ t ∈ Ioo 0 z, HasDerivAt f (f' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ ↦ 1 - exp (-s)) (exp (-t)) t := by
      simpa using ((hasDerivAt_neg t).exp).const_sub 1
    refine (h1.mul (hasDerivAt_log ht.1.ne')).congr_deriv ?_
    simp [f', div_eq_mul_inv]
  have hint1 : IntervalIntegrable (fun t : ℝ ↦ exp (-t) * log t) volume 0 z := by
    have hcongr : (fun t : ℝ ↦ exp (-t) * log t) = fun t ↦ log t * exp (-t) := by ext t; ring
    rw [hcongr, intervalIntegrable_iff_integrableOn_Ioc_of_le hz]
    exact integrableOn_Ioi_log_mul_exp_neg.mono_set Ioc_subset_Ioi_self
  have hint2 : IntervalIntegrable (fun t : ℝ ↦ (1 - exp (-t)) / t) volume 0 z :=
    intervalIntegrable_one_sub_exp_neg_div 0 z
  have hlim0 : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    have hratio : Tendsto (fun t : ℝ ↦ (1 - exp (-t)) / t) (𝓝[>] 0) (𝓝 1) := by
      have h1 := ((tendsto_exp_mul_sub_one_div (-1)).mono_left
        (nhdsWithin_mono _ (fun _ ht ↦ ne_of_gt (mem_Ioi.mp ht)))).neg
      rw [neg_neg] at h1
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t _
      rw [neg_one_mul]
      ring
    have htlog : Tendsto (fun t : ℝ ↦ t * log t) (𝓝[>] 0) (𝓝 0) := by
      simpa [mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero one_pos
    have hprod := hratio.mul htlog
    rw [one_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (t : ℝ) ≠ 0 := ne_of_gt (mem_Ioi.mp ht)
    simp only [f]
    field_simp [ht0]
  have hlimz : Tendsto f (𝓝[<] z) (𝓝 ((1 - exp (-z)) * log z)) :=
    (by fun_prop (disch := exact hz_pos.ne') : ContinuousAt f z).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hz_pos hderiv
    (hint1.add hint2) hlim0 hlimz
  rw [intervalIntegral.integral_add hint1 hint2, sub_zero] at hFTC
  have hcomm : (∫ t in (0 : ℝ)..z, exp (-t) * log t) = ∫ t in (0 : ℝ)..z, log t * exp (-t) :=
    intervalIntegral.integral_congr fun t _ ↦ mul_comm _ _
  linarith

/-- Integration by parts on `[1, b]` (`b > 0`) relating `∫ t in 1..b, exp (-t) / t` and
`∫ t in 1..b, log t * exp (-t)`. -/
theorem integral_exp_neg_div_eq_add_integral {b : ℝ} (hb : 0 < b) :
    ∫ t in (1 : ℝ)..b, exp (-t) / t =
      exp (-b) * log b + ∫ t in (1 : ℝ)..b, log t * exp (-t) := by
  let f (t : ℝ) : ℝ := -exp (-t) * log t
  let f' (t : ℝ) : ℝ := exp (-t) * log t - exp (-t) / t
  have hpos : ∀ t ∈ uIcc (1 : ℝ) b, 0 < t := fun t ht ↦ by
    rcases mem_uIcc.mp ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hderiv : ∀ t ∈ uIcc (1 : ℝ) b, HasDerivAt f (f' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ ↦ -exp (-s)) (exp (-t)) t := by
      simpa using ((hasDerivAt_neg t).exp).fun_neg
    refine (h1.mul (hasDerivAt_log (hpos t ht).ne')).congr_deriv ?_
    simp only [f', div_eq_mul_inv]
    ring
  have hint_log : IntervalIntegrable (fun t : ℝ ↦ log t * exp (-t)) volume 1 b := by
    rw [intervalIntegrable_iff]
    exact integrableOn_Ioi_log_mul_exp_neg.mono_set fun t ht ↦
      lt_of_lt_of_le (lt_min zero_lt_one hb) (uIoc_subset_uIcc ht).1
  have hint_exp : IntervalIntegrable (fun t : ℝ ↦ exp (-t) / t) volume 1 b :=
    intervalIntegrable_exp_neg_div zero_lt_one hb
  have hint_mul : IntervalIntegrable (fun t : ℝ ↦ exp (-t) * log t) volume 1 b := by
    simpa only [mul_comm] using hint_log
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint_mul.sub hint_exp)
  rw [intervalIntegral.integral_sub hint_mul hint_exp] at hFTC
  have hf1 : f 1 = 0 := by simp [f]
  have hcomm : (∫ t in (1 : ℝ)..b, exp (-t) * log t) = ∫ t in (1 : ℝ)..b, log t * exp (-t) :=
    intervalIntegral.integral_congr fun t _ ↦ mul_comm _ _
  dsimp only [f] at hFTC
  linarith

/-- For `a, b > 0`, `∫ t in a..b, (1 - e^{-t}) / t = log b - log a - ∫ t in a..b, e^{-t} / t`. -/
theorem integral_one_sub_exp_neg_div_eq_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in a..b, (1 - exp (-t)) / t =
      (log b - log a) - ∫ t in a..b, exp (-t) / t := by
  have hint1 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume a b :=
    intervalIntegrable_inv_iff.mpr (Or.inr fun h ↦ by
      rcases mem_uIcc.mp h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)
  have hint2 : IntervalIntegrable (fun t : ℝ ↦ exp (-t) / t) volume a b :=
    intervalIntegrable_exp_neg_div ha hb
  have hcongr : (fun t : ℝ ↦ (1 - exp (-t)) / t) = fun t : ℝ ↦ t⁻¹ - exp (-t) / t := by
    ext t
    by_cases ht : t = 0
    · simp [ht]
    · field_simp [ht]
  rw [hcongr, intervalIntegral.integral_sub hint1 hint2, integral_inv_of_pos ha hb,
    log_div hb.ne' ha.ne']

/-- For `a, b > 0`, `∫ u in a..b, e^u / u = log b - log a + ∫ u in a..b, (e^u - 1) / u`. -/
theorem integral_exp_div_eq_log_sub_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u in a..b, exp u / u =
      (log b - log a) + ∫ u in a..b, (exp u - 1) / u := by
  have hint1 : IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume a b :=
    intervalIntegrable_inv_iff.mpr (Or.inr fun h ↦ by
      rcases mem_uIcc.mp h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)
  have hint2 : IntervalIntegrable (fun u : ℝ ↦ (exp u - 1) / u) volume a b :=
    intervalIntegrable_exp_sub_one_div a b
  have hcongr : (fun u : ℝ ↦ exp u / u) = fun u : ℝ ↦ u⁻¹ + (exp u - 1) / u := by
    ext u
    by_cases hu : u = 0
    · simp [hu]
    · field_simp [hu]
      ring
  rw [hcongr, intervalIntegral.integral_add hint1 hint2, integral_inv_of_pos ha hb,
    log_div hb.ne' ha.ne']

/-- Reflection identity for `exp u / u`:
`∫ u in (-b)..(-a), exp u / u = -∫ t in a..b, exp (-t) / t`. -/
theorem integral_neg_exp_div (a b : ℝ) :
    ∫ u in (-b)..(-a), exp u / u = -∫ t in a..b, exp (-t) / t := by
  have hcomp := (intervalIntegral.integral_comp_neg
    (f := fun u : ℝ ↦ exp u / u) (a := a) (b := b)).symm
  have hneg : (fun t : ℝ ↦ exp (-t) / (-t)) = fun t : ℝ ↦ -(exp (-t) / t) := by
    ext t; ring
  rw [hcomp, hneg, intervalIntegral.integral_neg]

/-- The series `∑' n, y ^ (n + 1) / ((n + 1) * (n + 1)!)` is summable for every real `y`. -/
theorem summable_pow_div_mul_factorial (y : ℝ) :
    Summable fun n : ℕ ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  refine .of_norm_bounded ((summable_pow_div_factorial |y|).mul_left |y|) fun n ↦ ?_
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) * ((n + 1)! : ℝ) := by positivity
  rw [norm_eq_abs, abs_div, abs_of_pos hpos, ← pow_abs]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc |y| ^ (n + 1) / (((n : ℝ) + 1) * (((n : ℝ) + 1) * (n ! : ℝ)))
      ≤ |y| ^ (n + 1) / (1 * (1 * (n ! : ℝ))) := by
        gcongr <;> linarith
    _ = |y| * (|y| ^ n / (n ! : ℝ)) := by
        rw [pow_succ']
        ring

/-- The derivative of `z ↦ ∑' n, z ^ (n + 1) / ((n + 1) * (n + 1)!)` is
`Function.update (fun u : ℝ ↦ (e^u - 1) / u) 0 1 y`. -/
theorem hasDerivAt_tsum_pow_div_mul_factorial (y : ℝ) :
    HasDerivAt
      (fun z : ℝ ↦ ∑' n : ℕ, z ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
      (Function.update (fun u : ℝ ↦ (exp u - 1) / u) 0 1 y) y := by
  let R : ℝ := |y| + 1
  let g (n : ℕ) (z : ℝ) : ℝ := z ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))
  let g' (n : ℕ) (z : ℝ) : ℝ := z ^ n / ((n + 1)! : ℝ)
  have hg : ∀ n : ℕ, ∀ z ∈ Metric.ball (0 : ℝ) R, HasDerivAt (g n) (g' n z) z := by
    intro n z _
    have hpow := hasDerivAt_pow (n + 1) z
    refine (hpow.div_const (((n : ℝ) + 1) * ((n + 1)! : ℝ))).congr_deriv ?_
    dsimp only [g']
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp [hn1]
  have hg' : ∀ n : ℕ, ∀ z ∈ Metric.ball (0 : ℝ) R, ‖g' n z‖ ≤ R ^ n / (n ! : ℝ) := by
    intro n z hz
    rw [Metric.mem_ball, dist_eq, sub_zero] at hz
    have hfac : (n ! : ℝ) ≤ ((n + 1)! : ℝ) :=
      Nat.cast_le.mpr (Nat.factorial_le (Nat.le_succ n))
    rw [norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((n + 1)! : ℝ)), ← pow_abs]
    calc |z| ^ n / ((n + 1)! : ℝ) ≤ R ^ n / ((n + 1)! : ℝ) := by gcongr
      _ ≤ R ^ n / (n ! : ℝ) := by gcongr
  have hsum := hasDerivAt_tsum_of_isPreconnected (summable_pow_div_factorial R)
    Metric.isOpen_ball (convex_ball (0 : ℝ) R).isPreconnected hg hg'
    (Metric.mem_ball_self (by positivity : 0 < R))
    (by simp [g]) (Metric.mem_ball.mpr (by rw [dist_eq, sub_zero]; linarith))
  refine hsum.congr_deriv ?_
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [Function.update_self, g']
    rw [tsum_eq_single 0]
    · simp
    · intro n hn; simp [zero_pow hn]
  · simp only [Function.update_of_ne hy, g']
    exact Real.tsum_pow_div_factorial_succ hy

/-- Integrating `(e^u - 1) / u` from `0` to `y` gives the entire series
`∑' n, y ^ (n + 1) / ((n + 1) * (n + 1)!)`. -/
theorem integral_exp_sub_one_div_eq_tsum (y : ℝ) :
    ∫ u in (0 : ℝ)..y, (exp u - 1) / u =
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ hasDerivAt_tsum_pow_div_mul_factorial u)
    (continuous_update_exp_sub_one_div_zero.intervalIntegrable 0 y)
  have h0 : ∑' n : ℕ, (0 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) = 0 := by
    simp
  rw [h0, sub_zero] at hFTC
  rw [← hFTC]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [hne] with u hu _
  simp [hu]

/-- Integrating `(1 - e^{-t}) / t` from `0` to `z` gives
`-∑' n, (-z) ^ (n + 1) / ((n + 1) * (n + 1)!)`. -/
theorem integral_one_sub_exp_neg_div_eq (z : ℝ) :
    ∫ t in (0 : ℝ)..z, (1 - exp (-t)) / t =
      -∑' n : ℕ, (-z) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun u : ℝ ↦ (exp u - 1) / u) (a := (0 : ℝ)) (b := z)
  simp only [neg_zero] at hcomp
  have heq : (fun t : ℝ ↦ (exp (-t) - 1) / (-t)) = fun t : ℝ ↦ (1 - exp (-t)) / t := by
    ext t
    ring
  rw [heq, intervalIntegral.integral_symm 0 (-z)] at hcomp
  rw [hcomp, integral_exp_sub_one_div_eq_tsum (-z)]

end Real
