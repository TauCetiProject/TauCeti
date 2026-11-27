/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.ExpIntegralSeries
import TauCeti.Analysis.SpecialFunctions.Exp.Limits
import TauCeti.Analysis.SpecialFunctions.Integrals.LogMulExpNeg

/-!
# Additional interval-integral identities for exponentials and `1 / t`

This file records interval-integral identities and integrability lemmas for `(1 - e^{-t}) / t`,
`e^{-t} / t`, and `e^u / u` complementing `TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference`,
`TauCeti.Analysis.SpecialFunctions.Exp.ExpIntegralSeries`, and
`TauCeti.Analysis.SpecialFunctions.Integrals.LogMulExpNeg`.

## Main declarations

* `Real.intervalIntegrable_one_sub_exp_neg_div`: `(1 - e^{-t}) / t` is interval integrable on
  `[a, b]`.
* `Real.intervalIntegrable_exp_neg_div`: `e^{-t} / t` is interval integrable on `[a, b]` for
  `0 < a`, `0 < b`.
* `Real.integral_exp_neg_div_eq_add_integral`: integration by parts relating
  `∫ t in 1..b, e^{-t} / t` and `∫ t in 1..b, log t * e^{-t}` for `b > 0`.
* `Real.integral_one_sub_exp_neg_div_eq_log_sub`: for `a, b > 0`,
  `∫ t in a..b, (1 - e^{-t}) / t = log b - log a - ∫ t in a..b, e^{-t} / t`.
* `Real.integral_exp_div_eq_log_sub_add`: for `a, b > 0`,
  `∫ u in a..b, e^u / u = log b - log a + ∫ u in a..b, (e^u - 1) / u`.
* `Real.integral_exp_neg_div_eq_neg_integral_exp_div`: reflection identity
  `∫ t in a..b, e^{-t} / t = -∫ u in (-b)..(-a), e^u / u`.
* `Real.integral_one_sub_exp_neg_div_eq_neg_tsum`:
  `∫ t in 0..z, (1 - e^{-t}) / t = -∑' n, (-z) ^ (n + 1) / ((n + 1) * (n + 1)!)`.
-/

public section

open Filter MeasureTheory Set
open scoped Nat Topology

namespace Real

/-- `(1 - e^{-t}) / t` is interval integrable on every interval `[a, b]`. -/
theorem intervalIntegrable_one_sub_exp_neg_div (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ (1 - exp (-t)) / t) volume a b := by
  refine (continuous_update_one_sub_exp_neg_div_zero.intervalIntegrable a b).congr_ae ?_
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht
  simp [ht]

/-- `e^{-t} / t` is interval integrable between any two positive endpoints `a, b > 0`. -/
theorem intervalIntegrable_exp_neg_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ ↦ exp (-t) / t) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  exact (continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
    fun t ht h ↦ notMem_uIcc_of_lt ha hb (h ▸ ht)

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
    exact TauCeti.integrableOn_log_mul_exp_neg_Ioi.mono_set fun t ht ↦
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
    intervalIntegrable_inv_iff.mpr (Or.inr (notMem_uIcc_of_lt ha hb))
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
    intervalIntegrable_inv_iff.mpr (Or.inr (notMem_uIcc_of_lt ha hb))
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

/-- Reflection identity for `exp (-t) / t`:
`∫ t in a..b, exp (-t) / t = -∫ u in (-b)..(-a), exp u / u`. -/
theorem integral_exp_neg_div_eq_neg_integral_exp_div (a b : ℝ) :
    ∫ t in a..b, exp (-t) / t = -∫ u in (-b)..(-a), exp u / u := by
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun u : ℝ ↦ exp u / u) (a := a) (b := b)
  have hneg : (fun t : ℝ ↦ exp (-t) / (-t)) = fun t : ℝ ↦ -(exp (-t) / t) := by
    ext t; ring
  rw [hneg, intervalIntegral.integral_neg] at hcomp
  linarith

/-- Integrating `(1 - e^{-t}) / t` from `0` to `z` gives
`-∑' n, (-z) ^ (n + 1) / ((n + 1) * (n + 1)!)`. -/
theorem integral_one_sub_exp_neg_div_eq_neg_tsum (z : ℝ) :
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
