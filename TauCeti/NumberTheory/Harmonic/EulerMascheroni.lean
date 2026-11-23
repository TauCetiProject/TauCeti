/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import TauCeti.Analysis.SpecialFunctions.Exp.Integrals
import TauCeti.Analysis.SpecialFunctions.Exp.Limits

/-!
# Integral representations of the Euler–Mascheroni constant

This file records the classical exponential-integral identity for Euler's constant `γ`.

## Main declarations

* `Real.eulerMascheroniConstant_eq_integral_sub_integral`:
  `γ = ∫ t in 0..1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t`.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace Real

/-- Integration by parts on `[1, b]` relating `∫ t in 1..b, exp (-t) / t` and
`∫ t in 1..b, log t * exp (-t)`. -/
private theorem integral_exp_neg_div_eq_add_integral {b : ℝ} (hb : 1 ≤ b) :
    ∫ t in (1 : ℝ)..b, exp (-t) / t =
      exp (-b) * log b + ∫ t in (1 : ℝ)..b, log t * exp (-t) := by
  let f (t : ℝ) : ℝ := -exp (-t) * log t
  let f' (t : ℝ) : ℝ := exp (-t) * log t - exp (-t) / t
  have hderiv : ∀ t ∈ uIcc (1 : ℝ) b, HasDerivAt f (f' t) t := by
    intro t ht
    rw [uIcc_of_le hb] at ht
    have h1 : HasDerivAt (fun s : ℝ ↦ -exp (-s)) (exp (-t)) t := by
      simpa using ((hasDerivAt_neg t).exp).fun_neg
    refine (h1.mul (hasDerivAt_log (zero_lt_one.trans_le ht.1).ne')).congr_deriv ?_
    simp only [f', div_eq_mul_inv]
    ring
  have hint_log : IntervalIntegrable (fun t : ℝ ↦ log t * exp (-t)) volume 1 b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
    exact integrableOn_Ioi_log_mul_exp_neg.mono_set
      (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one))
  have hint_exp : IntervalIntegrable (fun t : ℝ ↦ exp (-t) / t) volume 1 b :=
    intervalIntegrable_exp_neg_div zero_lt_one (zero_lt_one.trans_le hb)
  have hint_mul : IntervalIntegrable (fun t : ℝ ↦ exp (-t) * log t) volume 1 b := by
    simpa only [mul_comm] using hint_log
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint_mul.sub hint_exp)
  rw [intervalIntegral.integral_sub hint_mul hint_exp] at hFTC
  have hf1 : f 1 = 0 := by simp [f]
  have hcomm : (∫ t in (1 : ℝ)..b, exp (-t) * log t) = ∫ t in (1 : ℝ)..b, log t * exp (-t) :=
    intervalIntegral.integral_congr fun t _ ↦ mul_comm _ _
  dsimp only [f] at hFTC
  linarith

/-- **Integral formula for Euler's constant**:
`γ = ∫ t in 0..1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t`. -/
theorem eulerMascheroniConstant_eq_integral_sub_integral :
    eulerMascheroniConstant =
      (∫ t in (0 : ℝ)..1, (1 - exp (-t)) / t) -
        ∫ t in Ioi (1 : ℝ), exp (-t) / t := by
  have h01 := integral_one_sub_exp_neg_div_eq_sub_integral (z := 1) zero_le_one
  simp only [log_one, mul_zero, zero_sub] at h01
  have htend_exp : Tendsto (fun b : ℝ ↦ ∫ t in (1 : ℝ)..b, exp (-t) / t) atTop
      (𝓝 (∫ t in Ioi (1 : ℝ), exp (-t) / t)) :=
    intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_Ioi_exp_neg_div zero_lt_one) tendsto_id
  have hint_Ioi1 : IntegrableOn (fun t : ℝ ↦ log t * exp (-t)) (Ioi 1) :=
    integrableOn_Ioi_log_mul_exp_neg.mono_set (Ioi_subset_Ioi zero_le_one)
  have htend_log : Tendsto (fun b : ℝ ↦ ∫ t in (1 : ℝ)..b, log t * exp (-t)) atTop
      (𝓝 (∫ t in Ioi (1 : ℝ), log t * exp (-t))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hint_Ioi1 tendsto_id
  have heq_Ioi1 : (∫ t in Ioi (1 : ℝ), exp (-t) / t) =
      ∫ t in Ioi (1 : ℝ), log t * exp (-t) := by
    refine tendsto_nhds_unique htend_exp ?_
    have hsum := tendsto_exp_neg_mul_log_atTop.add htend_log
    rw [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
    exact (integral_exp_neg_div_eq_add_integral hb).symm
  have hunion : (∫ t in Ioc (0 : ℝ) 1, log t * exp (-t)) +
      ∫ t in Ioi (1 : ℝ), log t * exp (-t) =
        ∫ t in Ioi (0 : ℝ), log t * exp (-t) := by
    have h01_int : IntegrableOn (fun t : ℝ ↦ log t * exp (-t)) (Ioc 0 1) :=
      integrableOn_Ioi_log_mul_exp_neg.mono_set Ioc_subset_Ioi_self
    rw [← MeasureTheory.setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h01_int hint_Ioi1,
      Ioc_union_Ioi_eq_Ioi zero_le_one]
  rw [h01, heq_Ioi1, intervalIntegral.integral_of_le zero_le_one,
    eulerMascheroniConstant_eq_neg_integral_log]
  linarith

end Real
