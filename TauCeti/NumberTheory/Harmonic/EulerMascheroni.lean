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
    exact (integral_exp_neg_div_eq_add_integral (zero_lt_one.trans_le hb)).symm
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
