/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference

/-!
# Integral representations of the Euler–Mascheroni constant

This file complements `Mathlib.NumberTheory.Harmonic.GammaDeriv` (which proves
`γ = -∫ t in Ioi 0, log t * exp (-t)`) by establishing the split exponential-integral formula

```text
γ = ∫ t in 0..1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t
```

together with the underlying integrability, boundary-limit, and integration-by-parts identities for
`log t * exp (-t)` and `(1 - exp (-t)) / t`. These identities connect the Euler–Mascheroni constant
directly to the exponential integral and the unoffset logarithmic integral `Real.li`.

## Main results

* `Real.integrableOn_log_mul_exp_neg_Ioi`: `t ↦ log t * exp (-t)` is integrable on `(0, ∞)`.
* `Real.integrableOn_exp_neg_div_Ioi`: `t ↦ exp (-t) / t` is integrable on `(a, ∞)` for every
  `a > 0`.
* `Real.tendsto_log_mul_exp_neg_atTop`: `log t * exp (-t) → 0` as `t → ∞`.
* `Real.continuous_one_sub_exp_neg_mul_log`: `t ↦ (1 - exp (-t)) * log t` is continuous on `ℝ`.
* `Real.one_sub_exp_neg_mul_log_eq`: integration by parts on `[0, z]` for `z ≥ 0`.
* `Real.eulerMascheroniConstant_eq_integral_sub_integral`:
  `γ = ∫ t in 0..1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t`.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §5.9 (Gamma Function:
  Integral Representations) and §6.2.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace Real

/-- `t ↦ log t * exp (-t)` is integrable on `(0, ∞)`. -/
theorem integrableOn_log_mul_exp_neg_Ioi :
    IntegrableOn (fun t : ℝ ↦ log t * exp (-t)) (Ioi 0) := by
  have h := integrableOn_log_log_mul_rpow one_lt_two
  rw [← exp_zero, ← integrableOn_comp_exp_Ioi] at h
  refine h.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
  simp only [log_exp, smul_eq_mul, ← exp_mul]
  rw [mul_left_comm, ← exp_add]
  ring_nf

/-- `t ↦ exp (-t) / t` is integrable on `(a, ∞)` for every `a > 0`. -/
theorem integrableOn_exp_neg_div_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ exp (-t) / t) (Ioi a) := by
  refine Integrable.mono' (g := fun t : ℝ ↦ exp (-t) / a)
    ((integrableOn_exp_neg_Ioi a).div_const a)
    ((continuous_exp.comp continuous_neg).measurable.div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : a < t)
  rw [norm_eq_abs, abs_div, abs_of_pos (exp_pos _), abs_of_pos (ha.trans ht)]
  exact div_le_div_of_nonneg_left (exp_pos _).le ha ht.le

/-- `log t * exp (-t) → 0` as `t → ∞`. -/
theorem tendsto_log_mul_exp_neg_atTop :
    Tendsto (fun t : ℝ ↦ log t * exp (-t)) atTop (𝓝 0) := by
  have hle : Tendsto (fun t : ℝ ↦ exp (-t) * t) atTop (𝓝 0) := by
    simpa [rpow_neg_one, div_inv_eq_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-1 : ℝ)).tendsto_div_nhds_zero
  refine squeeze_zero_norm' (a := fun t ↦ exp (-t) * t) ?_ hle
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [norm_eq_abs, abs_mul, abs_of_nonneg (log_nonneg ht),
    abs_of_pos (exp_pos _), mul_comm (exp (-t)) t]
  exact mul_le_mul_of_nonneg_right (log_le_self (zero_le_one.trans ht)) (exp_pos _).le

/-- The function `t ↦ (1 - exp (-t)) * log t` is continuous on `ℝ` (taking the value `0` at
`t = 0`). -/
@[fun_prop]
theorem continuous_one_sub_exp_neg_mul_log :
    Continuous fun t : ℝ ↦ (1 - exp (-t)) * log t := by
  have heq : (fun t : ℝ ↦ (1 - exp (-t)) * log t) = fun t ↦ dslope exp 0 (-t) * (t * log t) := by
    ext t
    by_cases ht : t = 0
    · simp [ht]
    · rw [dslope_exp_zero_of_ne (neg_ne_zero.mpr ht)]
      field_simp [ht]
      ring
  rw [heq]
  exact (continuous_dslope_exp_zero.comp continuous_neg).mul continuous_mul_log

/-- Integration by parts for `∫ t in 0..z, (1 - exp (-t)) / t` at `z ≥ 0`. -/
theorem one_sub_exp_neg_mul_log_eq {z : ℝ} (hz : 0 ≤ z) :
    (1 - exp (-z)) * log z =
      (∫ t in Ioc 0 z, log t * exp (-t)) + ∫ t in (0 : ℝ)..z, (1 - exp (-t)) / t := by
  have hlog_int : IntervalIntegrable (fun t : ℝ ↦ log t * exp (-t)) volume 0 z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz).mpr
      (integrableOn_log_mul_exp_neg_Ioi.mono_set Ioc_subset_Ioi_self)
  have hsub_int : IntervalIntegrable (fun t : ℝ ↦ (1 - exp (-t)) / t) volume 0 z := by
    have heq : (fun t : ℝ ↦ (1 - exp (-t)) / t) = fun t : ℝ ↦ (exp (-t) - 1) / (-t) := by
      ext t
      rw [← neg_sub 1 (exp (-t)), neg_div_neg_eq]
    rw [heq]
    simpa only [neg_zero, neg_neg] using
      (IntervalIntegrable.iff_comp_neg (a := 0) (b := -z)).mp
        (intervalIntegrable_exp_sub_one_div 0 (-z))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz
    continuous_one_sub_exp_neg_mul_log.continuousOn
    (f' := fun t : ℝ ↦ log t * exp (-t) + (1 - exp (-t)) / t)
    (fun t ht ↦ by
      have hd1 : HasDerivAt (fun u : ℝ ↦ 1 - exp (-u)) (exp (-t)) t := by
        simpa using (hasDerivAt_neg t).exp.const_sub 1
      exact (hd1.mul (hasDerivAt_log ht.1.ne')).congr_deriv (by ring))
    (hlog_int.add hsub_int)
  rw [intervalIntegral.integral_add hlog_int hsub_int, intervalIntegral.integral_of_le hz,
    neg_zero, exp_zero, sub_self, zero_mul, sub_zero] at hFTC
  exact hFTC.symm

/-- **Integral representation of the Euler–Mascheroni constant**:
`γ = ∫ t in 0..1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t`. -/
theorem eulerMascheroniConstant_eq_integral_sub_integral :
    eulerMascheroniConstant =
      (∫ t in (0 : ℝ)..1, (1 - exp (-t)) / t) - ∫ t in Ioi (1 : ℝ), exp (-t) / t := by
  have h1 : (∫ t in (0 : ℝ)..1, (1 - exp (-t)) / t) =
      -(∫ t in Ioc 0 1, log t * exp (-t)) := by
    have h := one_sub_exp_neg_mul_log_eq zero_le_one
    rw [log_one, mul_zero] at h
    linarith
  have h2 : (∫ t in Ioi (1 : ℝ), exp (-t) / t) =
      ∫ t in Ioi (1 : ℝ), log t * exp (-t) := by
    have hint_log : IntegrableOn (fun t : ℝ ↦ log t * exp (-t)) (Ioi 1) :=
      integrableOn_log_mul_exp_neg_Ioi.mono_set (Ioi_subset_Ioi zero_le_one)
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := (1 : ℝ)) (f := fun t : ℝ ↦ -(exp (-t) * log t))
      (f' := fun t : ℝ ↦ log t * exp (-t) - exp (-t) / t) (m := 0)
      (fun t ht ↦ by
        have ht0 : 0 < t := zero_lt_one.trans_le ht
        have hd1 : HasDerivAt (fun u : ℝ ↦ exp (-u)) (-exp (-t)) t := by
          simpa using (hasDerivAt_neg t).exp
        exact ((hd1.mul (hasDerivAt_log ht0.ne')).neg).congr_deriv (by ring))
      (hint_log.sub (integrableOn_exp_neg_div_Ioi one_pos))
      (by simpa [mul_comm] using tendsto_log_mul_exp_neg_atTop.neg)
    rw [log_one, mul_zero, neg_zero, sub_zero,
      integral_sub hint_log (integrableOn_exp_neg_div_Ioi one_pos)] at hFTC
    linarith
  have hsplit : (∫ t in Ioi (0 : ℝ), log t * exp (-t)) =
      (∫ t in Ioc (0 : ℝ) 1, log t * exp (-t)) +
        ∫ t in Ioi (1 : ℝ), log t * exp (-t) := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (integrableOn_log_mul_exp_neg_Ioi.mono_set Ioc_subset_Ioi_self)
      (integrableOn_log_mul_exp_neg_Ioi.mono_set (Ioi_subset_Ioi zero_le_one)),
      Ioc_union_Ioi_eq_Ioi zero_le_one]
  rw [h1, h2, eulerMascheroniConstant_eq_neg_integral_log, hsplit]
  ring

end Real
