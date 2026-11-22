/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference

/-!
# Exponential-integral tail integrability and logarithmic weight estimates

This file collects elementary integrability, boundary-decay, and integration-by-parts identities
for the exponential-integral kernel `exp u / u` and the Gamma-derivative kernel `log t * exp (-t)`
without depending on `Real.li` or `Real.eulerMascheroniConstant`:

* `t ↦ exp (-t) / t` is integrable on `(a, ∞)` for `a > 0`, and by reflection `u ↦ exp u / u` is
  integrable on `(-∞, y]` for `y < 0`.
* `t ↦ log t * exp (-t)` is integrable on `(0, ∞)` and tends to `0` as `t → ∞`.
* `t ↦ (1 - exp (-t)) * log t` is continuous on `ℝ` and gives the integration-by-parts identity
  `(1 - exp (-z)) * log z = ∫ t in Ioc 0 z, log t * exp (-t) + ∫ t in 0..z, (1 - exp (-t)) / t`
  for `z ≥ 0`.

## Main results

* `Real.integrableOn_log_mul_exp_neg_Ioi`: `t ↦ log t * exp (-t)` is integrable on `(0, ∞)`.
* `Real.integrableOn_exp_neg_div_Ioi`: `t ↦ exp (-t) / t` is integrable on `(a, ∞)` for `a > 0`.
* `Real.integrableOn_exp_div_Iic`: `u ↦ exp u / u` is integrable on `(-∞, y]` for `y < 0`.
* `Real.tendsto_log_mul_exp_neg_atTop`: `log t * exp (-t) → 0` as `t → ∞`.
* `Real.continuous_one_sub_exp_neg_mul_log`: `t ↦ (1 - exp (-t)) * log t` is continuous on `ℝ`.
* `Real.one_sub_exp_neg_mul_log_eq`: integration by parts on `[0, z]` for `z ≥ 0`.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §§5.9 and 6.2.
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

/-- `u ↦ exp u / u` is integrable on `(-∞, y]` whenever `y < 0`. -/
theorem integrableOn_exp_div_Iic {y : ℝ} (hy : y < 0) :
    IntegrableOn (fun u : ℝ ↦ exp u / u) (Iic y) := by
  have hcomp := (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
    (Homeomorph.neg ℝ).measurableEmbedding).mpr (integrableOn_exp_neg_div_Ioi (neg_pos.mpr hy))
  have hIio : IntegrableOn (fun u : ℝ ↦ exp u / u) (Iio y) := by
    simpa [Function.comp_def, div_neg] using hcomp.neg
  rw [integrableOn_Iic_iff_integrableOn_Iio]
  exact hIio

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

end Real
