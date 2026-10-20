/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Weibull.Basic
public import TauCeti.Probability.Quantile
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of Weibull laws

For positive shape `k` and scale `s`, the Weibull quantile at an interior level `u` is
`s * (-log (1 - u)) ^ (1 / k)`. This explicit inverse of the cdf gives the thresholds
corresponding to prescribed cumulative probabilities.

The one-sided limits in `EReal` are the support endpoints `0` and `⊤`. These limits
concern interior levels, independently of the totalized quantile values at `0` and `1`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), chapter on Weibull distributions.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {k s : ℝ}

/-- The quantile of a Weibull law with positive shape and scale. -/
theorem quantile_weibullMeasure (hk : 0 < k) (hs : 0 < s) {u : ℝ}
    (hu : u ∈ Ioo 0 1) :
    (weibullMeasure k s).quantile u = s * (-log (1 - u)) ^ (1 / k) := by
  have hlog : 0 < -log (1 - u) :=
    neg_pos.mpr (log_neg (sub_pos.mpr hu.2) (by linarith [hu.1]))
  have hq : 0 < s * (-log (1 - u)) ^ (1 / k) :=
    mul_pos hs (rpow_pos_of_pos hlog _)
  let := isProbabilityMeasure_weibullMeasure hk hs
  refine eq_of_forall_ge_iff fun x ↦ ?_
  rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_weibullMeasure_eq hk hs]
  by_cases hx : x ≤ 0
  · simp only [ite_eq_left hx, not_le.mpr hu.1, not_le.mpr (hx.trans_lt hq)]
  · rw [ite_eq_right hx]
    have hxpos : 0 < x / s := div_pos (lt_of_not_ge hx) hs
    calc
      u ≤ 1 - exp (-(x / s) ^ k) ↔ exp (-(x / s) ^ k) ≤ 1 - u := le_sub_comm
      _ ↔ -(x / s) ^ k ≤ log (1 - u) :=
        (le_log_iff_exp_le (sub_pos.mpr hu.2)).symm
      _ ↔ -log (1 - u) ≤ (x / s) ^ k := by
        constructor <;> intro h <;> linarith
      _ ↔ (-log (1 - u)) ^ (1 / k) ≤ x / s := by
        rw [one_div, rpow_inv_le_iff_of_pos hlog.le hxpos.le hk]
      _ ↔ s * (-log (1 - u)) ^ (1 / k) ≤ x := by
        rw [le_div_iff₀ hs, mul_comm]

/-- Weibull quantiles tend to the lower support endpoint `0` as the level tends to `0`
from above. -/
theorem tendsto_quantile_weibullMeasure_nhdsGT_zero (hk : 0 < k) (hs : 0 < s) :
    Tendsto (fun u ↦ ((weibullMeasure k s).quantile u : EReal)) (𝓝[>] 0) (𝓝 0) := by
  have hlog : Tendsto (fun u : ℝ ↦ -log (1 - u)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (((tendsto_const_nhds.sub continuousWithinAt_id.tendsto).log
      (by norm_num)).neg :
      Tendsto (fun u : ℝ ↦ -log (1 - u)) (𝓝[>] 0) (𝓝 (-log (1 - 0))))
  have hlim : Tendsto (fun u : ℝ ↦ s * (-log (1 - u)) ^ (1 / k))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (hlog.rpow_const_nhds_zero (one_div_pos.mpr hk)).const_mul s
  apply (EReal.tendsto_coe.2 hlim).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_weibullMeasure hk hs hu).symm

/-- Weibull quantiles tend to plus infinity as the level tends to `1` from below. -/
theorem tendsto_quantile_weibullMeasure_nhdsLT_one (hk : 0 < k) (hs : 0 < s) :
    Tendsto (fun u ↦ ((weibullMeasure k s).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) := by
  let := isProbabilityMeasure_weibullMeasure hk hs
  apply EReal.tendsto_coe_nhds_top_iff.2
  refine tendsto_atTop.2 fun b ↦ ?_
  have hb : cdf (weibullMeasure k s) b < 1 := by
    rw [cdf_weibullMeasure_eq hk hs]
    split_ifs <;> linarith [exp_pos (-(b / s) ^ k)]
  filter_upwards [Ioo_mem_nhdsLT hb] with u hu
  exact ((Measure.lt_quantile_iff _
    ((cdf_nonneg (weibullMeasure k s) b).trans_lt hu.1) hu.2).2 hu.1).le

end TauCeti.Probability
