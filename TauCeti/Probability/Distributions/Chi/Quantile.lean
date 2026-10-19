/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Chi.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Quantile
import TauCeti.Probability.Quantile.Map

/-!
# Quantiles of chi laws

Interior chi quantiles are scaled square roots of chi-squared quantiles, hence are expressed
using the inverse regularized Gamma function. Their endpoint limits are zero and positive
infinity at positive degrees; the degree-zero law has constant zero quantiles.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  second edition, Wiley, 1994, chapter 18.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {k s u : ℝ}

/-- The chi quantile is the scaled square root of twice the inverse regularized Gamma function,
including the zero-degree boundary. -/
@[simp]
theorem quantile_chiMeasure (hk : 0 ≤ k) (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (chiMeasure k s).quantile u = s * √(2 * inverseRegularizedGamma (k / 2) u) := by
  let _ := isProbabilityMeasure_chiSquaredMeasure hk
  rw [chiMeasure_of_scale_pos hs, Measure.quantile_map_of_monotone
    (fun x y hxy ↦ mul_le_mul_of_nonneg_left (sqrt_le_sqrt hxy) hs.le)
    (by fun_prop) hu.1 hu.2, quantile_chiSquaredMeasure hk hu]

/-- Every valid chi law has lower quantile endpoint zero. -/
theorem tendsto_quantile_chiMeasure_nhdsGT_zero (hk : 0 ≤ k) (hs : 0 < s) :
    Tendsto (fun u ↦ ((chiMeasure k s).quantile u : EReal)) (𝓝[>] 0) (𝓝 0) := by
  rcases hk.eq_or_lt' with rfl | hk
  · apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    simp [quantile_chiMeasure le_rfl hs hu]
  · have hlim := (((tendsto_inverseRegularizedGamma_nhdsGT_zero (half_pos hk)).mono_right
        inf_le_left).const_mul 2).sqrt.const_mul s
    simp only [mul_zero, sqrt_zero] at hlim
    apply (EReal.tendsto_coe.2 hlim).congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_chiMeasure hk.le hs hu).symm

/-- Positive-degree chi quantiles tend to infinity as the level tends to one; at degree zero
these quantiles remain zero. -/
theorem tendsto_quantile_chiMeasure_nhdsLT_one (hk : 0 ≤ k) (hs : 0 < s) :
    Tendsto (fun u ↦ ((chiMeasure k s).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if k = 0 then 0 else ⊤)) := by
  rcases hk.eq_or_lt' with rfl | hk
  · apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    simp [quantile_chiMeasure le_rfl hs hu]
  · rw [ite_eq_right hk.ne', EReal.tendsto_coe_nhds_top_iff]
    have hlim := (tendsto_sqrt_atTop.comp
      ((tendsto_inverseRegularizedGamma_nhdsLT_one (half_pos hk)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2))).const_mul_atTop hs
    apply hlim.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    exact (quantile_chiMeasure hk.le hs hu).symm

end TauCeti.Probability
