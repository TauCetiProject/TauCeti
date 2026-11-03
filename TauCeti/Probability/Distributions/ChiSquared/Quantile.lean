/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.Gamma.Quantile
public import TauCeti.Probability.Quantile.Map
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of chi-squared laws

For nonnegative degrees of freedom `k` and an interior level `u`, the chi-squared quantile is
`2 * inverseRegularizedGamma (k / 2) u`. This includes the zero-degree law, which is the Dirac
mass at zero.

The one-sided endpoint limits are stated in `EReal`. Every nonnegative-degree law has lower
endpoint zero. At the upper endpoint, a positive-degree law is unbounded, while the zero-degree
law remains at zero.

Scaling by a nonnegative factor `c` multiplies the quantile by `c`. The scaled laws are the
diagonal laws of Wishart matrices; their upper endpoint limit is infinite unless the factor or
the degree vanishes, when the law is the Dirac mass at zero.

## Main results

* `TauCeti.Probability.quantile_chiSquaredMeasure` gives the quantile formula, including the
  zero-degree boundary;
* `TauCeti.Probability.tendsto_quantile_chiSquaredMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_chiSquaredMeasure_nhdsLT_one` give the endpoint limits;
* `TauCeti.Probability.quantile_map_const_mul_chiSquaredMeasure` gives the quantile of a scaled
  chi-squared law.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {c k u : ℝ}

/-- The quantile of a chi-squared law with nonnegative degrees of freedom, including the
zero-degree Dirac boundary. -/
@[simp]
theorem quantile_chiSquaredMeasure (hk : 0 ≤ k) (hu : u ∈ Ioo 0 1) :
    (chiSquaredMeasure k).quantile u = 2 * inverseRegularizedGamma (k / 2) u := by
  rcases hk.eq_or_lt' with rfl | hk
  · rw [chiSquaredMeasure_zero, Measure.quantile_dirac 0 hu.1 hu.2.le]
    simp
  · rw [chiSquaredMeasure_eq_gammaMeasure hk,
      quantile_gammaMeasure (half_pos hk) one_half_pos hu]
    ring

/-- Chi-squared quantiles approach the lower support endpoint zero as the level tends to zero
from above, including at zero degrees of freedom. -/
theorem tendsto_quantile_chiSquaredMeasure_nhdsGT_zero (hk : 0 ≤ k) :
    Tendsto (fun u ↦ ((chiSquaredMeasure k).quantile u : EReal))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rcases hk.eq_or_lt' with rfl | hk
  · apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    rw [chiSquaredMeasure_zero, Measure.quantile_dirac 0 hu.1 hu.2.le]
    norm_num
  · rw [chiSquaredMeasure_eq_gammaMeasure hk]
    exact EReal.tendsto_coe.2
      ((tendsto_quantile_gammaMeasure_nhdsGT_zero (half_pos hk) one_half_pos).mono_right
        inf_le_left)

/-- At positive degrees of freedom, chi-squared quantiles tend to positive infinity as the level
tends to one from below; at zero degrees of freedom they remain at zero. -/
theorem tendsto_quantile_chiSquaredMeasure_nhdsLT_one (hk : 0 ≤ k) :
    Tendsto (fun u ↦ ((chiSquaredMeasure k).quantile u : EReal))
      (nhdsWithin 1 (Iio 1)) (nhds (if k = 0 then 0 else ⊤)) := by
  rcases hk.eq_or_lt' with rfl | hk
  · rw [ite_eq_left rfl]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    rw [chiSquaredMeasure_zero, Measure.quantile_dirac 0 hu.1 hu.2.le]
    norm_num
  · rw [ite_eq_right hk.ne', chiSquaredMeasure_eq_gammaMeasure hk,
      EReal.tendsto_coe_nhds_top_iff]
    exact tendsto_quantile_gammaMeasure_nhdsLT_one (half_pos hk) one_half_pos

/-- The quantile of a chi-squared law scaled by a nonnegative factor, including the Dirac
boundaries at zero factor and at zero degrees of freedom. -/
@[simp]
theorem quantile_map_const_mul_chiSquaredMeasure (hc : 0 ≤ c) (hk : 0 ≤ k) (hu : u ∈ Ioo 0 1) :
    ((chiSquaredMeasure k).map (c * ·)).quantile u =
      c * (2 * inverseRegularizedGamma (k / 2) u) := by
  have := isProbabilityMeasure_chiSquaredMeasure hk
  rw [Measure.quantile_map_const_mul hc hu.1 hu.2, quantile_chiSquaredMeasure hk hu]

/-- Quantiles of a chi-squared law scaled by a nonnegative factor tend to zero as the level
tends to zero from above. -/
theorem tendsto_quantile_map_const_mul_chiSquaredMeasure_nhdsGT_zero (hc : 0 ≤ c)
    (hk : 0 ≤ k) :
    Tendsto (fun u ↦ (((chiSquaredMeasure k).map (c * ·)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 0) := by
  have h := (EReal.tendsto_coe.1 (tendsto_quantile_chiSquaredMeasure_nhdsGT_zero hk)).const_mul c
  rw [mul_zero] at h
  refine (EReal.tendsto_coe.2 h).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  rw [quantile_map_const_mul_chiSquaredMeasure hc hk hu, quantile_chiSquaredMeasure hk hu]

/-- Quantiles of a chi-squared law scaled by a nonnegative factor tend to positive infinity as
the level tends to one from below, unless the factor or the degree vanishes, when they remain at
zero. -/
theorem tendsto_quantile_map_const_mul_chiSquaredMeasure_nhdsLT_one (hc : 0 ≤ c)
    (hk : 0 ≤ k) :
    Tendsto (fun u ↦ (((chiSquaredMeasure k).map (c * ·)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if c = 0 ∨ k = 0 then 0 else ⊤)) := by
  by_cases h0 : c = 0 ∨ k = 0
  · rw [ite_eq_left h0]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    rw [quantile_map_const_mul_chiSquaredMeasure hc hk hu]
    rcases h0 with rfl | rfl <;> simp
  · rw [ite_eq_right h0]
    push Not at h0
    have hk' : k ≠ 0 := h0.2
    have h := tendsto_quantile_chiSquaredMeasure_nhdsLT_one hk
    rw [ite_eq_right hk', EReal.tendsto_coe_nhds_top_iff] at h
    refine EReal.tendsto_coe_nhds_top_iff.2
      ((h.const_mul_atTop (lt_of_le_of_ne hc (Ne.symm h0.1))).congr' ?_)
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    rw [quantile_map_const_mul_chiSquaredMeasure hc hk hu, quantile_chiSquaredMeasure hk hu]

end TauCeti.Probability
