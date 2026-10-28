/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
public import TauCeti.Probability.Distributions.Pareto.Basic
public import TauCeti.Probability.Quantile

/-!
# Quantiles of the Pareto distribution

For positive threshold `t` and shape `r`, the Pareto quantile at an interior level `u` is
`t * (1 - u) ^ (-1 / r)`. This formula inverts the Pareto cdf and describes its unbounded
right tail. The quantile tends to the lower support endpoint `t` as the level tends to zero,
and tends to infinity as the level tends to one.

## Main results

* `TauCeti.Probability.quantile_paretoMeasure` gives the quantile formula.
* `TauCeti.Probability.tendsto_quantile_paretoMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_paretoMeasure_nhdsLT_one` give the endpoint limits.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  Chapter 20.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {t r u : ℝ}

/-- The Pareto quantile at an interior level is `t * (1 - u) ^ (-1 / r)`. -/
theorem quantile_paretoMeasure (ht : 0 < t) (hr : 0 < r) (hu : u ∈ Ioo 0 1) :
    (paretoMeasure t r).quantile u = t * (1 - u) ^ (-1 / r) := by
  have hy : 0 < 1 - u := sub_pos.mpr hu.2
  have he : -1 / r = (-r)⁻¹ := by simp [neg_div]
  have hge : t ≤ t * (1 - u) ^ (-1 / r) :=
    le_mul_of_one_le_right ht.le
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy (by linarith [hu.1])
        (le_of_lt (div_neg_of_neg_of_pos (by norm_num) hr)))
  refine eq_of_forall_ge_iff fun x => ?_
  rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_paretoMeasure_eq ht hr]
  by_cases hx : x < t
  · simp only [ite_eq_left hx]
    exact iff_of_false (not_le.mpr hu.1) (not_le.mpr (hx.trans_le hge))
  · have hx0 : 0 < x := ht.trans_le (le_of_not_gt hx)
    rw [ite_eq_right hx, he, ← le_div_iff₀' ht,
      Real.rpow_inv_le_iff_of_neg hy (div_pos hx0 ht) (neg_neg_of_pos hr),
      Real.rpow_neg_eq_inv_rpow, inv_div]
    constructor <;> intro h <;> linarith

/-- Pareto quantiles approach the threshold as the level tends to zero from above. -/
theorem tendsto_quantile_paretoMeasure_nhdsGT_zero (ht : 0 < t) (hr : 0 < r) :
    Tendsto (fun u ↦ ((paretoMeasure t r).quantile u : EReal)) (𝓝[>] 0) (𝓝 (t : EReal)) := by
  rw [EReal.tendsto_coe]
  have hcont : ContinuousAt (fun u : ℝ ↦ t * (1 - u) ^ (-1 / r)) 0 := by
    exact continuousAt_const.mul
      ((continuousAt_const.sub continuousAt_id).rpow_const (by norm_num))
  have hlim : Tendsto (fun u : ℝ ↦ t * (1 - u) ^ (-1 / r)) (𝓝[>] 0) (𝓝 t) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact (quantile_paretoMeasure ht hr hu).symm

/-- Pareto quantiles tend to infinity as the level tends to one from below. -/
theorem tendsto_quantile_paretoMeasure_nhdsLT_one (ht : 0 < t) (hr : 0 < r) :
    Tendsto (fun u ↦ ((paretoMeasure t r).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) := by
  rw [EReal.tendsto_coe_nhds_top_iff]
  have hsub : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[<] 1) (𝓝[>] 0) := by
    simpa only [Tendsto, Filter.map_subLeft_nhdsLT, sub_self] using
      (le_refl (𝓝[>] (0 : ℝ)))
  have hlim : Tendsto (fun u : ℝ ↦ t * (1 - u) ^ (-1 / r)) (𝓝[<] 1) atTop :=
    ((tendsto_rpow_neg_nhdsGT_zero
      (div_neg_of_neg_of_pos (by norm_num) hr)).comp hsub).const_mul_atTop ht
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_paretoMeasure ht hr hu).symm

end TauCeti.Probability
