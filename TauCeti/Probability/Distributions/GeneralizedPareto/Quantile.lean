/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedPareto.Cdf
public import TauCeti.Probability.Distributions.Exponential.Quantile
public import TauCeti.Probability.Quantile.Map
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of generalized Pareto laws

For positive scale `s`, the generalized Pareto quantile at an interior level `u` is
`-s * log (1 - u)` at shape zero and
`s * ((1 - u) ^ (-ξ) - 1) / ξ` at nonzero shape `ξ`.

The endpoint limits recover the lower support endpoint zero. At the upper endpoint they give
positive infinity for nonnegative shape and the finite endpoint `-s / ξ` for negative shape.

## Main results

* `TauCeti.Probability.quantile_generalizedParetoMeasure` gives the explicit quantile formula.
* `TauCeti.Probability.tendsto_quantile_generalizedParetoMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_generalizedParetoMeasure_nhdsLT_one` give its endpoint
  limits.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 4.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {s ξ u : ℝ}

/-- The quantile of a positive-scale generalized Pareto law at an interior probability level. -/
theorem quantile_generalizedParetoMeasure (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (generalizedParetoMeasure s ξ).quantile u =
      if ξ = 0 then -s * log (1 - u) else s * ((1 - u) ^ (-ξ) - 1) / ξ := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  rw [generalizedParetoMeasure_of_pos hs,
    Measure.quantile_map_of_monotone (strictMono_generalizedParetoMap hs ξ).monotone
      (continuous_generalizedParetoMap s ξ) hu.1 hu.2,
    quantile_expMeasure one_pos hu]
  by_cases hξ : ξ = 0
  · simp [hξ]
  rw [ite_eq_right hξ, generalizedParetoMap_of_shape_ne_zero hξ]
  have hu1 : 0 < 1 - u := sub_pos.mpr hu.2
  rw [Real.rpow_def_of_pos hu1]
  congr 2
  ring_nf

/-- Generalized Pareto quantiles tend to the lower support endpoint zero as the level tends to
zero from above. -/
theorem tendsto_quantile_generalizedParetoMeasure_nhdsGT_zero (hs : 0 < s) (ξ : ℝ) :
    Tendsto (fun u ↦ ((generalizedParetoMeasure s ξ).quantile u : EReal))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  have hbase : Tendsto (fun u ↦ (expMeasure 1).quantile u)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    EReal.tendsto_coe.1 (tendsto_quantile_expMeasure_nhdsGT_zero one_pos)
  have hlim : Tendsto
      (generalizedParetoMap s ξ ∘ fun u ↦ (expMeasure 1).quantile u)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [generalizedParetoMap_zero_right] using
      ((continuous_generalizedParetoMap s ξ).tendsto 0).comp hbase
  rw [generalizedParetoMeasure_of_pos hs]
  apply (EReal.tendsto_coe.2 hlim).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  simp only [Function.comp_apply]
  rw [Measure.quantile_map_of_monotone (strictMono_generalizedParetoMap hs ξ).monotone
    (continuous_generalizedParetoMap s ξ) hu.1 hu.2]

/-- For negative shape, generalized Pareto quantiles tend to the finite upper support endpoint
`-s / ξ` as the level tends to one from below. -/
private theorem tendsto_quantile_generalizedParetoMeasure_nhdsLT_one_of_neg
    (hs : 0 < s) (hξ : ξ < 0) :
    Tendsto (fun u ↦ ((generalizedParetoMeasure s ξ).quantile u : EReal))
      (nhdsWithin 1 (Iio 1)) (nhds ((-s / ξ : ℝ) : EReal)) := by
  have hpow : Tendsto (fun u : ℝ ↦ (1 - u) ^ (-ξ))
      (nhdsWithin 1 (Iio 1)) (nhds 0) := by
    have hsub : Tendsto (fun u : ℝ ↦ 1 - u) (nhdsWithin 1 (Iio 1)) (nhds 0) := by
      have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ))
          (nhdsWithin 1 (Iio 1)) (nhds 1) := tendsto_const_nhds
      simpa using hone.sub continuousWithinAt_id.tendsto
    exact hsub.rpow_const_nhds_zero (neg_pos.mpr hξ)
  have hlim : Tendsto (fun u : ℝ ↦ s * ((1 - u) ^ (-ξ) - 1) / ξ)
      (nhdsWithin 1 (Iio 1)) (nhds (-s / ξ)) := by
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ))
        (nhdsWithin 1 (Iio 1)) (nhds 1) := tendsto_const_nhds
    convert ((hpow.sub hone).const_mul s).div_const ξ using 1
    ring_nf
  apply (EReal.tendsto_coe.2 hlim).congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  norm_cast
  rw [quantile_generalizedParetoMeasure hs hu, ite_eq_right hξ.ne]

/-- For nonnegative shape, generalized Pareto quantiles tend to positive infinity as the level
tends to one from below. -/
private theorem tendsto_quantile_generalizedParetoMeasure_nhdsLT_one_of_nonneg (hs : 0 < s)
    (hξ : 0 ≤ ξ) :
    Tendsto (fun u ↦ ((generalizedParetoMeasure s ξ).quantile u : EReal))
      (nhdsWithin 1 (Iio 1)) (nhds ⊤) := by
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  apply EReal.tendsto_coe_nhds_top_iff.2
  refine tendsto_atTop.2 fun b ↦ ?_
  have hb : cdf (generalizedParetoMeasure s ξ) b < 1 := by
    rw [cdf_generalizedParetoMeasure_eq hs ξ b]
    split_ifs with hb0 hξ0 hbase
    · norm_num
    · linarith [exp_pos (-b / s)]
    · linarith [Real.rpow_pos_of_pos hbase (-1 / ξ)]
    · have hξ' : 0 < ξ := lt_of_le_of_ne hξ (Ne.symm hξ0)
      have hb' : 0 ≤ b := not_lt.mp hb0
      have : 0 ≤ ξ * b / s := div_nonneg (mul_nonneg hξ'.le hb') hs.le
      linarith
  filter_upwards [Ioo_mem_nhdsLT hb] with u hu
  exact ((Measure.lt_quantile_iff _ ((cdf_nonneg _ b).trans_lt hu.1) hu.2).2 hu.1).le

/-- Generalized Pareto quantiles tend at the upper endpoint to `-s / ξ` for negative shape
and to positive infinity for nonnegative shape. -/
theorem tendsto_quantile_generalizedParetoMeasure_nhdsLT_one (hs : 0 < s) (ξ : ℝ) :
    Tendsto (fun u ↦ ((generalizedParetoMeasure s ξ).quantile u : EReal))
      (nhdsWithin 1 (Iio 1))
      (nhds (if ξ < 0 then ((-s / ξ : ℝ) : EReal) else ⊤)) := by
  by_cases hξ : ξ < 0
  · rw [ite_eq_left hξ]
    exact tendsto_quantile_generalizedParetoMeasure_nhdsLT_one_of_neg hs hξ
  · rw [ite_eq_right hξ]
    exact tendsto_quantile_generalizedParetoMeasure_nhdsLT_one_of_nonneg hs (not_lt.mp hξ)

end TauCeti.Probability
