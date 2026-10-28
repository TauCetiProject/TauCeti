/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Basic
public import TauCeti.Probability.Quantile

/-!
# Quantiles of interval-uniform laws

This file computes the lower quantile of the uniform probability measure on a nondegenerate real
interval. At an interior probability level `u`, the quantile is the affine interpolation
`a + (b - a) * u`. Consequently the quantiles tend to the two interval endpoints as the level
tends to zero from above or to one from below.

## Main results

* `TauCeti.Probability.quantile_uniformMeasure` gives the explicit quantile formula;
* `TauCeti.Probability.tendsto_quantile_uniformMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_uniformMeasure_nhdsLT_one` give its endpoint limits.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {a b u : ℝ}

/-- The lower quantile of the uniform probability measure on `Set.Ioc a b` is affine
interpolation between the endpoints. -/
@[simp]
theorem quantile_uniformMeasure (hab : a < b) (hu : u ∈ Ioo 0 1) :
    (uniformMeasure a b).quantile u = a + (b - a) * u := by
  let _ : IsProbabilityMeasure (uniformMeasure a b) := isProbabilityMeasure_uniformMeasure hab
  have hba : 0 < b - a := sub_pos.mpr hab
  have hau : a < a + (b - a) * u := lt_add_of_pos_right a (mul_pos hba hu.1)
  have hub : a + (b - a) * u < b := by
    have := mul_lt_mul_of_pos_left hu.2 hba
    linarith
  apply le_antisymm
  · rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_uniformMeasure hab]
    rw [ite_eq_right (not_le.mpr hau), ite_eq_right (not_le.mpr hub)]
    field_simp
    ring_nf
    exact le_refl (u * b - u * a)
  · have hcdf := Measure.le_cdf_quantile (uniformMeasure a b) hu.2
    rw [cdf_uniformMeasure hab] at hcdf
    split_ifs at hcdf with hleft hright
    · exact (not_le_of_gt hu.1 hcdf).elim
    · exact hub.le.trans hright
    · have := (le_div_iff₀ hba).mp hcdf
      linarith

/-- Uniform quantiles tend to the lower endpoint as the probability level tends to zero from
above. -/
theorem tendsto_quantile_uniformMeasure_nhdsGT_zero (hab : a < b) :
    Tendsto (uniformMeasure a b).quantile (nhdsWithin 0 (Ioi 0)) (nhds a) := by
  have hlim : Tendsto (fun u : ℝ ↦ a + (b - a) * u) (nhdsWithin 0 (Ioi 0)) (nhds a) := by
    have hcont : ContinuousAt (fun u : ℝ ↦ a + (b - a) * u) 0 := by fun_prop
    have hwithin := hcont.continuousWithinAt (s := Ioi 0)
    have hval : a + (b - a) * 0 = a := by ring
    simpa only [ContinuousWithinAt, hval] using hwithin
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT one_pos] with u hu
  exact (quantile_uniformMeasure hab hu).symm

/-- Uniform quantiles tend to the upper endpoint as the probability level tends to one from
below. -/
theorem tendsto_quantile_uniformMeasure_nhdsLT_one (hab : a < b) :
    Tendsto (uniformMeasure a b).quantile (nhdsWithin 1 (Iio 1)) (nhds b) := by
  have hlim : Tendsto (fun u : ℝ ↦ a + (b - a) * u) (nhdsWithin 1 (Iio 1)) (nhds b) := by
    have hcont : ContinuousAt (fun u : ℝ ↦ a + (b - a) * u) 1 := by fun_prop
    have hwithin := hcont.continuousWithinAt (s := Iio 1)
    have hval : a + (b - a) * 1 = b := by ring
    simpa only [ContinuousWithinAt, hval] using hwithin
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_uniformMeasure hab hu).symm

end TauCeti.Probability
