/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Cdf
public import TauCeti.Probability.Quantile
import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Inverse

/-!
# Quantiles and powers of Beta laws

This file computes the lower quantile of a Beta probability measure with positive shape
parameters. At an interior probability level `u`, it is the inverse regularized incomplete Beta
function `inverseRegularizedIncompleteBeta a b u`. Consequently its one-sided endpoint limits are
the endpoints `0` and `1` of the Beta law's support.

When the second shape parameter is one, the quantile collapses to the power `u ^ a⁻¹`; when the
first shape parameter is one, it collapses by reflection to `1 - (1 - u) ^ b⁻¹`. For a `Beta(a, 1)`
variable, raising to a positive real power `p` gives the law `Beta(a / p, 1)`. In particular,
squaring halves the first shape parameter. These transformations follow from the power-function
quantile and identify powers of normalized uniform-ball radii.

## Main results

* `TauCeti.Probability.quantile_betaMeasure` gives the explicit quantile formula;
* `TauCeti.Probability.quantile_betaMeasure_one_right` and
  `TauCeti.Probability.quantile_betaMeasure_one_left` give the elementary power quantiles `u ^ a⁻¹`
  and `1 - (1 - u) ^ b⁻¹` when either shape parameter is one;
* `TauCeti.Probability.betaMeasure_map_rpow_one_right` and
  `TauCeti.Probability.betaMeasure_map_sq_one_right` give the positive-power and square laws
  when the second shape parameter is one;
* `TauCeti.Probability.tendsto_quantile_betaMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_betaMeasure_nhdsLT_one` give its endpoint limits.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {a b u : ℝ}

/-- The lower quantile of a Beta law with positive shape parameters is the inverse regularized
incomplete Beta function. -/
@[simp]
theorem quantile_betaMeasure (ha : 0 < a) (hb : 0 < b) (hu : u ∈ Ioo 0 1) :
    (betaMeasure a b).quantile u = inverseRegularizedIncompleteBeta a b u := by
  apply le_antisymm
  · rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_betaMeasure_eq ha hb,
      regularizedIncompleteBeta_inverse ha hb hu.1 hu.2]
  · rw [inverseRegularizedIncompleteBeta_le_iff ha hb hu.1 hu.2]
    simpa only [cdf_betaMeasure_eq ha hb] using Measure.le_cdf_quantile (betaMeasure a b) hu.2

/-- With second shape parameter one the beta law is the power-function law, whose lower quantile
at an interior level `u` is `u ^ a⁻¹`. -/
theorem quantile_betaMeasure_one_right (ha : 0 < a) (hu : u ∈ Ioo 0 1) :
    (betaMeasure a 1).quantile u = u ^ a⁻¹ := by
  rw [quantile_betaMeasure ha one_pos hu,
    inverseRegularizedIncompleteBeta_one_right ha hu.1 hu.2]

/-- With first shape parameter one the beta law has cumulative distribution function
`1 - (1 - x) ^ b` on `[0, 1]`, and its lower quantile at an interior level `u` is
`1 - (1 - u) ^ b⁻¹`. -/
theorem quantile_betaMeasure_one_left (hb : 0 < b) (hu : u ∈ Ioo 0 1) :
    (betaMeasure 1 b).quantile u = 1 - (1 - u) ^ b⁻¹ := by
  rw [quantile_betaMeasure one_pos hb hu,
    inverseRegularizedIncompleteBeta_one_left hb hu.1 hu.2]

/-- Raising a Beta variable with second shape one to a positive real power divides its first
shape by that power. -/
@[simp]
theorem betaMeasure_map_rpow_one_right {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    (betaMeasure a 1).map (fun x ↦ x ^ p) = betaMeasure (a / p) 1 := by
  have := isProbabilityMeasureBeta ha one_pos
  have := isProbabilityMeasureBeta (div_pos ha hp) one_pos
  rw [← Measure.map_quantile_volume_Ioo (betaMeasure a 1),
    Measure.map_map (by fun_prop) (Measure.measurable_quantile _),
    ← Measure.map_quantile_volume_Ioo (betaMeasure (a / p) 1)]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  simp only [Function.comp_apply, quantile_betaMeasure_one_right ha hu,
    quantile_betaMeasure_one_right (div_pos ha hp) hu]
  rw [← Real.rpow_mul hu.1.le]
  congr 1
  simp [div_eq_mul_inv, mul_comm]

/-- Squaring a Beta variable with second shape one halves its first shape. -/
@[simp]
theorem betaMeasure_map_sq_one_right {a : ℝ} (ha : 0 < a) :
    (betaMeasure a 1).map (fun x ↦ x ^ 2) = betaMeasure (a / 2) 1 := by
  simpa only [Real.rpow_two] using betaMeasure_map_rpow_one_right ha two_pos

/-- Beta quantiles tend to the lower support endpoint `0` as the probability level tends to zero
from above. -/
theorem tendsto_quantile_betaMeasure_nhdsGT_zero (ha : 0 < a) (hb : 0 < b) :
    Tendsto (betaMeasure a b).quantile (𝓝[>] 0) (𝓝 0) := by
  apply (tendsto_inverseRegularizedIncompleteBeta_zero a b).congr'
  filter_upwards [Ioo_mem_nhdsGT one_pos] with u hu
  exact (quantile_betaMeasure ha hb hu).symm

/-- Beta quantiles tend to the upper support endpoint `1` as the probability level tends to one
from below. -/
theorem tendsto_quantile_betaMeasure_nhdsLT_one (ha : 0 < a) (hb : 0 < b) :
    Tendsto (betaMeasure a b).quantile (𝓝[<] 1) (𝓝 1) := by
  apply (tendsto_inverseRegularizedIncompleteBeta_one ha hb).congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_betaMeasure ha hb hu).symm

end TauCeti.Probability
