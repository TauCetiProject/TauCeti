/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Cdf
public import TauCeti.Probability.Quantile

/-!
# Quantiles of Beta laws

This file computes the lower quantile of a Beta probability measure with positive shape
parameters. At an interior probability level `u`, it is the inverse regularized incomplete Beta
function `inverseRegularizedIncompleteBeta a b u`. Consequently its one-sided endpoint limits are
the endpoints `0` and `1` of the Beta law's support.

## Main results

* `TauCeti.Probability.quantile_betaMeasure` gives the explicit quantile formula;
* `TauCeti.Probability.quantile_betaMeasure_one_right` gives the power-function quantile
  `u ^ a⁻¹` when the second shape parameter is one;
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
  have hq : u ^ a⁻¹ ∈ Ioo 0 1 :=
    ⟨Real.rpow_pos_of_pos hu.1 _, Real.rpow_lt_one hu.1.le hu.2 (inv_pos.2 ha)⟩
  have hu' : regularizedIncompleteBeta a 1 (u ^ a⁻¹) = u := by
    rw [regularizedIncompleteBeta_one_right ha hq.1.le hq.2.le, ← Real.rpow_mul hu.1.le,
      inv_mul_cancel₀ ha.ne', Real.rpow_one]
  rw [quantile_betaMeasure ha one_pos hu]
  conv_lhs => rw [← hu']
  exact inverseRegularizedIncompleteBeta_regularizedIncompleteBeta ha one_pos hq.1 hq.2

/-- Beta quantiles tend to the lower support endpoint `0` as the probability level tends to zero
from above. -/
theorem tendsto_quantile_betaMeasure_nhdsGT_zero (ha : 0 < a) (hb : 0 < b) :
    Tendsto (betaMeasure a b).quantile (𝓝[>] 0) (𝓝 0) := by
  apply (tendsto_inverseRegularizedIncompleteBeta_zero ha hb).congr'
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
