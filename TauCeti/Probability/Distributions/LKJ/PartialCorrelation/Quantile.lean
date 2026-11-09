/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LKJ.PartialCorrelation.Basic
public import TauCeti.Probability.Distributions.Beta.Quantile
import TauCeti.Probability.Distributions.Affine

/-!
# Quantiles of LKJ partial correlations

Read a symmetric correlation matrix in strictly lower coordinates, then apply
`TauCeti.partialCorrelationOfCorrelationCoordinates`. Under the LKJ law of positive shape,
these partial correlations are independent centered symmetric Beta variables. In zero-based
column `j` their Beta shape is `lkjPartialCorrelationShape p η ij`.

Using the native-matrix laws proved in the basic partial-correlation file, this file gives
the scalar quantile formula
`-1 + 2 * inverseRegularizedIncompleteBeta a a u` for interior levels. Its one-sided endpoint
limits are `-1` and `1`. Dimensions zero and one have no partial-correlation coordinates.

The extraction uses the existing totalized coordinate inverse; its values outside the
positive-definite correlation region do not affect these laws.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {p : ℕ} {η : ℝ}

/-- An interior quantile of an LKJ partial correlation is the centered inverse-Beta quantile
with the shape of its column. -/
@[simp]
theorem quantile_map_eval_partialCorrelationOfCorrelationCoordinates_lkjMeasure (hη : 0 < η)
    (ij : strictLowerTriangle p) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((lkjMeasure p η).map
      (fun R ↦ partialCorrelationOfCorrelationCoordinates (correlationCoordinates p R) ij)).quantile
        u = -1 + 2 * inverseRegularizedIncompleteBeta (lkjPartialCorrelationShape p η ij)
          (lkjPartialCorrelationShape p η ij) u := by
  have ha := lkjPartialCorrelationShape_pos hη ij
  let _ := isProbabilityMeasureBeta ha ha
  rw [map_eval_partialCorrelationOfCorrelationCoordinates_lkjMeasure hη ij,
    quantile_map_affine_pos (by norm_num) hu.1 hu.2, quantile_betaMeasure ha ha hu]

/-- LKJ partial-correlation quantiles tend to the lower support endpoint `-1`. -/
theorem tendsto_quantile_partialCorrelation_lkjMeasure_nhdsGT_zero (hη : 0 < η)
    (ij : strictLowerTriangle p) :
    Tendsto ((lkjMeasure p η).map
      (fun R ↦ partialCorrelationOfCorrelationCoordinates (correlationCoordinates p R) ij)).quantile
        (𝓝[>] 0) (𝓝 (-1)) := by
  have ha := lkjPartialCorrelationShape_pos hη ij
  have h := ((tendsto_inverseRegularizedIncompleteBeta_zero ha ha).const_mul 2).const_add (-1)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact (quantile_map_eval_partialCorrelationOfCorrelationCoordinates_lkjMeasure hη ij hu).symm

/-- LKJ partial-correlation quantiles tend to the upper support endpoint `1`. -/
theorem tendsto_quantile_partialCorrelation_lkjMeasure_nhdsLT_one (hη : 0 < η)
    (ij : strictLowerTriangle p) :
    Tendsto ((lkjMeasure p η).map
      (fun R ↦ partialCorrelationOfCorrelationCoordinates (correlationCoordinates p R) ij)).quantile
        (𝓝[<] 1) (𝓝 1) := by
  have ha := lkjPartialCorrelationShape_pos hη ij
  have h := ((tendsto_inverseRegularizedIncompleteBeta_one ha ha).const_mul 2).const_add (-1)
  norm_num only [mul_one, neg_add_cancel_left] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_map_eval_partialCorrelationOfCorrelationCoordinates_lkjMeasure hη ij hu).symm

end TauCeti.Probability
