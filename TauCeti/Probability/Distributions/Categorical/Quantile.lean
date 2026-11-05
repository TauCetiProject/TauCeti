/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Categorical.Basic
public import TauCeti.Probability.Quantile.Finite

/-!
# Quantiles of labeled categorical laws

Real labels need neither be distinct nor respect an order on categories. The mass of a label
adds all the weights in its fibre. Quantiles are finite cumulative crossings among the distinct
positive-weight labels, and their endpoint limits are the smallest and largest such labels.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 35.
-/

public section

noncomputable section

open Convexity Filter MeasureTheory ProbabilityTheory Set Topology
open TauCeti.Probability
open scoped NNReal ENNReal

namespace Convexity.StdSimplex

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- A real number is the quantile of a categorical law with supplied real labels exactly when
the level strictly exceeds the total weight of smaller labels and is at most the total weight of
labels no larger than it. This sorts distinct labels and aggregates equal labels automatically. -/
theorem quantile_map_categoricalMeasure_eq_iff (p : StdSimplex NNReal I) (label : I → ℝ)
    {u x : ℝ} (hu : u ∈ Ioo 0 1) :
    ((categoricalMeasure p).map label).quantile u = x ↔
      (∑ i with label i < x, (p.weights i : ℝ)) < u ∧
        u ≤ ∑ i with label i ≤ x, (p.weights i : ℝ) := by
  rw [Measure.quantile_map_finite_eq_iff _ label hu,
    ← map_measureReal_apply (measurable_of_finite label) measurableSet_Iio,
    p.map_categoricalMeasure_real_Iio,
    ← Measure.cdf_map _ label (measurable_of_finite label), p.cdf_map_categoricalMeasure]

/-- As the level tends to zero from above, categorical quantiles tend to any least label whose
category has positive weight. Zero-weight categories do not affect the endpoint. -/
theorem tendsto_quantile_map_categoricalMeasure_nhdsGT_zero
    (p : StdSimplex NNReal I) (label : I → ℝ) (i : I) (hi : 0 < (p.weights i : ℝ))
    (hmin : ∀ j, 0 < (p.weights j : ℝ) → label i ≤ label j) :
    Tendsto ((categoricalMeasure p).map label).quantile (𝓝[>] 0) (𝓝 (label i)) := by
  apply Measure.tendsto_quantile_map_finite_nhdsGT_zero (categoricalMeasure p) label i
  · simpa only [categoricalMeasure_real_singleton] using hi
  · intro j hj
    exact hmin j (by simpa only [categoricalMeasure_real_singleton] using hj)

/-- As the level tends to one from below, categorical quantiles tend to any greatest label whose
category has positive weight. Zero-weight categories do not affect the endpoint. -/
theorem tendsto_quantile_map_categoricalMeasure_nhdsLT_one
    (p : StdSimplex NNReal I) (label : I → ℝ) (i : I) (hi : 0 < (p.weights i : ℝ))
    (hmax : ∀ j, 0 < (p.weights j : ℝ) → label j ≤ label i) :
    Tendsto ((categoricalMeasure p).map label).quantile (𝓝[<] 1) (𝓝 (label i)) := by
  apply Measure.tendsto_quantile_map_finite_nhdsLT_one (categoricalMeasure p) label i
  · simpa only [categoricalMeasure_real_singleton] using hi
  · intro j hj
    exact hmax j (by simpa only [categoricalMeasure_real_singleton] using hj)

open Classical in
/-- Compute a categorical quantile by taking the minimum of the distinct positive-weight labels
whose cumulative weight reaches the level. -/
theorem quantile_map_categoricalMeasure (p : StdSimplex ℝ≥0 I) (f : I → ℝ)
    {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((categoricalMeasure p).map f).quantile u =
      ((p.weights.support.image f).filter fun y ↦
        u ≤ ∑ i with f i ≤ y, (p.weights i : ℝ)).min' (by
          simpa only [cdf_map_categoricalMeasure] using
            ((categoricalMeasure p).map f).nonempty_filter_le_cdf
              (ae_mem_image_support_map_categoricalMeasure p f) hu) := by
  simpa only [cdf_map_categoricalMeasure] using
    ((categoricalMeasure p).map f).quantile_eq_min'_of_ae_mem_finset
      (ae_mem_image_support_map_categoricalMeasure p f) hu

end Convexity.StdSimplex
