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
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

open Classical in
/-- A label is the quantile exactly when it is the least positive-weight label whose explicit
cumulative weight reaches the level. No ordering or injectivity of the labels is assumed. -/
theorem quantile_map_categoricalMeasure_eq_iff (p : StdSimplex ℝ≥0 ι) (f : ι → ℝ)
    {u x : ℝ} (hu : u ∈ Ioo 0 1) :
    ((categoricalMeasure p).map f).quantile u = x ↔
      IsLeast {y | y ∈ p.weights.support.image f ∧
        u ≤ ∑ i with f i ≤ y, (p.weights i : ℝ)} x := by
  simpa only [cdf_map_categoricalMeasure] using
    ((categoricalMeasure p).map f).quantile_eq_iff_of_ae_mem_finset
      (ae_mem_image_support_map_categoricalMeasure p f) hu

open Classical in
/-- Compute a categorical quantile by taking the minimum of the distinct positive-weight labels
whose cumulative weight reaches the level. -/
theorem quantile_map_categoricalMeasure (p : StdSimplex ℝ≥0 ι) (f : ι → ℝ)
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

/-- At the lower endpoint, categorical quantiles tend to the smallest positive-weight label. -/
theorem tendsto_quantile_map_categoricalMeasure_nhdsGT_zero
    (p : StdSimplex ℝ≥0 ι) (f : ι → ℝ) :
    Tendsto (fun u ↦ (((categoricalMeasure p).map f).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ((p.weights.support.image f).min'
        (p.support_weights_nonempty.image f) : EReal)) := by
  apply Measure.tendsto_quantile_nhdsGT_zero_of_ae_mem_finset _
    (ae_mem_image_support_map_categoricalMeasure p f)
  exact map_categoricalMeasure_singleton_ne_zero p f (Finset.min'_mem _ _)

/-- At the upper endpoint, categorical quantiles tend to the largest positive-weight label. -/
theorem tendsto_quantile_map_categoricalMeasure_nhdsLT_one
    (p : StdSimplex ℝ≥0 ι) (f : ι → ℝ) :
    Tendsto (fun u ↦ (((categoricalMeasure p).map f).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ((p.weights.support.image f).max'
        (p.support_weights_nonempty.image f) : EReal)) := by
  apply Measure.tendsto_quantile_nhdsLT_one_of_ae_mem_finset _
    (ae_mem_image_support_map_categoricalMeasure p f)
  exact map_categoricalMeasure_singleton_ne_zero p f (Finset.max'_mem _ _)

end TauCeti.Probability
