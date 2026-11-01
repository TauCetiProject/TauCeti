/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Categorical
public import TauCeti.Probability.Quantile.Finite

/-!
# Quantiles of labelled categorical laws

A real label map turns a categorical outcome into a finitely supported real law. This file
characterizes each interior quantile by sorting the distinct supplied labels and taking the first
cumulative crossing. The cumulative sums run over categories rather than distinct values, so equal
labels have their masses combined. Zero-weight categories do not affect either endpoint.

## Main results

* `isLeast_quantile_map_categoricalMeasure` gives the weighted categorical crossing formula.
* `tendsto_quantile_map_categoricalMeasure_nhdsGT_zero` and
  `tendsto_quantile_map_categoricalMeasure_nhdsLT_one` identify the one-sided endpoint limits.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 35.
-/

public section

noncomputable section

open Convexity Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-- The cumulative mass of a labelled categorical law is the sum of the weights of all
categories whose labels are at most the threshold. Equal labels are therefore aggregated. -/
theorem categoricalMeasure_real_setOf_label_le (p : StdSimplex ℝ≥0 ι)
    (label : ι → ℝ) (x : ℝ) :
    (categoricalMeasure p).real {i | label i ≤ x} =
      ∑ i with label i ≤ x, (p.weights i : ℝ) := by
  classical
  rw [← Finset.coe_filter_univ, ← sum_measureReal_singleton]
  simp only [categoricalMeasure_real_singleton]

/-- The quantile of a labelled categorical law is the least distinct label whose accumulated
weight reaches the level. Categories with equal labels contribute to the same crossing. -/
theorem isLeast_quantile_map_categoricalMeasure (p : StdSimplex ℝ≥0 ι)
    (label : ι → ℝ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    IsLeast {x : ℝ | x ∈ Set.range label ∧
      u ≤ ∑ i with label i ≤ x, (p.weights i : ℝ)}
      (((categoricalMeasure p).map label).quantile u) := by
  simpa only [categoricalMeasure_real_setOf_label_le] using
    Measure.isLeast_quantile_map_finite (categoricalMeasure p) label hu

private theorem categoricalMeasure_real_label_eq_pos (p : StdSimplex ℝ≥0 ι)
    (label : ι → ℝ) {x : ℝ} (hx : ∃ i, label i = x ∧ 0 < p.weights i) :
    0 < (categoricalMeasure p).real {j | label j = x} := by
  obtain ⟨i, hi, hpi⟩ := hx
  have hsingle : 0 < (categoricalMeasure p).real {i} := by
    rw [categoricalMeasure_real_singleton]
    exact_mod_cast hpi
  exact hsingle.trans_le (measureReal_mono (singleton_subset_iff.mpr hi))

/-- At levels tending to zero, categorical quantiles tend to a lowest label carrying positive
weight. -/
theorem tendsto_quantile_map_categoricalMeasure_nhdsGT_zero (p : StdSimplex ℝ≥0 ι)
    (label : ι → ℝ) (a : ℝ) (ha : ∃ i, label i = a ∧ 0 < p.weights i)
    (hmin : ∀ i, 0 < p.weights i → a ≤ label i) :
    Tendsto (fun u ↦ (((categoricalMeasure p).map label).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (a : EReal)) := by
  apply Measure.tendsto_quantile_map_nhdsGT_zero_of_atom _ (measurable_of_finite label)
  · exact (ae_categoricalMeasure_iff p).2 hmin
  · exact categoricalMeasure_real_label_eq_pos p label ha

/-- At levels tending to one, categorical quantiles tend to a highest label carrying positive
weight. -/
theorem tendsto_quantile_map_categoricalMeasure_nhdsLT_one (p : StdSimplex ℝ≥0 ι)
    (label : ι → ℝ) (b : ℝ) (hb : ∃ i, label i = b ∧ 0 < p.weights i)
    (hmax : ∀ i, 0 < p.weights i → label i ≤ b) :
    Tendsto (fun u ↦ (((categoricalMeasure p).map label).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (b : EReal)) := by
  apply Measure.tendsto_quantile_map_nhdsLT_one_of_atom _ (measurable_of_finite label)
  · exact (ae_categoricalMeasure_iff p).2 hmax
  · exact categoricalMeasure_real_label_eq_pos p label hb

end TauCeti.Probability
