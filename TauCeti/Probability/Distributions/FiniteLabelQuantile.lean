/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Categorical
public import TauCeti.Probability.Distributions.Uniform.Finite
public import TauCeti.Probability.Quantile.Finite

/-!
# Quantiles of labelled finite laws

A real label map turns a categorical or finite-uniform outcome into a finitely supported real
law.  This file characterizes each interior quantile by sorting the distinct supplied labels and
taking the first cumulative crossing.  The cumulative sums run over categories rather than
distinct values, so equal labels have their masses combined.  For categorical laws, zero-weight
categories do not affect either endpoint.

## Main results

* `quantile_map_categoricalMeasure_isLeast` gives the weighted categorical crossing formula.
* `quantile_map_uniformOn_univ_isLeast` gives the finite-uniform counting formula.
* The four `tendsto_quantile_map_...` theorems identify the one-sided endpoint limits.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 35.
-/

public section

noncomputable section

open Convexity Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-- The cumulative mass of a labelled categorical law is the sum of the weights of all
categories whose labels are at most the threshold.  Equal labels are therefore aggregated. -/
theorem categoricalMeasure_real_le_label (p : StdSimplex ℝ≥0 ι) (label : ι → ℝ) (x : ℝ) :
    (categoricalMeasure p).real {i | label i ≤ x} =
      ∑ i with label i ≤ x, (p.weights i : ℝ) := by
  classical
  rw [show {i | label i ≤ x} =
    (↑(Finset.univ.filter fun i => label i ≤ x) : Set ι) by ext; simp]
  rw [← sum_measureReal_singleton]
  simp only [categoricalMeasure_real_singleton]

/-- The quantile of a labelled categorical law is the least distinct label whose accumulated
weight reaches the level.  Categories with equal labels contribute to the same crossing. -/
theorem quantile_map_categoricalMeasure_isLeast (p : StdSimplex ℝ≥0 ι)
    (label : ι → ℝ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    IsLeast {x : ℝ | x ∈ Set.range label ∧
      u ≤ ∑ i with label i ≤ x, (p.weights i : ℝ)}
      (((categoricalMeasure p).map label).quantile u) := by
  let _ := p.nonempty
  simpa only [categoricalMeasure_real_le_label] using
    Measure.isLeast_quantile_map_finite (categoricalMeasure p) label hu

/-- The real mass of a singleton under the uniform law on a nonempty finite type is the
reciprocal of the cardinality. -/
@[simp]
theorem uniformOn_univ_real_singleton (i : ι) :
    (uniformOn (Set.univ : Set ι)).real {i} = (Fintype.card ι : ℝ)⁻¹ := by
  rw [measureReal_def, uniformOn_univ_apply_singleton]
  rw [ENNReal.toReal_inv]
  norm_cast

/-- The cumulative mass of a labelled uniform law is the fraction of categories whose labels
are at most the threshold.  Repeated labels are counted with their full multiplicity. -/
theorem uniformOn_univ_real_le_label (label : ι → ℝ) (x : ℝ) :
    (uniformOn (Set.univ : Set ι)).real {i | label i ≤ x} =
      ((Finset.univ.filter fun i => label i ≤ x).card : ℝ) / Fintype.card ι := by
  classical
  rw [show {i | label i ≤ x} =
    (↑(Finset.univ.filter fun i => label i ≤ x) : Set ι) by ext; simp]
  rw [← sum_measureReal_singleton]
  simp [div_eq_mul_inv]

/-- The quantile of a labelled uniform law is the least distinct label for which the fraction of
categories at or below that label reaches the requested level. -/
theorem quantile_map_uniformOn_univ_isLeast [Nonempty ι]
    (label : ι → ℝ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    IsLeast {x : ℝ | x ∈ Set.range label ∧
      u ≤ ((Finset.univ.filter fun i => label i ≤ x).card : ℝ) / Fintype.card ι}
      (((uniformOn (Set.univ : Set ι)).map label).quantile u) := by
  simpa only [uniformOn_univ_real_le_label] using
    Measure.isLeast_quantile_map_finite (uniformOn (Set.univ : Set ι)) label hu

/-- At levels tending to zero, categorical quantiles tend to a lowest label carrying positive
weight. -/
theorem tendsto_quantile_map_categoricalMeasure_nhdsGT_zero (p : StdSimplex ℝ≥0 ι)
    (label : ι → ℝ) (a : ℝ) (ha : ∃ i, label i = a ∧ 0 < p.weights i)
    (hmin : ∀ i, 0 < p.weights i → a ≤ label i) :
    Tendsto (fun u ↦ (((categoricalMeasure p).map label).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (a : EReal)) := by
  apply Measure.tendsto_quantile_map_finite_nhdsGT_zero
  · apply ae_iff_of_countable.mpr
    intro i hi
    apply hmin i
    exact pos_iff_ne_zero.mpr (ENNReal.coe_ne_zero.mp (by simpa using hi))
  · obtain ⟨i, hi, hpi⟩ := ha
    have hsingle : 0 < (categoricalMeasure p).real {i} := by
      rw [categoricalMeasure_real_singleton]
      exact_mod_cast hpi
    exact hsingle.trans_le (measureReal_mono (singleton_subset_iff.mpr hi))

/-- At levels tending to one, categorical quantiles tend to a highest label carrying positive
weight. -/
theorem tendsto_quantile_map_categoricalMeasure_nhdsLT_one (p : StdSimplex ℝ≥0 ι)
    (label : ι → ℝ) (b : ℝ) (hb : ∃ i, label i = b ∧ 0 < p.weights i)
    (hmax : ∀ i, 0 < p.weights i → label i ≤ b) :
    Tendsto (fun u ↦ (((categoricalMeasure p).map label).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (b : EReal)) := by
  apply Measure.tendsto_quantile_map_finite_nhdsLT_one
  · apply ae_iff_of_countable.mpr
    intro i hi
    apply hmax i
    exact pos_iff_ne_zero.mpr (ENNReal.coe_ne_zero.mp (by simpa using hi))
  · obtain ⟨i, hi, hpi⟩ := hb
    have hsingle : 0 < (categoricalMeasure p).real {i} := by
      rw [categoricalMeasure_real_singleton]
      exact_mod_cast hpi
    exact hsingle.trans_le (measureReal_mono (singleton_subset_iff.mpr hi))

/-- At levels tending to zero, finite-uniform quantiles tend to a lowest supplied label. -/
theorem tendsto_quantile_map_uniformOn_univ_nhdsGT_zero
    {κ : Type*} [Finite κ] [Nonempty κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (label : κ → ℝ) (a : ℝ)
    (ha : ∃ i, label i = a) (hmin : ∀ i, a ≤ label i) :
    Tendsto (fun u ↦ (((uniformOn (Set.univ : Set κ)).map label).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (a : EReal)) := by
  let _ := Fintype.ofFinite κ
  apply Measure.tendsto_quantile_map_finite_nhdsGT_zero
  · exact ae_of_all _ hmin
  · obtain ⟨i, hi⟩ := ha
    have hsingle : 0 < (uniformOn (Set.univ : Set κ)).real {i} := by
      rw [uniformOn_univ_real_singleton]
      exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    exact hsingle.trans_le (measureReal_mono (singleton_subset_iff.mpr hi))

/-- At levels tending to one, finite-uniform quantiles tend to a highest supplied label. -/
theorem tendsto_quantile_map_uniformOn_univ_nhdsLT_one
    {κ : Type*} [Finite κ] [Nonempty κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (label : κ → ℝ) (b : ℝ)
    (hb : ∃ i, label i = b) (hmax : ∀ i, label i ≤ b) :
    Tendsto (fun u ↦ (((uniformOn (Set.univ : Set κ)).map label).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (b : EReal)) := by
  let _ := Fintype.ofFinite κ
  apply Measure.tendsto_quantile_map_finite_nhdsLT_one
  · exact ae_of_all _ hmax
  · obtain ⟨i, hi⟩ := hb
    have hsingle : 0 < (uniformOn (Set.univ : Set κ)).real {i} := by
      rw [uniformOn_univ_real_singleton]
      exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    exact hsingle.trans_le (measureReal_mono (singleton_subset_iff.mpr hi))

end TauCeti.Probability
