/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Basic
public import TauCeti.Probability.Distributions.Uniform.Finite
public import TauCeti.Probability.Quantile
public import TauCeti.Probability.Quantile.Finite

/-!
# Quantiles of interval and finite-uniform laws

This file computes the lower quantile of the uniform probability measure on a nondegenerate real
interval. At an interior probability level `u`, the quantile is the affine interpolation
`a + (b - a) * u`. Consequently the quantiles tend to the two interval endpoints as the level
tends to zero from above or to one from below.

For a uniform law on a finite type with supplied real labels, the quantile is the first distinct
label whose cumulative cardinality fraction reaches the requested level. Repeated labels retain
their full multiplicity.

## Main results

* `TauCeti.Probability.quantile_uniformMeasure` gives the explicit quantile formula;
* `TauCeti.Probability.tendsto_quantile_uniformMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_uniformMeasure_nhdsLT_one` give its endpoint limits;
* `TauCeti.Probability.isLeast_quantile_map_uniformOn_univ` gives the finite-uniform cumulative
  crossing formula.
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

section Finite

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The cumulative mass of a labelled uniform law is the fraction of categories whose labels
are at most the threshold. Repeated labels are counted with their full multiplicity. -/
theorem uniformOn_univ_real_setOf_label_le (label : ι → ℝ) (x : ℝ) :
    (uniformOn (Set.univ : Set ι)).real {i | label i ≤ x} =
      ((Finset.univ.filter fun i => label i ≤ x).card : ℝ) / Fintype.card ι := by
  classical
  rw [← Finset.coe_filter_univ, ← sum_measureReal_singleton]
  simp [div_eq_mul_inv]

/-- The quantile of a labelled uniform law is the least distinct label for which the fraction of
categories at or below that label reaches the requested level. -/
theorem isLeast_quantile_map_uniformOn_univ [Nonempty ι]
    (label : ι → ℝ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    IsLeast {x : ℝ | x ∈ Set.range label ∧
      u ≤ ((Finset.univ.filter fun i => label i ≤ x).card : ℝ) / Fintype.card ι}
      (((uniformOn (Set.univ : Set ι)).map label).quantile u) := by
  simpa only [uniformOn_univ_real_setOf_label_le] using
    Measure.isLeast_quantile_map_finite (uniformOn (Set.univ : Set ι)) label hu

private theorem uniformOn_univ_real_label_eq_pos
    {κ : Type*} [Finite κ] [Nonempty κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (label : κ → ℝ) {x : ℝ} (hx : ∃ i, label i = x) :
    0 < (uniformOn (Set.univ : Set κ)).real {j | label j = x} := by
  let _ := Fintype.ofFinite κ
  obtain ⟨i, hi⟩ := hx
  have hsingle : 0 < (uniformOn (Set.univ : Set κ)).real {i} := by
    rw [uniformOn_univ_real_singleton]
    exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  exact hsingle.trans_le (measureReal_mono (singleton_subset_iff.mpr hi))

/-- At levels tending to zero, finite-uniform quantiles tend to a lowest supplied label. -/
theorem tendsto_quantile_map_uniformOn_univ_nhdsGT_zero
    {κ : Type*} [Finite κ] [Nonempty κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (label : κ → ℝ) (a : ℝ)
    (ha : ∃ i, label i = a) (hmin : ∀ i, a ≤ label i) :
    Tendsto (fun u ↦ (((uniformOn (Set.univ : Set κ)).map label).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (a : EReal)) := by
  let _ := Fintype.ofFinite κ
  apply Measure.tendsto_quantile_map_nhdsGT_zero_of_atom _ (measurable_of_finite label)
  · exact ae_of_all _ hmin
  · exact uniformOn_univ_real_label_eq_pos label ha

/-- At levels tending to one, finite-uniform quantiles tend to a highest supplied label. -/
theorem tendsto_quantile_map_uniformOn_univ_nhdsLT_one
    {κ : Type*} [Finite κ] [Nonempty κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (label : κ → ℝ) (b : ℝ)
    (hb : ∃ i, label i = b) (hmax : ∀ i, label i ≤ b) :
    Tendsto (fun u ↦ (((uniformOn (Set.univ : Set κ)).map label).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (b : EReal)) := by
  let _ := Fintype.ofFinite κ
  apply Measure.tendsto_quantile_map_nhdsLT_one_of_atom _ (measurable_of_finite label)
  · exact ae_of_all _ hmax
  · exact uniformOn_univ_real_label_eq_pos label hb

end Finite

end TauCeti.Probability
