/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Basic
public import TauCeti.Probability.Distributions.Uniform.Finite
public import TauCeti.Probability.Quantile.Finite

/-!
# Quantiles of uniform laws

This file computes the lower quantile of the uniform probability measure on a nondegenerate real
interval. At an interior probability level `u`, the quantile is the affine interpolation
`a + (b - a) * u`. Consequently the quantiles tend to the two interval endpoints as the level
tends to zero from above or to one from below.

For finite uniform sampling with arbitrary real labels, quantiles are the least distinct labels
whose cumulative input counts reach the requested level, retaining multiplicities of repeated
labels. Their endpoint limits are the smallest and largest attained labels.

## Main results

* `TauCeti.Probability.quantile_uniformMeasure` gives the explicit quantile formula;
* `TauCeti.Probability.tendsto_quantile_uniformMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_uniformMeasure_nhdsLT_one` give its endpoint limits;
* `Finset.quantile_map_uniformOn_finset_eq_iff` and `Finset.quantile_map_uniformOn_finset`
  characterize and compute finite uniform quantiles by cumulative counts;
* `Finset.tendsto_quantile_map_uniformOn_finset_nhdsGT_zero` and
  `Finset.tendsto_quantile_map_uniformOn_finset_nhdsLT_one` give the finite uniform endpoint limits.
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

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A real number is the quantile of a uniformly sampled finite collection of supplied labels
exactly when the level strictly exceeds the proportion of smaller labels and is at most the
proportion of labels no larger than it. This is the cumulative-crossing description obtained by
sorting the distinct labels and aggregating equal ones. -/
theorem quantile_map_uniformOn_univ_eq_iff [Fintype α] [Nonempty α] (label : α → ℝ)
    {u x : ℝ} (hu : u ∈ Set.Ioo 0 1) :
    ((uniformOn (Set.univ : Set α)).map label).quantile u = x ↔
      ((Finset.univ.filter fun i ↦ label i < x).card : ℝ) / Fintype.card α < u ∧
        u ≤ ((Finset.univ.filter fun i ↦ label i ≤ x).card : ℝ) / Fintype.card α := by
  rw [Measure.quantile_map_finite_eq_iff _ label hu]
  have hpreimage_lt : label ⁻¹' Set.Iio x =
      (Finset.univ.filter fun i ↦ label i < x : Finset α) := by
    ext i
    simp
  have hpreimage_le : label ⁻¹' Set.Iic x =
      (Finset.univ.filter fun i ↦ label i ≤ x : Finset α) := by
    ext i
    simp
  rw [hpreimage_lt, hpreimage_le, Finset.uniformOn_univ_real_finset,
    Finset.uniformOn_univ_real_finset]

/-- As the level tends to zero from above, labelled finite-uniform quantiles tend to a least
supplied label. -/
theorem tendsto_quantile_map_uniformOn_univ_nhdsGT_zero [Finite α] [Nonempty α]
    (label : α → ℝ) (i : α) (hmin : ∀ j, label i ≤ label j) :
    Tendsto ((uniformOn (Set.univ : Set α)).map label).quantile (𝓝[>] 0)
      (𝓝 (label i)) := by
  let _ := Fintype.ofFinite α
  apply Measure.tendsto_quantile_map_finite_nhdsGT_zero
    (uniformOn (Set.univ : Set α)) label i
  · rw [measureReal_def, uniformOn_univ_apply_singleton]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  · exact fun j _ ↦ hmin j

/-- As the level tends to one from below, labelled finite-uniform quantiles tend to a greatest
supplied label. -/
theorem tendsto_quantile_map_uniformOn_univ_nhdsLT_one [Finite α] [Nonempty α]
    (label : α → ℝ) (i : α) (hmax : ∀ j, label j ≤ label i) :
    Tendsto ((uniformOn (Set.univ : Set α)).map label).quantile (𝓝[<] 1)
      (𝓝 (label i)) := by
  let _ := Fintype.ofFinite α
  apply Measure.tendsto_quantile_map_finite_nhdsLT_one
    (uniformOn (Set.univ : Set α)) label i
  · rw [measureReal_def, uniformOn_univ_apply_singleton]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  · exact fun j _ ↦ hmax j

end TauCeti.Probability

namespace Finset

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

open Classical in
/-- The uniform quantile is the least distinct label whose cumulative input count reaches the
requested fraction of the sample size. This retains multiplicities of repeated labels. -/
theorem quantile_map_uniformOn_finset_eq_iff (s : Finset α) (hs : s.Nonempty) (f : α → ℝ)
    {u x : ℝ} (hu : u ∈ Set.Ioo 0 1) :
    ((uniformOn (s : Set α)).map f).quantile u = x ↔
      IsLeast {y | y ∈ s.image f ∧
        u ≤ ((s.filter fun i ↦ f i ≤ y).card : ℝ) / s.card} x := by
  let _ := isProbabilityMeasure_uniformOn s.finite_toSet hs
  simpa only [s.cdf_map_uniformOn_finset hs] using
    ((uniformOn (s : Set α)).map f).quantile_eq_iff_of_ae_mem_finset
      (s.ae_mem_image_map_uniformOn_finset f) hu

open Classical in
/-- Compute a finite uniform quantile by a minimum over distinct labels, with cumulative counts
including every input carrying each label. -/
theorem quantile_map_uniformOn_finset (s : Finset α) (hs : s.Nonempty) (f : α → ℝ)
    {u : ℝ} (hu : u ∈ Set.Ioo 0 1) :
    ((uniformOn (s : Set α)).map f).quantile u =
      ((s.image f).filter fun y ↦
        u ≤ ((s.filter fun i ↦ f i ≤ y).card : ℝ) / s.card).min' (by
          let _ := isProbabilityMeasure_uniformOn s.finite_toSet hs
          simpa only [s.cdf_map_uniformOn_finset hs] using
            ((uniformOn (s : Set α)).map f).nonempty_filter_le_cdf
              (s.ae_mem_image_map_uniformOn_finset f) hu) := by
  let _ := isProbabilityMeasure_uniformOn s.finite_toSet hs
  simpa only [s.cdf_map_uniformOn_finset hs] using
    ((uniformOn (s : Set α)).map f).quantile_eq_min'_of_ae_mem_finset
      (s.ae_mem_image_map_uniformOn_finset f) hu

open Filter Topology in
/-- Uniform quantiles tend to the smallest attained label as the level decreases to zero. -/
theorem tendsto_quantile_map_uniformOn_finset_nhdsGT_zero
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    Tendsto (fun u ↦ (((uniformOn (s : Set α)).map f).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ((s.image f).min' (hs.image f) : EReal)) := by
  let _ := isProbabilityMeasure_uniformOn s.finite_toSet hs
  apply Measure.tendsto_quantile_nhdsGT_zero_of_ae_mem_finset _
    (s.ae_mem_image_map_uniformOn_finset f)
  exact s.map_uniformOn_finset_singleton_ne_zero f (min'_mem _ _)

open Filter Topology in
/-- Uniform quantiles tend to the largest attained label as the level increases to one. -/
theorem tendsto_quantile_map_uniformOn_finset_nhdsLT_one
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    Tendsto (fun u ↦ (((uniformOn (s : Set α)).map f).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ((s.image f).max' (hs.image f) : EReal)) := by
  let _ := isProbabilityMeasure_uniformOn s.finite_toSet hs
  apply Measure.tendsto_quantile_nhdsLT_one_of_ae_mem_finset _
    (s.ae_mem_image_map_uniformOn_finset f)
  exact s.map_uniformOn_finset_singleton_ne_zero f (max'_mem _ _)

end Finset
