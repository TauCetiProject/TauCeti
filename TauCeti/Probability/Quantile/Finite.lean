/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Quantile
public import Mathlib.Data.Finset.Max
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of finitely supported real laws

A probability law on a finite type becomes a finitely supported real law after applying a
real-valued label map.  Its cumulative distribution function is the mass of the labels below the
threshold, and each interior quantile is the least distinct label at which that cumulative mass
reaches the requested level.  The formulation through the image of the label map automatically
collapses repeated labels.

## Main results

* `MeasureTheory.Measure.cdf_map_finite` computes the cumulative mass of a labelled finite law.
* `MeasureTheory.Measure.isLeast_quantile_map_finite` identifies an interior quantile as the
  least labelled cumulative crossing.
* `MeasureTheory.Measure.tendsto_quantile_map_finite_nhdsGT_zero` and
  `MeasureTheory.Measure.tendsto_quantile_map_finite_nhdsLT_one` give the endpoint limits from
  an extreme label of positive mass.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace MeasureTheory.Measure

variable {ι : Type*} [Finite ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-- The cdf of a real-labelled law on a finite type is the mass of the categories whose labels
are at most the threshold. -/
theorem cdf_map_finite (μ : Measure ι) [IsProbabilityMeasure μ] (label : ι → ℝ) (x : ℝ) :
    cdf (μ.map label) x = μ.real {i | label i ≤ x} := by
  rw [cdf_eq_real, Measure.real, Measure.map_apply (measurable_of_finite label) measurableSet_Iic]
  rfl

/-- An interior quantile of a real-labelled probability law on a finite type is the least
distinct supplied label whose cumulative mass reaches the requested level. -/
theorem isLeast_quantile_map_finite (μ : Measure ι) [IsProbabilityMeasure μ]
    [Nonempty ι] (label : ι → ℝ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    IsLeast {x : ℝ | x ∈ Set.range label ∧ u ≤ μ.real {i | label i ≤ x}}
      ((μ.map label).quantile u) := by
  let _ := Fintype.ofFinite ι
  classical
  let labels : Finset ℝ := Finset.univ.image label
  have hlabels : labels.Nonempty := Finset.univ_nonempty.image label
  let top := labels.max' hlabels
  have htop_mem : top ∈ labels := labels.max'_mem hlabels
  have htop_cross : u ≤ μ.real {i | label i ≤ top} := by
    have hset : {i | label i ≤ top} = (Set.univ : Set ι) := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact labels.le_max' (label i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    rw [hset, probReal_univ]
    exact hu.2.le
  let crossings := labels.filter fun x => u ≤ μ.real {i | label i ≤ x}
  have hcrossings : crossings.Nonempty :=
    ⟨top, Finset.mem_filter.2 ⟨htop_mem, htop_cross⟩⟩
  let q := crossings.min' hcrossings
  have hq_mem : q ∈ labels := (Finset.mem_filter.1 (crossings.min'_mem hcrossings)).1
  have hq_cross : u ≤ μ.real {i | label i ≤ q} :=
    (Finset.mem_filter.1 (crossings.min'_mem hcrossings)).2
  have hquantile_le : (μ.map label).quantile u ≤ q := by
    rw [quantile_le_iff _ hu.1 hu.2, cdf_map_finite]
    exact hq_cross
  have hq_le_quantile : q ≤ (μ.map label).quantile u := by
    by_contra h
    have hlevel := le_cdf_quantile (μ.map label) hu.2
    rw [cdf_map_finite] at hlevel
    let below := Finset.univ.filter fun i => label i ≤ (μ.map label).quantile u
    have hbelow : below.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hset : {i | label i ≤ (μ.map label).quantile u} = (∅ : Set ι) := by
        ext i
        have hi : i ∉ below := by simp [hempty]
        simpa [below] using hi
      rw [hset, measureReal_empty] at hlevel
      exact hu.1.not_ge hlevel
    let y := (below.image label).max' (hbelow.image label)
    have hy_mem_image : y ∈ below.image label := (below.image label).max'_mem (hbelow.image label)
    obtain ⟨i, hi, hiy⟩ := Finset.mem_image.1 hy_mem_image
    have hi_le : label i ≤ (μ.map label).quantile u := (Finset.mem_filter.1 hi).2
    have hy_le : y ≤ (μ.map label).quantile u := hiy ▸ hi_le
    have hpreimage : {j | label j ≤ y} = {j | label j ≤ (μ.map label).quantile u} := by
      ext j
      constructor
      · exact fun hj => hj.trans hy_le
      · intro hj
        exact (below.image label).le_max'
          (label j) (Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, rfl⟩)
    have hy_cross : u ≤ μ.real {j | label j ≤ y} := by rwa [hpreimage]
    have hy_labels : y ∈ labels := by
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hiy⟩
    have hy_crossings : y ∈ crossings := Finset.mem_filter.2 ⟨hy_labels, hy_cross⟩
    exact h ((crossings.min'_le y hy_crossings).trans hy_le)
  have hquantile_eq : (μ.map label).quantile u = q := le_antisymm hquantile_le hq_le_quantile
  rw [hquantile_eq]
  refine ⟨?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hq_mem
    exact ⟨⟨i, hi⟩, hq_cross⟩
  · intro x hx
    have hx_labels : x ∈ labels := Finset.mem_image.2 <| by
      obtain ⟨i, hi⟩ := hx.1
      exact ⟨i, Finset.mem_univ _, hi⟩
    exact crossings.min'_le x (Finset.mem_filter.2 ⟨hx_labels, hx.2⟩)

/-- Quantiles of a finite labelled law tend to a lowest label of positive mass as the level tends
to zero from above. -/
theorem tendsto_quantile_map_finite_nhdsGT_zero (μ : Measure ι) [IsProbabilityMeasure μ]
    (label : ι → ℝ) (a : ℝ) (hbound : ∀ᵐ i ∂μ, a ≤ label i)
    (hatom : 0 < μ.real {i | label i = a}) :
    Tendsto (fun u ↦ ((μ.map label).quantile u : EReal)) (𝓝[>] 0) (𝓝 (a : EReal)) := by
  apply tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos
  · exact (ae_map_iff (measurable_of_finite label).aemeasurable measurableSet_Ici).2 hbound
  · intro x hax
    rw [cdf_map_finite]
    exact hatom.trans_le (measureReal_mono fun i hi => hi.trans_le hax.le)

/-- Quantiles of a finite labelled law tend to a highest label of positive mass as the level tends
to one from below. -/
theorem tendsto_quantile_map_finite_nhdsLT_one (μ : Measure ι) [IsProbabilityMeasure μ]
    (label : ι → ℝ) (b : ℝ) (hbound : ∀ᵐ i ∂μ, label i ≤ b)
    (hatom : 0 < μ.real {i | label i = b}) :
    Tendsto (fun u ↦ ((μ.map label).quantile u : EReal)) (𝓝[<] 1) (𝓝 (b : EReal)) := by
  apply tendsto_quantile_nhdsLT_one_of_ae_le_of_cdf_lt_one
  · exact (ae_map_iff (measurable_of_finite label).aemeasurable measurableSet_Iic).2 hbound
  · intro x hxb
    rw [cdf_map_finite]
    have hsubset : {i | label i ≤ x} ⊆ ({i | label i = b} : Set ι)ᶜ := by
      intro i hi
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
      exact ne_of_lt (hi.trans_lt hxb)
    calc
      μ.real {i | label i ≤ x} ≤ μ.real ({i | label i = b} : Set ι)ᶜ :=
        measureReal_mono hsubset
      _ = 1 - μ.real {i | label i = b} := probReal_compl_eq_one_sub .of_discrete
      _ < 1 := sub_lt_self 1 hatom

end MeasureTheory.Measure
