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

* `MeasureTheory.Measure.cdf_map_eq_measureReal` computes the cumulative mass of a mapped law.
* `MeasureTheory.Measure.isLeast_quantile_map_finite` identifies an interior quantile as the
  least labelled cumulative crossing.
* `MeasureTheory.Measure.tendsto_quantile_map_nhdsGT_zero` and
  `MeasureTheory.Measure.tendsto_quantile_map_nhdsLT_one` give the endpoint limits from
  an extreme label of positive mass.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- The cdf of a mapped probability law is the mass of the points whose images are at most the
threshold. -/
theorem cdf_map_eq_measureReal (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (x : ℝ) : cdf (μ.map f) x = μ.real {a | f a ≤ x} := by
  rw [cdf_eq_real, map_measureReal_apply hf measurableSet_Iic]
  -- The preimage of `Iic x` is definitionally the set of points mapped below `x`.
  rfl

variable {ι : Type*} [Finite ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-- Some supplied label at or below an interior quantile already has cumulative mass at least
the requested level. -/
theorem exists_label_le_quantile_map_finite (μ : Measure ι) [IsProbabilityMeasure μ]
    (label : ι → ℝ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ∃ y ∈ Set.range label,
      y ≤ (μ.map label).quantile u ∧ u ≤ μ.real {i | label i ≤ y} := by
  let _ := Fintype.ofFinite ι
  let _ := nonempty_of_isProbabilityMeasure μ
  classical
  have hlevel := le_cdf_quantile (μ.map label) hu.2
  rw [cdf_map_eq_measureReal _ (measurable_of_finite label)] at hlevel
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
  exact ⟨y, ⟨i, hiy⟩, hy_le, hy_cross⟩

/-- An interior quantile of a real-labelled probability law on a finite type is the least
distinct supplied label whose cumulative mass reaches the requested level. -/
theorem isLeast_quantile_map_finite (μ : Measure ι) [IsProbabilityMeasure μ]
    (label : ι → ℝ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    IsLeast {x : ℝ | x ∈ Set.range label ∧ u ≤ μ.real {i | label i ≤ x}}
      ((μ.map label).quantile u) := by
  let _ := Fintype.ofFinite ι
  let _ := nonempty_of_isProbabilityMeasure μ
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
    rw [quantile_le_iff _ hu.1 hu.2,
      cdf_map_eq_measureReal _ (measurable_of_finite label)]
    exact hq_cross
  have hq_le_quantile : q ≤ (μ.map label).quantile u := by
    obtain ⟨y, ⟨i, hiy⟩, hy_le, hy_cross⟩ :=
      exists_label_le_quantile_map_finite μ label hu
    have hy_labels : y ∈ labels := Finset.mem_image.2 ⟨i, Finset.mem_univ _, hiy⟩
    have hy_crossings : y ∈ crossings := Finset.mem_filter.2 ⟨hy_labels, hy_cross⟩
    exact (crossings.min'_le y hy_crossings).trans hy_le
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

/-- Quantiles of a mapped law tend to a lowest image value of positive mass as the level tends to
zero from above. -/
theorem tendsto_quantile_map_nhdsGT_zero (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Measurable f) (a : ℝ) (hbound : ∀ᵐ x ∂μ, a ≤ f x)
    (hatom : 0 < μ.real {x | f x = a}) :
    Tendsto (fun u ↦ ((μ.map f).quantile u : EReal)) (𝓝[>] 0) (𝓝 (a : EReal)) := by
  apply tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos
  · exact (ae_map_iff hf.aemeasurable measurableSet_Ici).2 hbound
  · intro x hax
    rw [cdf_map_eq_measureReal _ hf]
    exact hatom.trans_le (measureReal_mono fun y hy => hy.trans_le hax.le)

/-- Quantiles of a mapped law tend to a highest image value of positive mass as the level tends to
one from below. -/
theorem tendsto_quantile_map_nhdsLT_one (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Measurable f) (b : ℝ) (hbound : ∀ᵐ x ∂μ, f x ≤ b)
    (hatom : 0 < μ.real {x | f x = b}) :
    Tendsto (fun u ↦ ((μ.map f).quantile u : EReal)) (𝓝[<] 1) (𝓝 (b : EReal)) := by
  apply tendsto_quantile_nhdsLT_one_of_ae_le_of_cdf_lt_one
  · exact (ae_map_iff hf.aemeasurable measurableSet_Iic).2 hbound
  · intro x hxb
    rw [cdf_map_eq_measureReal _ hf]
    have hsubset : {y | f y ≤ x} ⊆ ({y | f y = b} : Set α)ᶜ := by
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
      exact ne_of_lt (hy.trans_lt hxb)
    calc
      μ.real {y | f y ≤ x} ≤ μ.real ({y | f y = b} : Set α)ᶜ :=
        measureReal_mono hsubset
      _ = 1 - μ.real {y | f y = b} :=
        probReal_compl_eq_one_sub (hf (measurableSet_singleton b))
      _ < 1 := sub_lt_self 1 hatom

end MeasureTheory.Measure
