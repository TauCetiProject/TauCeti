/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Quantile
public import Mathlib.Data.Finset.Max
import TauCeti.MeasureTheory.Measure.FiniteMeasure.Basic

/-!
# Quantiles of finite labelled laws

A probability measure on a finite type becomes a finitely supported real law after assigning a
real label to every outcome. This file characterizes its quantiles directly from the mass below
and at a proposed label. The characterization automatically sorts the distinct labels and
aggregates outcomes carrying equal labels.

For any real probability law carried by a finite set, a quantile at a level in `(0, 1]`
belongs to that set and is its least cumulative crossing, the endpoint level `1` included. A
finite minimum therefore computes it. The lower (upper) endpoint limit is the smallest (largest)
candidate whenever that candidate has positive mass.

## Main results

* `MeasureTheory.Measure.quantile_mem_finset` places a quantile at a level in `(0, 1]` in a
  carrying set, and `MeasureTheory.Measure.quantile_eq_min'_of_ae_mem_finset` computes it by a
  finite minimum over that set;
* `MeasureTheory.Measure.quantile_eq_iff_measureReal_Iio_lt_of_ae_mem_finset` characterizes it by
  the strict cumulative crossing below a point and the weak crossing at it;
* `MeasureTheory.Measure.tendsto_quantile_nhdsGT_zero_of_ae_mem_finset` and
  `MeasureTheory.Measure.tendsto_quantile_nhdsLT_one_of_ae_mem_finset` give its endpoint limits;

* `MeasureTheory.Measure.quantile_map_finite_eq_iff` is its labelled form, characterizing the
  quantile at a level in `(0, 1]` by the mass below and at a label;
* `MeasureTheory.Measure.tendsto_quantile_map_finite_nhdsGT_zero` and
  `MeasureTheory.Measure.tendsto_quantile_map_finite_nhdsLT_one` give the endpoint limits at the
  least and greatest labels of positive mass.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace MeasureTheory.Measure

section FiniteSupport

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : Finset ℝ} {u x : ℝ}

/-- A law carried by a finite set reaches full cumulative mass at the largest point of that set,
so every level at most `1` is reached. -/
theorem nonempty_setOf_le_cdf_of_ae_mem_finset (hs : ∀ᵐ y ∂μ, y ∈ s) (hu : u ≤ 1) :
    {x : ℝ | u ≤ cdf μ x}.Nonempty := by
  obtain ⟨y, hy⟩ := hs.exists
  exact μ.nonempty_setOf_le_cdf_of_ae_le (b := s.max' ⟨y, hy⟩)
    (hs.mono fun z hz ↦ s.le_max' z hz) hu

/-- A quantile at a level in `(0, 1]` of a law carried by a finite set belongs to that set,
including the endpoint level `1`. The set may include points of zero mass. -/
theorem quantile_mem_finset (hs : ∀ᵐ y ∂μ, y ∈ s) (hu : u ∈ Ioc 0 1) :
    μ.quantile u ∈ s := by
  classical
  have hreach := μ.nonempty_setOf_le_cdf_of_ae_mem_finset hs hu.2
  let t := s.filter (· ≤ μ.quantile u)
  have ht : t.Nonempty := by
    by_contra h
    have he : μ.real (Iic (μ.quantile u)) = 0 := by
      rw [← measureReal_empty (μ := μ)]
      apply measureReal_congr
      filter_upwards [hs] with y hy
      simp only [mem_Iic, mem_empty_iff_false, iff_false]
      exact fun hle ↦ h ⟨y, Finset.mem_filter.mpr ⟨hy, hle⟩⟩
    have := le_cdf_quantile_of_nonempty μ hreach
    rw [cdf_eq_real, he] at this
    exact hu.1.not_ge this
  have ha : t.max' ht ≤ μ.quantile u := (Finset.mem_filter.mp (t.max'_mem ht)).2
  have he : cdf μ (t.max' ht) = cdf μ (μ.quantile u) := by
    simp only [cdf_eq_real]
    apply measureReal_congr
    filter_upwards [hs] with y hy
    exact ⟨fun h ↦ h.trans ha, fun h ↦ t.le_max' y (Finset.mem_filter.mpr ⟨hy, h⟩)⟩
  have hq : μ.quantile u = t.max' ht :=
    le_antisymm ((μ.quantile_le_iff_of_nonempty hu.1 hreach).2
      (he.symm ▸ le_cdf_quantile_of_nonempty μ hreach)) ha
  rw [hq]
  exact (Finset.mem_filter.mp (t.max'_mem ht)).1

/-- At a level in `(0, 1]`, the endpoint level `1` included, the quantile is characterized by the
least cumulative crossing among a finite set carrying the law, including levels equal to a
cumulative mass. -/
theorem quantile_eq_iff_of_ae_mem_finset (hs : ∀ᵐ y ∂μ, y ∈ s) (hu : u ∈ Ioc 0 1) :
    μ.quantile u = x ↔ IsLeast {y | y ∈ s ∧ u ≤ cdf μ y} x := by
  have hreach := μ.nonempty_setOf_le_cdf_of_ae_mem_finset hs hu.2
  constructor
  · rintro rfl
    exact ⟨⟨μ.quantile_mem_finset hs hu, le_cdf_quantile_of_nonempty μ hreach⟩,
      fun _ hy ↦ (μ.quantile_le_iff_of_nonempty hu.1 hreach).2 hy.2⟩
  · intro hx
    exact le_antisymm ((μ.quantile_le_iff_of_nonempty hu.1 hreach).2 hx.1.2)
      (hx.2 ⟨μ.quantile_mem_finset hs hu, le_cdf_quantile_of_nonempty μ hreach⟩)

open Classical in
/-- The finite set of cumulative crossings at a level at most `1` is nonempty: it contains the
largest point of the carrying set, where the law reaches full cumulative mass. -/
theorem nonempty_filter_le_cdf (hs : ∀ᵐ y ∂μ, y ∈ s) (hu : u ≤ 1) :
    (s.filter fun y ↦ u ≤ cdf μ y).Nonempty := by
  obtain ⟨y, hy⟩ := hs.exists
  exact ⟨s.max' ⟨y, hy⟩, Finset.mem_filter.mpr ⟨s.max'_mem _,
    hu.trans_eq (cdf_eq_one_of_ae_le μ (hs.mono fun z hz ↦ s.le_max' z hz)).symm⟩⟩

open Classical in
/-- A finite minimum computes the quantile at a level in `(0, 1]`, the endpoint level `1`
included. -/
theorem quantile_eq_min'_of_ae_mem_finset (hs : ∀ᵐ y ∂μ, y ∈ s) (hu : u ∈ Ioc 0 1) :
    μ.quantile u = (s.filter fun y ↦ u ≤ cdf μ y).min'
      (μ.nonempty_filter_le_cdf hs hu.2) := by
  apply (μ.quantile_eq_iff_of_ae_mem_finset hs hu).2
  simpa only [Finset.coe_filter, Finset.mem_coe] using
    (s.filter fun y ↦ u ≤ cdf μ y).isLeast_min' (μ.nonempty_filter_le_cdf hs hu.2)

/-- At a level in `(0, 1]`, the endpoint level `1` included, the quantile of a law carried by a
finite set is the point strictly below which the mass is less than the level and at which the
cumulative distribution function reaches it. Unlike for a general law, the strict crossing below
the quantile holds because the mass below it is the cumulative mass at the largest point of the
carrying set lying below it. -/
theorem quantile_eq_iff_measureReal_Iio_lt_of_ae_mem_finset (hs : ∀ᵐ y ∂μ, y ∈ s)
    (hu : u ∈ Ioc 0 1) : μ.quantile u = x ↔ μ.real (Iio x) < u ∧ u ≤ cdf μ x := by
  classical
  have hreach := μ.nonempty_setOf_le_cdf_of_ae_mem_finset hs hu.2
  constructor
  · rintro rfl
    refine ⟨?_, le_cdf_quantile_of_nonempty μ hreach⟩
    by_contra! hleft
    let t := s.filter (· < μ.quantile u)
    have ht : t.Nonempty := by
      by_contra h
      have he : μ.real (Iio (μ.quantile u)) = 0 := by
        rw [← measureReal_empty (μ := μ)]
        apply measureReal_congr
        filter_upwards [hs] with y hy
        simp only [mem_Iio, mem_empty_iff_false, iff_false]
        exact fun hlt ↦ h ⟨y, Finset.mem_filter.mpr ⟨hy, hlt⟩⟩
      rw [he] at hleft
      exact hu.1.not_ge hleft
    have hlt : t.max' ht < μ.quantile u := (Finset.mem_filter.mp (t.max'_mem ht)).2
    have he : cdf μ (t.max' ht) = μ.real (Iio (μ.quantile u)) := by
      rw [cdf_eq_real]
      apply measureReal_congr
      filter_upwards [hs] with y hy
      exact ⟨fun h ↦ h.trans_lt hlt, fun h ↦ t.le_max' y (Finset.mem_filter.mpr ⟨hy, h⟩)⟩
    rw [← he] at hleft
    exact hlt.not_ge ((μ.quantile_le_iff_of_nonempty hu.1 hreach).2 hleft)
  · rintro ⟨hleft, hright⟩
    refine le_antisymm ((μ.quantile_le_iff_of_nonempty hu.1 hreach).2 hright) ?_
    by_contra! hlt
    have hmono : cdf μ (μ.quantile u) ≤ μ.real (Iio x) := by
      rw [cdf_eq_real]
      exact measureReal_mono fun y hy ↦ lt_of_le_of_lt hy hlt
    exact hleft.not_ge ((le_cdf_quantile_of_nonempty μ hreach).trans hmono)

/-- For a finite carrying set whose smallest point has positive mass, the lower endpoint
limit is that point. -/
theorem tendsto_quantile_nhdsGT_zero_of_ae_mem_finset (hs : ∀ᵐ y ∂μ, y ∈ s)
    (hne : s.Nonempty) (hpos : μ {s.min' hne} ≠ 0) :
    Tendsto (fun u ↦ (μ.quantile u : EReal)) (𝓝[>] 0) (𝓝 (s.min' hne : EReal)) := by
  apply μ.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos
  · filter_upwards [hs] with y hy using s.min'_le y hy
  · intro y hy
    rw [cdf_eq_real]
    exact (lt_of_le_of_ne measureReal_nonneg
      ((measureReal_ne_zero_iff).2 hpos).symm).trans_le
      (measureReal_mono (singleton_subset_iff.mpr hy.le))

/-- For a finite carrying set whose largest point has positive mass, the upper endpoint
limit is that point. -/
theorem tendsto_quantile_nhdsLT_one_of_ae_mem_finset (hs : ∀ᵐ y ∂μ, y ∈ s)
    (hne : s.Nonempty) (hpos : μ {s.max' hne} ≠ 0) :
    Tendsto (fun u ↦ (μ.quantile u : EReal)) (𝓝[<] 1) (𝓝 (s.max' hne : EReal)) := by
  apply μ.tendsto_quantile_nhdsLT_one_of_ae_le_of_cdf_lt_one
  · filter_upwards [hs] with y hy using s.le_max' y hy
  · intro y hy
    have hp : 0 < μ.real {s.max' hne} :=
      lt_of_le_of_ne measureReal_nonneg ((measureReal_ne_zero_iff).2 hpos).symm
    have hle : μ.real {s.max' hne} ≤ 1 - cdf μ y := by
      rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic]
      exact measureReal_mono (singleton_subset_iff.mpr (not_le.mpr hy))
    linarith

end FiniteSupport

variable {I : Type*} [Finite I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- A real number is the quantile at a level in `(0, 1]` of a probability measure on a finite
labelled type exactly when the level lies strictly above the mass below that label and at most the
mass at or below it. The endpoint level `1` is included. In particular, the strict inequality
forces the answer to be one of the supplied labels with positive total mass. -/
@[simp]
theorem quantile_map_finite_eq_iff (μ : Measure I) [IsProbabilityMeasure μ] (label : I → ℝ)
    {u x : ℝ} (hu : u ∈ Ioc 0 1) :
    (μ.map label).quantile u = x ↔
      μ.real (label ⁻¹' Iio x) < u ∧ u ≤ μ.real (label ⁻¹' Iic x) := by
  classical
  let _ := Fintype.ofFinite I
  have hlabel : Measurable label := measurable_of_finite label
  rw [(μ.map label).quantile_eq_iff_measureReal_Iio_lt_of_ae_mem_finset
      (s := Finset.univ.image label) ((ae_map_iff hlabel.aemeasurable
        (Finset.univ.image label).measurableSet).2
          (ae_of_all _ fun i ↦ Finset.mem_image_of_mem label (Finset.mem_univ i))) hu,
    map_measureReal_apply hlabel measurableSet_Iio, cdf_map _ label hlabel.aemeasurable]

/-- For a finite labelled law, quantiles tend to any least label of positive mass as the level
tends to zero from above. Labels of zero mass do not affect the endpoint. -/
theorem tendsto_quantile_map_finite_nhdsGT_zero (μ : Measure I) [IsProbabilityMeasure μ]
    (label : I → ℝ) (i : I) (hi : 0 < μ.real {i})
    (hmin : ∀ j, 0 < μ.real {j} → label i ≤ label j) :
    Tendsto (μ.map label).quantile (𝓝[>] 0) (𝓝 (label i)) := by
  let _ := Fintype.ofFinite I
  classical
  have hleft_zero : μ.real (label ⁻¹' Iio (label i)) = 0 := by
    let below := Finset.univ.filter fun j ↦ label j < label i
    have hpreimage : label ⁻¹' Iio (label i) = (below : Set I) := by
      ext j
      simp [below]
    rw [hpreimage]
    apply measureReal_finset_eq_zero μ below
    intro j hj
    have hjlt : label j < label i := (Finset.mem_filter.mp hj).2
    have hjnonpos : ¬0 < μ.real {j} := fun hjpos ↦ (hmin j hjpos).not_gt hjlt
    exact le_antisymm (not_lt.mp hjnonpos) measureReal_nonneg
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min hi one_pos)] with u hu
  symm
  apply (quantile_map_finite_eq_iff μ label ⟨hu.1, (hu.2.trans_le (min_le_right _ _)).le⟩).2
  constructor
  · rw [hleft_zero]
    exact hu.1
  · apply (hu.2.trans_le (min_le_left _ _)).le.trans
    apply measureReal_mono _ (by finiteness)
    intro j hj
    rw [Set.mem_singleton_iff.mp hj]
    simp

omit [MeasurableSingletonClass I] in
/-- For a finite labelled law, quantiles tend to any greatest label of positive mass as the
level tends to one from below. Labels of zero mass do not affect the endpoint. -/
theorem tendsto_quantile_map_finite_nhdsLT_one (μ : Measure I) [IsProbabilityMeasure μ]
    [MeasurableSingletonClass I]
    (label : I → ℝ) (i : I) (hi : 0 < μ.real {i})
    (hmax : ∀ j, 0 < μ.real {j} → label j ≤ label i) :
    Tendsto (μ.map label).quantile (𝓝[<] 1) (𝓝 (label i)) := by
  let _ := Fintype.ofFinite I
  classical
  have hi_le_one : μ.real {i} ≤ 1 := by
    calc
      μ.real {i} ≤ μ.real univ := measureReal_mono (subset_univ _)
      _ = 1 := probReal_univ
  have hright_full : μ.real (label ⁻¹' Iic (label i)) = 1 := by
    let above := Finset.univ.filter fun j ↦ label i < label j
    have hcomplement : (label ⁻¹' Iic (label i))ᶜ = (above : Set I) := by
      ext j
      simp [above]
    have habove_zero : μ.real (above : Set I) = 0 := by
      apply measureReal_finset_eq_zero μ above
      intro j hj
      have hjgt : label i < label j := (Finset.mem_filter.mp hj).2
      have hjnonpos : ¬0 < μ.real {j} := fun hjpos ↦ (hmax j hjpos).not_gt hjgt
      exact le_antisymm (not_lt.mp hjnonpos) measureReal_nonneg
    have hcomplement_mass : μ.real (label ⁻¹' Iic (label i))ᶜ =
        1 - μ.real (label ⁻¹' Iic (label i)) :=
      probReal_compl_eq_one_sub (μ := μ)
        ((measurable_of_finite label) measurableSet_Iic)
    rw [hcomplement, habove_zero] at hcomplement_mass
    linarith
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (sub_lt_self 1 hi)] with u hu
  have hu_pos : 0 < u := (sub_nonneg.mpr hi_le_one).trans_lt hu.1
  symm
  apply (quantile_map_finite_eq_iff μ label ⟨hu_pos, hu.2.le⟩).2
  constructor
  · calc
      μ.real (label ⁻¹' Iio (label i)) ≤ μ.real ({i} : Set I)ᶜ :=
        measureReal_mono fun j hj ↦ by
          simp only [mem_compl_iff, mem_singleton_iff]
          intro hji
          subst j
          exact (lt_irrefl _ hj)
      _ = 1 - μ.real {i} := probReal_compl_eq_one_sub (MeasurableSet.singleton i)
      _ < u := hu.1
  · rw [hright_full]
    exact hu.2.le

end MeasureTheory.Measure
