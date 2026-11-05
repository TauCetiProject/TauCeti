/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Quantile
import TauCeti.MeasureTheory.Measure.FiniteMeasure.Basic

/-!
# Quantiles of finite labelled laws

A probability measure on a finite type becomes a finitely supported real law after assigning a
real label to every outcome. This file characterizes its quantiles directly from the mass below
and at a proposed label. The characterization automatically sorts the distinct labels and
aggregates outcomes carrying equal labels.

## Main results

* `MeasureTheory.Measure.quantile_map_finite_eq_iff` characterizes the quantile by the strict
  cumulative crossing below a label and the weak crossing at it;
* `MeasureTheory.Measure.tendsto_quantile_map_finite_nhdsGT_zero` and
  `MeasureTheory.Measure.tendsto_quantile_map_finite_nhdsLT_one` give the endpoint limits at the
  least and greatest labels of positive mass.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace MeasureTheory.Measure

variable {I : Type*} [Finite I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- A real number is the interior quantile of a probability measure on a finite labelled type
exactly when the level lies strictly above the mass below that label and at most the mass at or
below it. In particular, the strict inequality forces the answer to be one of the supplied
labels with positive total mass. -/
@[simp]
theorem quantile_map_finite_eq_iff (μ : Measure I) [IsProbabilityMeasure μ] (label : I → ℝ)
    {u x : ℝ} (hu : u ∈ Ioo 0 1) :
    (μ.map label).quantile u = x ↔
      μ.real (label ⁻¹' Iio x) < u ∧ u ≤ μ.real (label ⁻¹' Iic x) := by
  classical
  let _ := Fintype.ofFinite I
  constructor
  · intro hquantile
    subst x
    constructor
    · by_contra! hleft
      let labelsBelow := (Finset.univ.image label).filter (· < (μ.map label).quantile u)
      have hlabelsBelow : labelsBelow.Nonempty := by
        by_contra hempty
        have hpreimage : label ⁻¹' Iio ((μ.map label).quantile u) = ∅ := by
          ext i
          simp only [mem_preimage, mem_Iio, Set.mem_empty_iff_false]
          exact ⟨fun hi ↦ hempty ⟨label i, by simp [labelsBelow, hi]⟩, False.elim⟩
        rw [hpreimage, measureReal_empty] at hleft
        exact (not_lt_of_ge hleft) hu.1
      let y := labelsBelow.max' hlabelsBelow
      have hylt : y < (μ.map label).quantile u :=
        (Finset.mem_filter.mp (labelsBelow.max'_mem hlabelsBelow)).2
      have hpreimage : label ⁻¹' Iic y = label ⁻¹' Iio ((μ.map label).quantile u) := by
        ext i
        simp only [mem_preimage, mem_Iic, mem_Iio]
        constructor
        · exact fun hi ↦ hi.trans_lt hylt
        · intro hi
          exact Finset.le_max' labelsBelow (label i) (by simp [labelsBelow, hi])
      have hlevel : u ≤ cdf (μ.map label) y := by
        rw [cdf_map _ label (measurable_of_finite label).aemeasurable, hpreimage]
        exact hleft
      have hquantile_le : (μ.map label).quantile u ≤ y :=
        (quantile_le_iff _ hu.1 hu.2).2 hlevel
      exact (not_lt_of_ge hquantile_le) hylt
    · have hlevel := le_cdf_quantile (μ.map label) hu.2
      rwa [cdf_map _ label (measurable_of_finite label).aemeasurable] at hlevel
  · rintro ⟨hleft, hright⟩
    apply le_antisymm
    · rw [quantile_le_iff _ hu.1 hu.2, cdf_map _ label (measurable_of_finite label).aemeasurable]
      exact hright
    · by_contra! hquantile_lt
      have hcdf := le_cdf_quantile (μ.map label) hu.2
      have hmono : cdf (μ.map label) ((μ.map label).quantile u) ≤
          μ.real (label ⁻¹' Iio x) := by
        rw [cdf_map _ label (measurable_of_finite label).aemeasurable]
        exact measureReal_mono fun i hi ↦ hi.trans_lt hquantile_lt
      exact (not_lt_of_ge (hcdf.trans hmono)) hleft

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
  apply (quantile_map_finite_eq_iff μ label ⟨hu.1, hu.2.trans_le (min_le_right _ _)⟩).2
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
  apply (quantile_map_finite_eq_iff μ label ⟨hu_pos, hu.2⟩).2
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
