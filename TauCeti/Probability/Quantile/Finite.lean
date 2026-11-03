/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Quantile
public import Mathlib.Data.Finset.Max

/-!
# Quantiles of finitely supported laws

For a real probability law carried by a finite set, every interior quantile is a member of that
set. It is the least support candidate whose cumulative mass reaches the level, so computing a
quantile reduces to a finite minimum. If every candidate has positive mass, the endpoint limits
are the smallest and largest candidates.
-/

public section

noncomputable section

open Filter ProbabilityTheory Set Topology

namespace MeasureTheory.Measure

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : Finset ℝ} {u x : ℝ}

/-- An interior quantile of a law carried by a finite set belongs to that set. The set may
include points of zero mass. -/
theorem quantile_mem_finset (hs : ∀ᵐ y ∂μ, y ∈ s) (hu : u ∈ Ioo 0 1) :
    μ.quantile u ∈ s := by
  classical
  let t := s.filter (· ≤ μ.quantile u)
  have ht : t.Nonempty := by
    by_contra h
    have he : μ.real (Iic (μ.quantile u)) = 0 := by
      rw [← measureReal_empty (μ := μ)]
      apply measureReal_congr
      filter_upwards [hs] with y hy
      apply propext
      simp only [mem_Iic, mem_empty_iff_false, iff_false]
      exact fun hle ↦ h ⟨y, Finset.mem_filter.mpr ⟨hy, hle⟩⟩
    have := le_cdf_quantile μ hu.2
    rw [cdf_eq_real, he] at this
    exact hu.1.not_ge this
  have ha : t.max' ht ≤ μ.quantile u := (Finset.mem_filter.mp (t.max'_mem ht)).2
  have he : cdf μ (t.max' ht) = cdf μ (μ.quantile u) := by
    simp only [cdf_eq_real]
    apply measureReal_congr
    filter_upwards [hs] with y hy
    apply propext
    exact ⟨fun h ↦ h.trans ha, fun h ↦ t.le_max' y (Finset.mem_filter.mpr ⟨hy, h⟩)⟩
  have hq : μ.quantile u = t.max' ht :=
    le_antisymm ((μ.quantile_le_iff hu.1 hu.2).2 (he.symm ▸ le_cdf_quantile μ hu.2)) ha
  rw [hq]
  exact (Finset.mem_filter.mp (t.max'_mem ht)).1

/-- The quantile is characterized by the least cumulative crossing among a finite set carrying
the law, including levels equal to a cumulative mass. -/
theorem quantile_eq_iff_of_ae_mem_finset (hs : ∀ᵐ y ∂μ, y ∈ s) (hu : u ∈ Ioo 0 1) :
    μ.quantile u = x ↔ IsLeast {y | y ∈ s ∧ u ≤ cdf μ y} x := by
  constructor
  · rintro rfl
    exact ⟨⟨μ.quantile_mem_finset hs hu, le_cdf_quantile μ hu.2⟩,
      fun _ hy ↦ (μ.quantile_le_iff hu.1 hu.2).2 hy.2⟩
  · intro hx
    exact le_antisymm ((μ.quantile_le_iff hu.1 hu.2).2 hx.1.2)
      (hx.2 ⟨μ.quantile_mem_finset hs hu, le_cdf_quantile μ hu.2⟩)

open Classical in
/-- The finite set of cumulative crossings at an interior level is nonempty. -/
theorem nonempty_filter_le_cdf (hs : ∀ᵐ y ∂μ, y ∈ s) (hu : u ∈ Ioo 0 1) :
    (s.filter fun y ↦ u ≤ cdf μ y).Nonempty :=
  ⟨μ.quantile u, Finset.mem_filter.mpr
    ⟨μ.quantile_mem_finset hs hu, le_cdf_quantile μ hu.2⟩⟩

open Classical in
/-- A finite minimum computes an interior quantile. -/
theorem quantile_eq_min'_of_ae_mem_finset (hs : ∀ᵐ y ∂μ, y ∈ s) (hu : u ∈ Ioo 0 1) :
    μ.quantile u = (s.filter fun y ↦ u ≤ cdf μ y).min'
      (μ.nonempty_filter_le_cdf hs hu) := by
  apply (μ.quantile_eq_iff_of_ae_mem_finset hs hu).2
  simpa only [Finset.coe_filter, Finset.mem_coe] using
    (s.filter fun y ↦ u ≤ cdf μ y).isLeast_min' (μ.nonempty_filter_le_cdf hs hu)

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

end MeasureTheory.Measure
