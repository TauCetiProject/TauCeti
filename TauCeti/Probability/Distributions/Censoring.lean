/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.ProjIcc
public import TauCeti.Probability.Moments.Basic
public import TauCeti.Probability.Quantile

/-!
# Censoring real probability laws to a bounded interval

Projecting a real random variable onto a closed interval replaces its lower and upper tails by
atoms at the corresponding endpoints and leaves the variable unchanged in the interval's
interior.  This file describes that pushforward through Mathlib's `Set.projIcc`: it gives the
endpoint/interior decomposition, the cumulative distribution function, and the quantile formula.

Since the projected variable is bounded, all of its natural moments and exponential moments are
integrable.  The natural-moment formula below separates the two endpoint atoms from the unchanged
interior contribution.

## Main results

* `MeasureTheory.Measure.map_coe_projIcc` decomposes the censored law into its two endpoint atoms
  and its unchanged restriction to the open interval;
* `MeasureTheory.Measure.cdf_map_coe_projIcc` computes its cumulative distribution function;
* `MeasureTheory.Measure.quantile_map_coe_projIcc` says that censoring commutes with interior
  quantiles;
* `MeasureTheory.Measure.integral_pow_map_coe_projIcc` decomposes every natural moment;
* `MeasureTheory.Measure.integrableExpSet_id_map_coe_projIcc` shows that the exponential-
  integrability domain is all of `ℝ`.
-/

public section

noncomputable section

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable (μ : Measure ℝ)

local notation "clip[" l ", " r "; " h "]" =>
  (fun x : ℝ ↦ (Set.projIcc l r h x : ℝ))

private theorem measurable_clip {l r : ℝ} (h : l ≤ r) : Measurable clip[l, r; h] := by
  fun_prop

/-- Projecting a measure onto `[l, r]` moves the lower and upper tails to atoms at the endpoints
and leaves the restriction to `(l, r)` unchanged. -/
theorem map_coe_projIcc {l r : ℝ} (hlr : l < r) :
    μ.map clip[l, r; hlr.le] =
      μ (Iic l) • Measure.dirac l + μ.restrict (Ioo l r) + μ (Ici r) • Measure.dirac r := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_clip hlr.le) hs]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs,
    Measure.restrict_apply hs, smul_eq_mul]
  have hpreimage :
      clip[l, r; hlr.le] ⁻¹' s =
        (if l ∈ s then Iic l else ∅) ∪ (s ∩ Ioo l r) ∪ (if r ∈ s then Ici r else ∅) := by
    by_cases hls : l ∈ s <;> by_cases hrs : r ∈ s <;>
      ext x <;> simp [hls, hrs, Set.coe_projIcc] <;> grind
  rw [hpreimage]
  rw [measure_union]
  · rw [measure_union]
    · by_cases hls : l ∈ s <;> by_cases hrs : r ∈ s <;> simp [hls, hrs]
    · by_cases hls : l ∈ s
      · apply Set.disjoint_left.2
        intro x hx hx'
        rw [ite_eq_left hls] at hx
        exact (not_lt_of_ge hx) hx'.2.1
      · simp [hls]
    · exact hs.inter measurableSet_Ioo
  · by_cases hrs : r ∈ s
    · apply Set.disjoint_left.2
      intro x hx hx'
      rw [ite_eq_left hrs] at hx'
      rcases hx with hx | hx
      · by_cases hls : l ∈ s
        · rw [ite_eq_left hls] at hx
          exact (not_lt_of_ge hx') (hx.trans_lt hlr)
        · rw [ite_eq_right hls] at hx
          exact hx.elim
      · exact (not_lt_of_ge hx') hx.2.2
    · simp [hrs]
  · by_cases hrs : r ∈ s
    · simp [hrs]
    · simp [hrs]

/-- The cdf of a law projected onto `[l, r]` is zero below `l`, agrees with the original cdf on
`[l, r)`, and is one from `r` onwards. -/
@[simp] theorem cdf_map_coe_projIcc [IsProbabilityMeasure μ] {l r : ℝ} (hlr : l ≤ r) (x : ℝ) :
    cdf (μ.map clip[l, r; hlr]) x =
      if x < l then 0 else if x < r then cdf μ x else 1 := by
  rw [cdf_eq_real, Measure.real, Measure.map_apply (measurable_clip hlr) measurableSet_Iic]
  by_cases hxl : x < l
  · rw [ite_eq_left hxl]
    have hpre : clip[l, r; hlr] ⁻¹' Iic x = ∅ := by
      ext y
      simp only [mem_preimage, mem_Iic, Set.coe_projIcc, mem_empty_iff_false, iff_false]
      grind
    rw [hpre, measure_empty, ENNReal.toReal_zero]
  · rw [ite_eq_right hxl]
    by_cases hxr : x < r
    · rw [ite_eq_left hxr]
      rw [cdf_eq_real, Measure.real]
      have hpre : clip[l, r; hlr] ⁻¹' Iic x = Iic x := by
        ext y
        simp only [mem_preimage, mem_Iic, Set.coe_projIcc]
        grind
      rw [hpre]
    · rw [ite_eq_right hxr]
      have hpre : clip[l, r; hlr] ⁻¹' Iic x = Set.univ := by
        ext y
        simp only [mem_preimage, mem_Iic, Set.coe_projIcc, mem_univ, iff_true]
        grind
      rw [hpre, measure_univ]
      simp

/-- For an interior probability level, the quantile of a law projected onto `[l, r]` is the
projection of the original quantile. -/
@[simp] theorem quantile_map_coe_projIcc [IsProbabilityMeasure μ] {l r u : ℝ} (hlr : l ≤ r)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (μ.map clip[l, r; hlr]).quantile u = clip[l, r; hlr] (μ.quantile u) := by
  let ν := μ.map clip[l, r; hlr]
  have hlevel (x : ℝ) :
      clip[l, r; hlr] (μ.quantile u) ≤ x ↔ u ≤ cdf ν x := by
    rw [cdf_map_coe_projIcc μ hlr]
    by_cases hxl : x < l
    · rw [ite_eq_left hxl]
      constructor <;> intro h
      · exact ((not_le_of_gt hxl) ((Set.projIcc l r hlr _).property.1.trans h)).elim
      · linarith [hu.1]
    · rw [ite_eq_right hxl]
      by_cases hxr : x < r
      · rw [ite_eq_left hxr]
        rw [← quantile_le_iff μ hu.1 hu.2]
        simp only [Set.coe_projIcc]
        grind
      · rw [ite_eq_right hxr]
        constructor
        · exact fun _ ↦ hu.2.le
        · intro _
          exact (Set.projIcc l r hlr _).property.2.trans (not_lt.mp hxr)
  apply le_antisymm
  · exact (quantile_le_iff ν hu.1 hu.2).2 ((hlevel _).1 le_rfl)
  · exact (hlevel _).2 ((quantile_le_iff ν hu.1 hu.2).1 le_rfl)

/-- Every natural power is integrable under a law projected onto a bounded interval. -/
theorem integrable_pow_map_coe_projIcc [IsFiniteMeasure μ] {l r : ℝ} (hlr : l ≤ r) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (μ.map clip[l, r; hlr]) := by
  rw [integrable_map_measure (by fun_prop) (measurable_clip hlr).aemeasurable]
  refine Integrable.of_bound (by fun_prop) (max |l| |r| ^ n) ?_
  filter_upwards with x
  rw [Function.comp_apply, Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_le_max_abs_abs (Set.projIcc l r hlr x).property.1
      (Set.projIcc l r hlr x).property.2) n

/-- Every natural moment of a projected law is the sum of the two endpoint contributions and the
unchanged contribution from the interval interior. -/
theorem integral_pow_map_coe_projIcc [IsFiniteMeasure μ] {l r : ℝ} (hlr : l < r) (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂(μ.map clip[l, r; hlr.le]) =
      μ.real (Iic l) * l ^ n + ∫ x in Ioo l r, x ^ n ∂μ + μ.real (Ici r) * r ^ n := by
  have hint := integrable_pow_map_coe_projIcc μ hlr.le n
  rw [map_coe_projIcc μ hlr, integrable_add_measure, integrable_add_measure] at hint
  rw [map_coe_projIcc μ hlr, integral_add_measure (hint.1.1.add_measure hint.1.2) hint.2,
    integral_add_measure hint.1.1 hint.1.2]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul, Measure.real]

/-- The mean of a projected law splits into its lower endpoint, unchanged interior, and upper
endpoint contributions. -/
theorem integral_id_map_coe_projIcc [IsFiniteMeasure μ] {l r : ℝ} (hlr : l < r) :
    ∫ x : ℝ, x ∂(μ.map clip[l, r; hlr.le]) =
      μ.real (Iic l) * l + ∫ x in Ioo l r, x ∂μ + μ.real (Ici r) * r := by
  simpa using integral_pow_map_coe_projIcc μ hlr 1

/-- The second moment of a projected law splits into its lower endpoint, unchanged interior, and
upper endpoint contributions. -/
theorem integral_sq_map_coe_projIcc [IsFiniteMeasure μ] {l r : ℝ} (hlr : l < r) :
    ∫ x : ℝ, x ^ 2 ∂(μ.map clip[l, r; hlr.le]) =
      μ.real (Iic l) * l ^ 2 + ∫ x in Ioo l r, x ^ 2 ∂μ + μ.real (Ici r) * r ^ 2 :=
  integral_pow_map_coe_projIcc μ hlr 2

/-- Every exponential moment is integrable under a law projected onto a bounded interval. -/
theorem integrable_exp_mul_id_map_coe_projIcc [IsFiniteMeasure μ] {l r t : ℝ} (hlr : l ≤ r) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) (μ.map clip[l, r; hlr]) := by
  rw [integrable_map_measure (by fun_prop) (measurable_clip hlr).aemeasurable]
  exact integrable_exp_mul_of_mem_Icc (measurable_clip hlr).aemeasurable
    (Filter.Eventually.of_forall fun x ↦ (Set.projIcc l r hlr x).property)

/-- A law projected onto a bounded interval has every real exponential moment. -/
@[simp] theorem integrableExpSet_id_map_coe_projIcc [IsFiniteMeasure μ] {l r : ℝ} (hlr : l ≤ r) :
    integrableExpSet id (μ.map clip[l, r; hlr]) = Set.univ := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true, id_eq]
  exact integrable_exp_mul_id_map_coe_projIcc μ hlr

end MeasureTheory.Measure
