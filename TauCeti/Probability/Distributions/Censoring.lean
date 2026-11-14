/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.ProjIcc
public import TauCeti.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import TauCeti.Probability.Moments.Basic
public import TauCeti.Probability.Quantile.Map

/-!
# Censoring real probability laws

Projecting a real random variable onto a closed interval replaces its lower and upper tails by
atoms at the corresponding endpoints and leaves the variable unchanged in the interval's
interior. This file describes that pushforward through Mathlib's `Set.projIcc`, together with the
one-sided projections `Set.projIci` and `Set.projIic`: it gives their endpoint/interior
decompositions, singleton masses, atomlessness criteria, cumulative distribution functions, and
quantile formulas.

Since the variable projected to a bounded interval is bounded, all of its natural moments and
exponential moments are integrable. The natural-moment formula below separates the two endpoint
atoms from the unchanged interior contribution. One-sided censoring instead preserves precisely
the integrability needed on the unchanged tail.

## Main results

* `MeasureTheory.Measure.map_coe_projIcc` and `MeasureTheory.Measure.map_coe_projIcc_self`
  decompose the censored law on nondegenerate and degenerate closed intervals;
* `MeasureTheory.Measure.map_coe_projIcc_singleton_left`,
  `MeasureTheory.Measure.map_coe_projIcc_singleton_right`, and
  `MeasureTheory.Measure.nullSingletonClass_map_coe_projIcc_iff` evaluate singleton masses and
  characterize when the censored law has null singletons;
* `MeasureTheory.Measure.cdf_map_coe_projIcc` computes its cumulative distribution function;
* `MeasureTheory.Measure.quantile_map_coe_projIcc` says that censoring commutes with interior
  quantiles;
* `MeasureTheory.Measure.integral_pow_map_coe_projIcc` decomposes every natural moment;
* `MeasureTheory.Measure.integrableExpSet_id_map_coe_projIcc` shows that the exponential-
  integrability domain is all of `ℝ`;
* `MeasureTheory.Measure.map_coe_projIci` and
  `MeasureTheory.Measure.map_coe_projIic`, together with their singleton and
  `NullSingletonClass` characterizations, describe the two one-sided censored laws;
* `MeasureTheory.Measure.integral_id_map_coe_projIci` and
  `MeasureTheory.Measure.integral_id_map_coe_projIic`, with their second-moment counterparts,
  compute the moments that remain integrable after one-sided censoring.
-/

public section

noncomputable section

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable (μ : Measure ℝ)

local notation "clip[" l ", " r "; " h "]" =>
  (fun x : ℝ ↦ (Set.projIcc l r h x : ℝ))

/-- Projecting a measure onto the degenerate interval `[l, l]` collapses all of its mass onto a
Dirac atom at `l`. -/
@[simp] theorem map_coe_projIcc_self (l : ℝ) :
    μ.map clip[l, l; le_rfl] = μ univ • Measure.dirac l := by
  have hconst : clip[l, l; le_rfl] = fun _ ↦ l :=
    funext fun x ↦ max_eq_left (min_le_left l x)
  rw [hconst, Measure.map_const]

/-- Projecting a measure onto `[l, r]` moves the lower and upper tails to atoms at the endpoints
and leaves the restriction to `(l, r)` unchanged. -/
theorem map_coe_projIcc {l r : ℝ} (hlr : l < r) :
    μ.map clip[l, r; hlr.le] =
      μ (Iic l) • Measure.dirac l + μ.restrict (Ioo l r) + μ (Ici r) • Measure.dirac r := by
  classical
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs]
  simp only [_root_.add_apply, _root_.smul_apply, Measure.dirac_apply' _ hs,
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

/-- At the left endpoint of a nondegenerate interval, the censored law has singleton mass equal to
the lower-tail mass `μ (Iic l)`. -/
@[simp] theorem map_coe_projIcc_singleton_left {l r : ℝ} (hlr : l < r) :
    μ.map clip[l, r; hlr.le] {l} = μ (Iic l) := by
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton l)]
  have hpre : clip[l, r; hlr.le] ⁻¹' {l} = Iic l := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, Set.coe_projIcc, mem_Iic]
    grind
  rw [hpre]

/-- At the right endpoint of a nondegenerate interval, the censored law has singleton mass equal
to the upper-tail mass `μ (Ici r)`. -/
@[simp] theorem map_coe_projIcc_singleton_right {l r : ℝ} (hlr : l < r) :
    μ.map clip[l, r; hlr.le] {r} = μ (Ici r) := by
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton r)]
  have hpre : clip[l, r; hlr.le] ⁻¹' {r} = Ici r := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, Set.coe_projIcc, mem_Ici]
    grind
  rw [hpre]

/-- Strictly inside `[l, r]`, censoring preserves the singleton mass of `μ`. -/
theorem map_coe_projIcc_singleton_of_mem_Ioo {l r x : ℝ} (hlr : l ≤ r) (hx : x ∈ Ioo l r) :
    μ.map clip[l, r; hlr] {x} = μ {x} := by
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  have hpre : clip[l, r; hlr] ⁻¹' {x} = {x} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, Set.coe_projIcc]
    have := hx.1
    have := hx.2
    grind
  rw [hpre]

/-- Outside `[l, r]`, the censored law assigns zero mass to every singleton. -/
theorem map_coe_projIcc_singleton_of_notMem_Icc {l r x : ℝ} (hlr : l ≤ r) (hx : x ∉ Icc l r) :
    μ.map clip[l, r; hlr] {x} = 0 := by
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  have hpre : clip[l, r; hlr] ⁻¹' {x} = ∅ :=
    eq_empty_of_forall_notMem fun y hy ↦
      hx (mem_singleton_iff.mp hy ▸ (Set.projIcc l r hlr y).property)
  rw [hpre, measure_empty]

/-- At the left endpoint of a nondegenerate interval, the real singleton mass of the censored law
is `μ.real (Iic l)`. -/
@[simp] theorem map_coe_projIcc_real_singleton_left {l r : ℝ} (hlr : l < r) :
    (μ.map clip[l, r; hlr.le]).real {l} = μ.real (Iic l) := by
  simp [Measure.real, map_coe_projIcc_singleton_left μ hlr]

/-- At the right endpoint of a nondegenerate interval, the real singleton mass of the censored law
is `μ.real (Ici r)`. -/
@[simp] theorem map_coe_projIcc_real_singleton_right {l r : ℝ} (hlr : l < r) :
    (μ.map clip[l, r; hlr.le]).real {r} = μ.real (Ici r) := by
  simp [Measure.real, map_coe_projIcc_singleton_right μ hlr]

/-- Projecting `μ` onto `[l, r]` produces a measure with null singletons if and only if both
outer tails `Iic l` and `Ici r` are `μ`-null and `μ` has null singletons on `(l, r)`. This
includes the degenerate case `l = r`, where `(l, r)` is empty and `Iic l ∪ Ici l = univ`. -/
theorem nullSingletonClass_map_coe_projIcc_iff {l r : ℝ} (hlr : l ≤ r) :
    NullSingletonClass (μ.map clip[l, r; hlr]) ↔
      μ (Iic l) = 0 ∧ NullSingletonClass (μ.restrict (Ioo l r)) ∧ μ (Ici r) = 0 := by
  rcases hlr.eq_or_lt with rfl | hlt
  · rw [map_coe_projIcc_self, nullSingletonClass_smul_dirac_iff, Ioo_self, Measure.restrict_empty]
    refine ⟨fun h ↦ ⟨measure_mono_null (subset_univ _) h, inferInstance,
      measure_mono_null (subset_univ _) h⟩, fun ⟨h1, _, h2⟩ ↦ ?_⟩
    rw [← Iic_union_Ici (a := l)]
    exact measure_union_null h1 h2
  · rw [map_coe_projIcc μ hlt, nullSingletonClass_add_iff, nullSingletonClass_add_iff,
      nullSingletonClass_smul_dirac_iff, nullSingletonClass_smul_dirac_iff, and_assoc]

/-- For a measure with null singletons, projecting onto `[l, r]` preserves null singletons if and
only if both outer tails `Iic l` and `Ici r` are null. -/
theorem nullSingletonClass_map_coe_projIcc_iff_of_nullSingletonClass [NullSingletonClass μ]
    {l r : ℝ} (hlr : l ≤ r) :
    NullSingletonClass (μ.map clip[l, r; hlr]) ↔ μ (Iic l) = 0 ∧ μ (Ici r) = 0 := by
  rw [nullSingletonClass_map_coe_projIcc_iff μ hlr]
  exact ⟨fun ⟨h1, _, h2⟩ ↦ ⟨h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, inferInstance, h2⟩⟩

/-- The cdf of a law projected onto `[l, r]` is zero below `l`, agrees with the original cdf on
`[l, r)`, and is one from `r` onwards. -/
@[simp] theorem cdf_map_coe_projIcc [IsProbabilityMeasure μ] {l r : ℝ} (hlr : l ≤ r) (x : ℝ) :
    cdf (μ.map clip[l, r; hlr]) x =
      if x < l then 0 else if x < r then cdf μ x else 1 := by
  rw [cdf_eq_real, Measure.real, Measure.map_apply (by fun_prop) measurableSet_Iic]
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
    (μ.map clip[l, r; hlr]).quantile u = clip[l, r; hlr] (μ.quantile u) :=
  Measure.quantile_map_of_monotone (Set.monotone_projIcc hlr) (by fun_prop) hu.1 hu.2

/-- Every natural power is integrable under a law projected onto a bounded interval. -/
theorem integrable_pow_map_coe_projIcc [IsFiniteMeasure μ] {l r : ℝ} (hlr : l ≤ r) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (μ.map clip[l, r; hlr]) := by
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
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
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  exact integrable_exp_mul_of_mem_Icc (by fun_prop)
    (Filter.Eventually.of_forall fun x ↦ (Set.projIcc l r hlr x).property)

/-- A law projected onto a bounded interval has every real exponential moment. -/
@[simp] theorem integrableExpSet_id_map_coe_projIcc [IsFiniteMeasure μ] {l r : ℝ} (hlr : l ≤ r) :
    integrableExpSet id (μ.map clip[l, r; hlr]) = Set.univ := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true, id_eq]
  exact integrable_exp_mul_id_map_coe_projIcc μ hlr

/-! ### Lower censoring -/

/-- Projecting a measure onto `[l, ∞)` moves the lower tail to an atom at `l` and leaves the
restriction to `(l, ∞)` unchanged. -/
theorem map_coe_projIci (l : ℝ) :
    μ.map (fun x : ℝ ↦ (Set.projIci l x : ℝ)) =
      μ (Iic l) • Measure.dirac l + μ.restrict (Ioi l) := by
  classical
  ext s hs
  rw [Measure.map_apply (by simp only [Set.coe_projIci]; fun_prop) hs]
  simp only [_root_.add_apply, _root_.smul_apply, Measure.dirac_apply' _ hs,
    Measure.restrict_apply hs, smul_eq_mul]
  have hpreimage :
      (fun x : ℝ ↦ (Set.projIci l x : ℝ)) ⁻¹' s =
        (if l ∈ s then Iic l else ∅) ∪ (s ∩ Ioi l) := by
    by_cases hls : l ∈ s <;> ext x <;> simp [hls, Set.coe_projIci] <;> grind
  rw [hpreimage, measure_union]
  · by_cases hls : l ∈ s <;> simp [hls]
  · by_cases hls : l ∈ s
    · apply Set.disjoint_left.2
      intro x hx hx'
      rw [ite_eq_left hls] at hx
      exact (not_lt_of_ge hx) hx'.2
    · simp [hls]
  · exact hs.inter measurableSet_Ioi

/-- At the lower cutoff `l`, lower censoring has singleton mass equal to the lower-tail mass
`μ (Iic l)`. -/
@[simp] theorem map_coe_projIci_singleton_self (l : ℝ) :
    μ.map (fun x : ℝ ↦ (Set.projIci l x : ℝ)) {l} = μ (Iic l) := by
  rw [Measure.map_apply (by simp only [Set.coe_projIci]; fun_prop) (measurableSet_singleton l)]
  have hpre : (fun x : ℝ ↦ (Set.projIci l x : ℝ)) ⁻¹' {l} = Iic l := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, Set.coe_projIci, mem_Iic]
    grind
  rw [hpre]

/-- Strictly above `l`, lower censoring preserves the singleton mass of `μ`. -/
theorem map_coe_projIci_singleton_of_mem_Ioi {l x : ℝ} (hx : x ∈ Ioi l) :
    μ.map (fun y : ℝ ↦ (Set.projIci l y : ℝ)) {x} = μ {x} := by
  rw [Measure.map_apply (by simp only [Set.coe_projIci]; fun_prop) (measurableSet_singleton x)]
  have hpre : (fun y : ℝ ↦ (Set.projIci l y : ℝ)) ⁻¹' {x} = {x} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, Set.coe_projIci]
    have : l < x := hx
    grind
  rw [hpre]

/-- Strictly below `l`, lower censoring assigns zero mass to every singleton. -/
theorem map_coe_projIci_singleton_of_notMem_Ici {l x : ℝ} (hx : x ∉ Ici l) :
    μ.map (fun y : ℝ ↦ (Set.projIci l y : ℝ)) {x} = 0 := by
  rw [Measure.map_apply (by simp only [Set.coe_projIci]; fun_prop) (measurableSet_singleton x)]
  have hpre : (fun y : ℝ ↦ (Set.projIci l y : ℝ)) ⁻¹' {x} = ∅ :=
    eq_empty_of_forall_notMem fun y hy ↦
      hx (mem_singleton_iff.mp hy ▸ (Set.projIci l y).property)
  rw [hpre, measure_empty]

/-- At the lower cutoff `l`, the real singleton mass of the lower-censored law is
`μ.real (Iic l)`. -/
@[simp] theorem map_coe_projIci_real_singleton_self (l : ℝ) :
    (μ.map fun x : ℝ ↦ (Set.projIci l x : ℝ)).real {l} = μ.real (Iic l) := by
  simp [Measure.real, map_coe_projIci_singleton_self μ l]

/-- Lower censoring at `l` produces a measure with null singletons if and only if the lower tail
`Iic l` is `μ`-null and `μ` has null singletons on `(l, ∞)`. -/
theorem nullSingletonClass_map_coe_projIci_iff (l : ℝ) :
    NullSingletonClass (μ.map fun x : ℝ ↦ (Set.projIci l x : ℝ)) ↔
      μ (Iic l) = 0 ∧ NullSingletonClass (μ.restrict (Ioi l)) := by
  rw [map_coe_projIci μ l, nullSingletonClass_add_iff, nullSingletonClass_smul_dirac_iff]

/-- For a measure with null singletons, lower censoring at `l` preserves null singletons if and
only if the lower tail `Iic l` is null. -/
theorem nullSingletonClass_map_coe_projIci_iff_of_nullSingletonClass [NullSingletonClass μ]
    (l : ℝ) :
    NullSingletonClass (μ.map fun x : ℝ ↦ (Set.projIci l x : ℝ)) ↔ μ (Iic l) = 0 := by
  rw [nullSingletonClass_map_coe_projIci_iff μ l]
  exact and_iff_left inferInstance

/-- The cdf of a law projected onto `[l, ∞)` is zero below `l` and agrees with the original cdf
from `l` onwards. -/
@[simp] theorem cdf_map_coe_projIci [IsProbabilityMeasure μ] (l x : ℝ) :
    cdf (μ.map fun y : ℝ ↦ (Set.projIci l y : ℝ)) x =
      if x < l then 0 else cdf μ x := by
  rw [cdf_eq_real, Measure.real,
    Measure.map_apply (by simp only [Set.coe_projIci]; fun_prop) measurableSet_Iic]
  by_cases hxl : x < l
  · rw [ite_eq_left hxl]
    have hpre : (fun y : ℝ ↦ (Set.projIci l y : ℝ)) ⁻¹' Iic x = ∅ := by
      ext y
      simp only [mem_preimage, mem_Iic, Set.coe_projIci, mem_empty_iff_false, iff_false]
      exact fun h ↦ (not_lt_of_ge ((le_max_left l y).trans h)) hxl
    rw [hpre, measure_empty, ENNReal.toReal_zero]
  · rw [ite_eq_right hxl, cdf_eq_real, Measure.real]
    have hpre : (fun y : ℝ ↦ (Set.projIci l y : ℝ)) ⁻¹' Iic x = Iic x := by
      ext y
      simp only [mem_preimage, mem_Iic, Set.coe_projIci]
      exact max_le_iff.trans (and_iff_right (le_of_not_gt hxl))
    rw [hpre]

/-- For an interior probability level, lower censoring takes the quantile to the maximum of the
cutoff and the original quantile. -/
@[simp] theorem quantile_map_coe_projIci [IsProbabilityMeasure μ] (l : ℝ) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (μ.map fun x : ℝ ↦ (Set.projIci l x : ℝ)).quantile u =
      (Set.projIci l (μ.quantile u) : ℝ) := by
  exact Measure.quantile_map_of_monotone
    (fun _ _ h ↦ max_le_max le_rfl h) (by simp only [Set.coe_projIci]; fun_prop) hu.1 hu.2

/-- Integrability after lower censoring is exactly integrability on the unchanged upper tail. -/
theorem integrable_map_coe_projIci_iff {E : Type*} [SeminormedAddGroup E]
    [IsFiniteMeasure μ] (l : ℝ) {f : ℝ → E} :
    Integrable f (μ.map fun x : ℝ ↦ (Set.projIci l x : ℝ)) ↔
      Integrable f (μ.restrict (Ioi l)) := by
  rw [map_coe_projIci μ l, integrable_add_measure]
  exact and_iff_right ((integrable_dirac (by simp)).smul_measure (measure_ne_top μ (Iic l)))

/-- Integration under lower censoring is the endpoint contribution plus the unchanged upper-tail
integral. -/
theorem integral_map_coe_projIci {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [IsFiniteMeasure μ] (l : ℝ) {f : ℝ → E}
    (hf : Integrable f (μ.restrict (Ioi l))) :
    ∫ x, f x ∂(μ.map fun y : ℝ ↦ (Set.projIci l y : ℝ)) =
      μ.real (Iic l) • f l + ∫ x in Ioi l, f x ∂μ := by
  have hint := (integrable_map_coe_projIci_iff μ l).2 hf
  rw [map_coe_projIci μ l, integrable_add_measure] at hint
  rw [map_coe_projIci μ l, integral_add_measure hint.1 hint.2]
  simp only [integral_smul_measure, integral_dirac, Measure.real]

/-- The first moment after lower censoring is the lower endpoint contribution plus the unchanged
upper-tail integral. -/
theorem integral_id_map_coe_projIci [IsFiniteMeasure μ] (l : ℝ)
    (h : Integrable id (μ.restrict (Ioi l))) :
    ∫ x, x ∂(μ.map fun y : ℝ ↦ (Set.projIci l y : ℝ)) =
      μ.real (Iic l) * l + ∫ x in Ioi l, x ∂μ := by
  simpa using integral_map_coe_projIci μ l (f := id) h

/-- The second moment after lower censoring is the lower endpoint contribution plus the unchanged
upper-tail contribution. -/
theorem integral_sq_map_coe_projIci [IsFiniteMeasure μ] (l : ℝ)
    (h : Integrable (fun x : ℝ ↦ x ^ 2) (μ.restrict (Ioi l))) :
    ∫ x, x ^ 2 ∂(μ.map fun y : ℝ ↦ (Set.projIci l y : ℝ)) =
      μ.real (Iic l) * l ^ 2 + ∫ x in Ioi l, x ^ 2 ∂μ :=
  integral_map_coe_projIci μ l h

/-! ### Upper censoring -/

/-- Projecting a measure onto `(-∞, r]` leaves the restriction to `(-∞, r)` unchanged and
moves the upper tail to an atom at `r`. -/
theorem map_coe_projIic (r : ℝ) :
    μ.map (fun x : ℝ ↦ (Set.projIic r x : ℝ)) =
      μ.restrict (Iio r) + μ (Ici r) • Measure.dirac r := by
  classical
  ext s hs
  rw [Measure.map_apply (by simp only [Set.coe_projIic]; fun_prop) hs]
  simp only [_root_.add_apply, _root_.smul_apply, Measure.dirac_apply' _ hs,
    Measure.restrict_apply hs, smul_eq_mul]
  have hpreimage :
      (fun x : ℝ ↦ (Set.projIic r x : ℝ)) ⁻¹' s =
        (s ∩ Iio r) ∪ (if r ∈ s then Ici r else ∅) := by
    by_cases hrs : r ∈ s <;> ext x <;> simp [hrs, Set.coe_projIic] <;> grind
  rw [hpreimage, measure_union]
  · by_cases hrs : r ∈ s <;> simp [hrs]
  · by_cases hrs : r ∈ s
    · apply Set.disjoint_left.2
      intro x hx hx'
      rw [ite_eq_left hrs] at hx'
      exact (not_lt_of_ge hx') hx.2
    · simp [hrs]
  · by_cases hrs : r ∈ s <;> simp [hrs]

/-- At the upper cutoff `r`, upper censoring has singleton mass equal to the upper-tail mass
`μ (Ici r)`. -/
@[simp] theorem map_coe_projIic_singleton_self (r : ℝ) :
    μ.map (fun x : ℝ ↦ (Set.projIic r x : ℝ)) {r} = μ (Ici r) := by
  rw [Measure.map_apply (by simp only [Set.coe_projIic]; fun_prop) (measurableSet_singleton r)]
  have hpre : (fun x : ℝ ↦ (Set.projIic r x : ℝ)) ⁻¹' {r} = Ici r := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, Set.coe_projIic, mem_Ici]
    grind
  rw [hpre]

/-- Strictly below `r`, upper censoring preserves the singleton mass of `μ`. -/
theorem map_coe_projIic_singleton_of_mem_Iio {r x : ℝ} (hx : x ∈ Iio r) :
    μ.map (fun y : ℝ ↦ (Set.projIic r y : ℝ)) {x} = μ {x} := by
  rw [Measure.map_apply (by simp only [Set.coe_projIic]; fun_prop) (measurableSet_singleton x)]
  have hpre : (fun y : ℝ ↦ (Set.projIic r y : ℝ)) ⁻¹' {x} = {x} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, Set.coe_projIic]
    have : x < r := hx
    grind
  rw [hpre]

/-- Strictly above `r`, upper censoring assigns zero mass to every singleton. -/
theorem map_coe_projIic_singleton_of_notMem_Iic {r x : ℝ} (hx : x ∉ Iic r) :
    μ.map (fun y : ℝ ↦ (Set.projIic r y : ℝ)) {x} = 0 := by
  rw [Measure.map_apply (by simp only [Set.coe_projIic]; fun_prop) (measurableSet_singleton x)]
  have hpre : (fun y : ℝ ↦ (Set.projIic r y : ℝ)) ⁻¹' {x} = ∅ :=
    eq_empty_of_forall_notMem fun y hy ↦
      hx (mem_singleton_iff.mp hy ▸ (Set.projIic r y).property)
  rw [hpre, measure_empty]

/-- At the upper cutoff `r`, the real singleton mass of the upper-censored law is
`μ.real (Ici r)`. -/
@[simp] theorem map_coe_projIic_real_singleton_self (r : ℝ) :
    (μ.map fun x : ℝ ↦ (Set.projIic r x : ℝ)).real {r} = μ.real (Ici r) := by
  simp [Measure.real, map_coe_projIic_singleton_self μ r]

/-- Upper censoring at `r` produces a measure with null singletons if and only if `μ` has null
singletons on `(-∞, r)` and the upper tail `Ici r` is `μ`-null. -/
theorem nullSingletonClass_map_coe_projIic_iff (r : ℝ) :
    NullSingletonClass (μ.map fun x : ℝ ↦ (Set.projIic r x : ℝ)) ↔
      NullSingletonClass (μ.restrict (Iio r)) ∧ μ (Ici r) = 0 := by
  rw [map_coe_projIic μ r, nullSingletonClass_add_iff, nullSingletonClass_smul_dirac_iff]

/-- For a measure with null singletons, upper censoring at `r` preserves null singletons if and
only if the upper tail `Ici r` is null. -/
theorem nullSingletonClass_map_coe_projIic_iff_of_nullSingletonClass [NullSingletonClass μ]
    (r : ℝ) :
    NullSingletonClass (μ.map fun x : ℝ ↦ (Set.projIic r x : ℝ)) ↔ μ (Ici r) = 0 := by
  rw [nullSingletonClass_map_coe_projIic_iff μ r]
  exact and_iff_right inferInstance

/-- The cdf of a law projected onto `(-∞, r]` agrees with the original cdf below `r` and is one
from `r` onwards. -/
@[simp] theorem cdf_map_coe_projIic [IsProbabilityMeasure μ] (r x : ℝ) :
    cdf (μ.map fun y : ℝ ↦ (Set.projIic r y : ℝ)) x =
      if x < r then cdf μ x else 1 := by
  rw [cdf_eq_real, Measure.real,
    Measure.map_apply (by simp only [Set.coe_projIic]; fun_prop) measurableSet_Iic]
  by_cases hxr : x < r
  · rw [ite_eq_left hxr, cdf_eq_real, Measure.real]
    have hpre : (fun y : ℝ ↦ (Set.projIic r y : ℝ)) ⁻¹' Iic x = Iic x := by
      ext y
      simp only [mem_preimage, mem_Iic, Set.coe_projIic]
      constructor
      · intro h
        by_contra hy
        exact (not_lt_of_ge h) (lt_min hxr (lt_of_not_ge hy))
      · intro h
        exact (min_le_right r y).trans h
    rw [hpre]
  · rw [ite_eq_right hxr]
    have hpre : (fun y : ℝ ↦ (Set.projIic r y : ℝ)) ⁻¹' Iic x = Set.univ := by
      ext y
      simp only [mem_preimage, mem_Iic, Set.coe_projIic, mem_univ, iff_true]
      exact (min_le_left r y).trans (le_of_not_gt hxr)
    rw [hpre, measure_univ]
    simp

/-- For an interior probability level, upper censoring takes the quantile to the minimum of the
cutoff and the original quantile. -/
@[simp] theorem quantile_map_coe_projIic [IsProbabilityMeasure μ] (r : ℝ) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (μ.map fun x : ℝ ↦ (Set.projIic r x : ℝ)).quantile u =
      (Set.projIic r (μ.quantile u) : ℝ) := by
  exact Measure.quantile_map_of_monotone
    (fun _ _ h ↦ min_le_min le_rfl h) (by simp only [Set.coe_projIic]; fun_prop) hu.1 hu.2

/-- Integrability after upper censoring is exactly integrability on the unchanged lower tail. -/
theorem integrable_map_coe_projIic_iff {E : Type*} [SeminormedAddGroup E]
    [IsFiniteMeasure μ] (r : ℝ) {f : ℝ → E} :
    Integrable f (μ.map fun x : ℝ ↦ (Set.projIic r x : ℝ)) ↔
      Integrable f (μ.restrict (Iio r)) := by
  rw [map_coe_projIic μ r, integrable_add_measure]
  exact and_iff_left ((integrable_dirac (by simp)).smul_measure (measure_ne_top μ (Ici r)))

/-- Integration under upper censoring is the unchanged lower-tail integral plus the endpoint
contribution. -/
theorem integral_map_coe_projIic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [IsFiniteMeasure μ] (r : ℝ) {f : ℝ → E}
    (hf : Integrable f (μ.restrict (Iio r))) :
    ∫ x, f x ∂(μ.map fun y : ℝ ↦ (Set.projIic r y : ℝ)) =
      (∫ x in Iio r, f x ∂μ) + μ.real (Ici r) • f r := by
  have hint := (integrable_map_coe_projIic_iff μ r).2 hf
  rw [map_coe_projIic μ r, integrable_add_measure] at hint
  rw [map_coe_projIic μ r, integral_add_measure hint.1 hint.2]
  simp only [integral_smul_measure, integral_dirac, Measure.real]

/-- The first moment after upper censoring is the unchanged lower-tail integral plus the upper
endpoint contribution. -/
theorem integral_id_map_coe_projIic [IsFiniteMeasure μ] (r : ℝ)
    (h : Integrable id (μ.restrict (Iio r))) :
    ∫ x, x ∂(μ.map fun y : ℝ ↦ (Set.projIic r y : ℝ)) =
      (∫ x in Iio r, x ∂μ) + μ.real (Ici r) * r := by
  simpa using integral_map_coe_projIic μ r (f := id) h

/-- The second moment after upper censoring is the unchanged lower-tail contribution plus the
upper endpoint contribution. -/
theorem integral_sq_map_coe_projIic [IsFiniteMeasure μ] (r : ℝ)
    (h : Integrable (fun x : ℝ ↦ x ^ 2) (μ.restrict (Iio r))) :
    ∫ x, x ^ 2 ∂(μ.map fun y : ℝ ↦ (Set.projIic r y : ℝ)) =
      (∫ x in Iio r, x ^ 2 ∂μ) + μ.real (Ici r) * r ^ 2 :=
  integral_map_coe_projIic μ r h

end MeasureTheory.Measure
