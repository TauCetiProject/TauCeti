/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.IntegerValued.Basic
public import TauCeti.MeasureTheory.MeasurableSpace.Option
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import TauCeti.Probability.Quantile

/-!
# Measurable selection of an occurrence

A measurable family of finite integer-valued measures on a standard Borel space
admits a measurable selection of an occurrence, with `none` exactly for zero
measures. Selected locations have mass at least one, so multiplicities are retained.
This is the selection step for enumerating occurrences and subsequently attaching
independent marks to them.

On the real line, a sufficiently low quantile of the normalized measure selects its
first occurrence: the open ray below it has mass less than one, hence zero by
integrality. A measurable embedding into the real line gives the standard Borel case.
No topology on the parameter space is required. The construction uses
`MeasureTheory.Measure.measurable_quantile_cdf_family` and Mathlib's
`measurableEmbedding_embeddingReal`.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 6 (measurable enumeration and multiplicities).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- The low quantile used for occurrence selection lies at an atom. -/
private lemma one_le_singleton_low_quantile {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hint : μ.IsIntegerValued) (hne : μ ≠ 0) :
    let ν := (μ univ)⁻¹ • μ
    1 ≤ μ {ν.quantile (μ.real univ + 1)⁻¹} := by
  intro ν
  have : IsProbabilityMeasure ν := ⟨by
    simp only [ν, smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (measure_univ_ne_zero.mpr hne) (measure_ne_top _ _)⟩
  have : NeZero μ := ⟨hne⟩
  have hpos : 0 < μ.real univ := measureReal_univ_pos
  let p : Ioo (0 : ℝ) 1 := ⟨(μ.real univ + 1)⁻¹, by
    constructor
    · positivity
    · exact (inv_lt_one₀ (by positivity)).2 (by linarith)⟩
  have hscale (s : Set ℝ) : ν.real s = (μ.real univ)⁻¹ * μ.real s := by
    simp [ν, ENNReal.toReal_inv, Measure.real]
  have hlo := ν.measureReal_Iio_quantile_le p.2.1
  have hhi := ν.le_cdf_quantile p.2.2
  rw [hscale] at hlo
  rw [ProbabilityTheory.cdf_eq_real, hscale] at hhi
  have hlo' : μ.real (Iio (ν.quantile p)) < 1 := by
    have hmul : (p : ℝ) * μ.real univ < 1 := by
      dsimp [p]
      rw [mul_comm, ← div_eq_mul_inv, div_lt_one (by positivity)]
      linarith
    have hbound := mul_le_mul_of_nonneg_left hlo hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_comm] at hbound
    exact hbound.trans_lt hmul
  have hzero : μ (Iio (ν.quantile p)) = 0 := by
    by_contra h
    have hone := hint.one_le_apply measurableSet_Iio h
    have := (ENNReal.toReal_le_toReal (by simp) (measure_ne_top _ _)).2 hone
    exact (not_le_of_gt hlo') this
  have hclosed : μ (Iic (ν.quantile p)) ≠ 0 := by
    intro h
    simp only [Measure.real, h, ENNReal.toReal_zero, mul_zero] at hhi
    exact (not_le_of_gt p.2.1) hhi
  apply hint.one_le_apply (measurableSet_singleton _)
  intro hsingle
  apply hclosed
  rw [← Iio_union_right, measure_union_null hzero hsingle]

private theorem exists_measurable_one_le_singleton_real {α : Type*} [MeasurableSpace α]
    {μ : α → Measure ℝ} (hm : Measurable μ)
    (hfinite : ∀ a, IsFiniteMeasure (μ a)) (hint : ∀ a, (μ a).IsIntegerValued)
    (hne : ∀ a, μ a ≠ 0) :
    ∃ f : α → ℝ, Measurable f ∧ ∀ a, 1 ≤ μ a {f a} := by
  let ν : α → Measure ℝ := fun a => (μ a univ)⁻¹ • μ a
  have hprob (a : α) : IsProbabilityMeasure (ν a) := by
    have := hfinite a
    exact ⟨by
      simp only [ν, smul_apply, smul_eq_mul]
      exact ENNReal.inv_mul_cancel (measure_univ_ne_zero.mpr (hne a)) (measure_ne_top _ _)⟩
  have hν : Measurable ν := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    exact (((Measure.measurable_coe MeasurableSet.univ).comp hm).inv).mul
      ((Measure.measurable_coe hs).comp hm)
  let p : α → Ioo (0 : ℝ) 1 := fun a =>
    ⟨((μ a).real univ + 1)⁻¹, by
      have := hfinite a
      have : NeZero (μ a) := ⟨hne a⟩
      have h : 0 < (μ a).real univ := measureReal_univ_pos
      constructor
      · positivity
      · exact (inv_lt_one₀ (by positivity)).2 (by linarith)⟩
  have hp : Measurable p := by
    apply Measurable.subtype_mk
    exact ((((Measure.measurable_coe MeasurableSet.univ).comp hm).ennreal_toReal).add_const 1).inv
  refine ⟨fun a => (ν a).quantile (p a),
    (measurable_quantile_cdf_family ν hν hprob).comp (measurable_id.prodMk hp), fun a => ?_⟩
  have := hfinite a
  exact one_le_singleton_low_quantile (hint a) (hne a)

/-- Select an occurrence measurably from each nonzero finite integer-valued measure
in a measurable family on a standard Borel space. The selected singleton has mass
at least one, even when locations have multiplicity. -/
theorem _root_.Measurable.exists_one_le_singleton {α X : Type*} [MeasurableSpace α]
    [MeasurableSpace X] [StandardBorelSpace X] {μ : α → Measure X} (hm : Measurable μ)
    (hfinite : ∀ a, IsFiniteMeasure (μ a)) (hint : ∀ a, (μ a).IsIntegerValued)
    (hne : ∀ a, μ a ≠ 0) :
    ∃ f : α → X, Measurable f ∧ ∀ a, 1 ≤ μ a {f a} := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
    have hfalse (a : α) : False := hne a (Subsingleton.elim _ _)
    exact ⟨fun a => (hfalse a).elim, measurable_of_subsingleton_codomain _,
      fun a => (hfalse a).elim⟩
  | inr hX =>
    let e := embeddingReal X
    have he : MeasurableEmbedding e := measurableEmbedding_embeddingReal X
    obtain ⟨g, hg, hmass⟩ := exists_measurable_one_le_singleton_real
      (μ := fun a => (μ a).map e)
      ((Measure.measurable_map e he.measurable).comp hm)
      (fun a => by have := hfinite a; infer_instance)
      (fun a => (hint a).map)
      (fun a => (Measure.map_ne_zero_iff he.measurable.aemeasurable).2 (hne a))
    refine ⟨fun a => he.invFun (g a), he.measurable_invFun.comp hg, fun a => ?_⟩
    have hrange : g a ∈ range e := by
      by_contra h
      have hpre : e ⁻¹' {g a} = ∅ := preimage_singleton_eq_empty.mpr h
      have h := hmass a
      rw [he.map_apply, hpre, measure_empty] at h
      exact (not_le_of_gt zero_lt_one) h
    obtain ⟨x, hx⟩ := hrange
    dsimp only
    rw [← hx, he.leftInverse_invFun x]
    have h := hmass a
    rw [← hx, ← image_singleton, he.map_apply, he.injective.preimage_image] at h
    exact h

/-- A measurable family of finite integer-valued measures admits an optional measurable
occurrence selection. It returns `none` exactly for the zero measure, and each selected
location has mass at least one. This includes empty state spaces and zero measures. -/
theorem _root_.Measurable.exists_option_one_le_singleton {α X : Type*} [MeasurableSpace α]
    [MeasurableSpace X] [StandardBorelSpace X] {μ : α → Measure X} (hm : Measurable μ)
    (hfinite : ∀ a, IsFiniteMeasure (μ a)) (hint : ∀ a, (μ a).IsIntegerValued) :
    ∃ f : α → Option X, Measurable f ∧
      (∀ a, f a = none ↔ μ a = 0) ∧
      ∀ a x, f a = some x → 1 ≤ μ a {x} := by
  classical
  let s : Set α := {a | μ a ≠ 0}
  have hs : MeasurableSet s := by
    have hs' : MeasurableSet {a | μ a univ = 0} :=
      measurableSet_eq_fun ((Measure.measurable_coe MeasurableSet.univ).comp hm) measurable_const
    exact hs'.compl.congr (Set.ext fun _ => measure_univ_ne_zero)
  obtain ⟨g, hg, hmass⟩ := (hm.comp measurable_subtype_coe).exists_one_le_singleton
    (fun a : s => hfinite a) (fun a : s => hint a) (fun a : s => a.2)
  refine ⟨fun a => if h : a ∈ s then some (g ⟨a, h⟩) else none,
    (Option.measurable_some.comp hg).dite measurable_const hs, ?_, ?_⟩
  · intro a
    by_cases h : a ∈ s <;> simp_all [s]
  · intro a x hx
    dsimp only at hx
    split_ifs at hx with h
    cases Option.some.inj hx
    exact hmass ⟨a, h⟩

end MeasureTheory.Measure
