/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.UniformOn

/-!
# Empirical measures of finite families and sequences

This file defines the empirical finite measure `(card κ)⁻¹ ∑ᵢ δ_{x i}` of a family indexed by an
arbitrary finite type (`empiricalFiniteMeasure`), which is the zero measure for an empty family.
For a nonempty index type its underlying measure is a probability measure, packaged as
`empiricalMeasureOfFintype`; as its `κ := Fin (n + 1)` case, `empiricalMeasure` is the empirical
probability measure of the first `n + 1` terms of a sequence. The successor indexing is what
supplies the `Nonempty` instance for the sequence form, so it needs no side condition, and it
matches the shape used in limit theorems.

There is one construction, not three: the probability measures are *defined* from the finite
measure, and the sequence form as a specialization, so they can never drift apart.

The API covers evaluation, integration, pushforward, measurability and finite support. Values are
counted with multiplicity: the empirical measure depends only on the multiset of values, so it is
invariant under reindexing, and the empirical measure of a concatenation is the average of the
empirical measures of its pieces weighted by their sizes. The finite-population form is used by
quantitative sampling arguments and, applied to eigenvalues, defines empirical spectral measures of
matrices. The sequence form is the process-level input to the empirical-measure form of de
Finetti's theorem.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

variable {α Ω E : Type*} [MeasurableSpace α] [MeasurableSpace Ω]


section FiniteFamily

variable {κ κ' : Type*} [Fintype κ] [Fintype κ']

/-- The empirical finite measure `(card κ)⁻¹ ∑ᵢ δ_{x i}` of a finite family `x : κ → α`.

Values are counted with multiplicity. For a nonempty index type this is a probability measure, the
one underlying `empiricalMeasureOfFintype`; for an empty family it is the zero measure. -/
def empiricalFiniteMeasure (x : κ → α) : FiniteMeasure α :=
  ⟨∑ i, ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (x i), by
    refine ⟨?_⟩
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · simp
    · simp [ENNReal.mul_lt_top_iff, Fintype.card_pos]⟩

/-- The measure underlying an empirical finite measure is the normalized sum of its Dirac
masses. -/
@[simp]
theorem empiricalFiniteMeasure_toMeasure (x : κ → α) :
    (empiricalFiniteMeasure x : Measure α) =
      ∑ i, ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (x i) :=
  (rfl)

/-- Scaling the empirical finite measure by the size of the family gives the sum of its Dirac
masses. -/
theorem card_smul_empiricalFiniteMeasure (x : κ → α) :
    ((Fintype.card κ : ℕ) : ℝ≥0∞) • (empiricalFiniteMeasure x : Measure α) =
      ∑ i, Measure.dirac (x i) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  · rw [empiricalFiniteMeasure_toMeasure, ← Finset.smul_sum, smul_smul,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_smul]

/-- The empirical finite measure of an empty family is zero. -/
@[simp]
theorem empiricalFiniteMeasure_of_isEmpty [IsEmpty κ] (x : κ → α) :
    empiricalFiniteMeasure x = 0 :=
  FiniteMeasure.toMeasure_injective (by
    rw [empiricalFiniteMeasure_toMeasure, Finset.univ_eq_empty, Finset.sum_empty,
      FiniteMeasure.toMeasure_zero])

/-- Evaluation of an empirical finite measure on a measurable set is its empirical frequency. -/
theorem empiricalFiniteMeasure_apply {x : κ → α} {s : Set α} (hs : MeasurableSet s) :
    (empiricalFiniteMeasure x : Measure α) s = ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ *
      ∑ i, s.indicator (1 : α → ℝ≥0∞) (x i) := by
  rw [empiricalFiniteMeasure_toMeasure]
  simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hs, Finset.mul_sum]

/-- A nonempty family has an empirical probability measure. -/
instance isProbabilityMeasure_empiricalFiniteMeasure [Nonempty κ] (x : κ → α) :
    IsProbabilityMeasure (empiricalFiniteMeasure x : Measure α) := by
  refine ⟨?_⟩
  rw [empiricalFiniteMeasure_apply MeasurableSet.univ]
  have hκ0 : ((Fintype.card κ : ℕ) : ℝ≥0∞) ≠ 0 := by simp
  have hκtop : ((Fintype.card κ : ℕ) : ℝ≥0∞) ≠ ∞ := by simp
  simpa [mul_comm] using ENNReal.mul_inv_cancel hκ0 hκtop

/-- A nonempty family has an empirical measure of total mass one. -/
@[simp]
theorem mass_empiricalFiniteMeasure [Nonempty κ] (x : κ → α) :
    (empiricalFiniteMeasure x).mass = 1 := by
  rw [← ENNReal.coe_inj, FiniteMeasure.ennreal_mass, measure_univ, ENNReal.coe_one]

/-- The empirical finite measure depends only on the multiset of values of the family, so two
families with the same values, counted with multiplicity, have the same empirical measure. -/
theorem empiricalFiniteMeasure_eq_of_map_univ_val_eq {x : κ → α} {y : κ' → α}
    (h : (Finset.univ : Finset κ).val.map x = (Finset.univ : Finset κ').val.map y) :
    empiricalFiniteMeasure x = empiricalFiniteMeasure y := by
  have hcard : Fintype.card κ = Fintype.card κ' := by
    simpa using congrArg Multiset.card h
  have hsum : ∑ i, Measure.dirac (x i) = ∑ j, Measure.dirac (y j) := by
    have := congrArg (fun s => (s.map Measure.dirac).sum) h
    simp only [Multiset.map_map, Function.comp_def] at this
    rwa [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  apply FiniteMeasure.toMeasure_injective
  simp only [empiricalFiniteMeasure_toMeasure, ← Finset.smul_sum, hcard, hsum]

/-- Reindexing a family by an equivalence does not change its empirical finite measure. -/
@[simp]
theorem empiricalFiniteMeasure_comp_equiv (e : κ' ≃ κ) (x : κ → α) :
    empiricalFiniteMeasure (x ∘ e) = empiricalFiniteMeasure x := by
  apply FiniteMeasure.toMeasure_injective
  simp only [empiricalFiniteMeasure_toMeasure, Function.comp_apply, Fintype.card_congr e]
  exact e.sum_comp fun i => ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (x i)

/-- The empirical finite measure of a concatenation is the average of the empirical finite
measures of the pieces, weighted by their sizes. -/
theorem empiricalFiniteMeasure_sumElim (x : κ → α) (y : κ' → α) :
    empiricalFiniteMeasure (Sum.elim x y) =
      ((Fintype.card κ : ℝ≥0) / (Fintype.card κ + Fintype.card κ')) • empiricalFiniteMeasure x +
        ((Fintype.card κ' : ℝ≥0) / (Fintype.card κ + Fintype.card κ')) •
          empiricalFiniteMeasure y := by
  apply FiniteMeasure.toMeasure_injective
  rcases eq_or_ne (Fintype.card κ + Fintype.card κ') 0 with hN | hN
  · have : IsEmpty κ := Fintype.card_eq_zero_iff.mp (by omega)
    have : IsEmpty κ' := Fintype.card_eq_zero_iff.mp (by omega)
    simp
  have hN' : ((Fintype.card κ : ℝ≥0) + Fintype.card κ') ≠ 0 := mod_cast hN
  simp only [FiniteMeasure.toMeasure_add, FiniteMeasure.toMeasure_smul, ENNReal.smul_def,
    div_eq_inv_mul, ← smul_smul, ENNReal.coe_natCast,
    card_smul_empiricalFiniteMeasure]
  rw [empiricalFiniteMeasure_toMeasure, Fintype.card_sum, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ← Finset.smul_sum, Nat.cast_add, ENNReal.coe_inv hN',
    ENNReal.coe_add, ENNReal.coe_natCast]

/-- Pushing an empirical finite measure forward along a measurable map gives the empirical finite
measure of the image family. -/
@[simp]
theorem map_empiricalFiniteMeasure {β : Type*} [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (x : κ → α) :
    (empiricalFiniteMeasure x).map f = empiricalFiniteMeasure (f ∘ x) := by
  apply FiniteMeasure.toMeasure_injective
  ext s hs
  rw [FiniteMeasure.toMeasure_map, Measure.map_apply hf hs, empiricalFiniteMeasure_apply (hf hs),
    empiricalFiniteMeasure_apply hs]
  simp only [← Set.indicator_comp_right, Pi.one_comp, Function.comp_apply]

/-- Integrating against an empirical finite measure is averaging over the family. -/
theorem integral_empiricalFiniteMeasure [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {x : κ → α} {f : α → E} (hf : StronglyMeasurable f) :
    ∫ y, f y ∂(empiricalFiniteMeasure x : Measure α) =
      ((Fintype.card κ : ℕ) : ℝ)⁻¹ • ∑ i, f (x i) := by
  rw [empiricalFiniteMeasure_toMeasure, integral_finsetSum_measure]
  · simp_rw [integral_smul_measure, integral_dirac' f _ hf]
    rw [← Finset.smul_sum]
    congr 1
    rw [ENNReal.toReal_inv]
    norm_cast
  · intro i _
    have : Nonempty κ := ⟨i⟩
    exact (integrable_dirac' hf (by simp)).smul_measure (by simp)

/-- When singletons are measurable, integrating any function against an empirical finite measure
is averaging over the family; no measurability of the integrand is needed. -/
theorem integral_empiricalFiniteMeasure_of_measurableSingletonClass [MeasurableSingletonClass α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {x : κ → α} (f : α → E) :
    ∫ y, f y ∂(empiricalFiniteMeasure x : Measure α) =
      ((Fintype.card κ : ℕ) : ℝ)⁻¹ • ∑ i, f (x i) := by
  rw [empiricalFiniteMeasure_toMeasure, integral_finsetSum_measure]
  · simp_rw [integral_smul_measure, integral_dirac]
    rw [← Finset.smul_sum]
    congr 1
    rw [ENNReal.toReal_inv]
    norm_cast
  · intro i _
    have : Nonempty κ := ⟨i⟩
    exact (integrable_dirac (by simp)).smul_measure (by simp)

/-- The Lebesgue integral against an empirical finite measure is the average over the family. -/
theorem lintegral_empiricalFiniteMeasure {x : κ → α} {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(empiricalFiniteMeasure x : Measure α) =
      ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, f (x i) := by
  simp [lintegral_finsetSum_measure, lintegral_dirac' _ hf, Finset.mul_sum]

/-- Empirical finite measures depend measurably on the family. -/
theorem measurable_empiricalFiniteMeasure :
    Measurable (empiricalFiniteMeasure : (κ → α) → FiniteMeasure α) := by
  apply Measurable.subtype_mk
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [← empiricalFiniteMeasure_toMeasure, empiricalFiniteMeasure_apply hs]
  fun_prop

end FiniteFamily

section FinitePopulation

variable {κ : Type*} [Fintype κ] [Nonempty κ]

/-- The empirical probability measure of a nonempty finite population `x : κ → α`.

Its underlying finite measure is `empiricalFiniteMeasure x`. Unlike `empiricalMeasure`, its
population can have an arbitrary nonempty finite index type rather than a natural-number
prefix. -/
def empiricalMeasureOfFintype (x : κ → α) : ProbabilityMeasure α :=
  ⟨empiricalFiniteMeasure x, inferInstance⟩

/-- The finite measure underlying a finite empirical population is its empirical finite
measure. -/
@[simp]
theorem toFiniteMeasure_empiricalMeasureOfFintype (x : κ → α) :
    (empiricalMeasureOfFintype x).toFiniteMeasure = empiricalFiniteMeasure x :=
  (rfl)

/-- The measure underlying a finite empirical population is the normalized sum of its Dirac
masses. -/
@[simp]
theorem empiricalMeasureOfFintype_toMeasure (x : κ → α) :
    (empiricalMeasureOfFintype x : Measure α) =
      ∑ i, ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (x i) :=
  (rfl)

/-- Evaluation of a finite empirical population on a measurable set is its empirical
frequency. -/
theorem empiricalMeasureOfFintype_apply {x : κ → α} {s : Set α} (hs : MeasurableSet s) :
    (empiricalMeasureOfFintype x : Measure α) s = ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ *
      ∑ i, s.indicator (1 : α → ℝ≥0∞) (x i) := by
  rw [← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    toFiniteMeasure_empiricalMeasureOfFintype, empiricalFiniteMeasure_apply hs]

/-- Two nonempty finite populations with the same values, counted with multiplicity, have the
same empirical measure. -/
theorem empiricalMeasureOfFintype_eq_of_map_univ_val_eq {κ' : Type*} [Fintype κ'] [Nonempty κ']
    {x : κ → α} {y : κ' → α}
    (h : (Finset.univ : Finset κ).val.map x = (Finset.univ : Finset κ').val.map y) :
    empiricalMeasureOfFintype x = empiricalMeasureOfFintype y := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    toFiniteMeasure_empiricalMeasureOfFintype, toFiniteMeasure_empiricalMeasureOfFintype,
    empiricalFiniteMeasure_eq_of_map_univ_val_eq h]

/-- Reindexing a finite population by an equivalence does not change its empirical measure. -/
@[simp]
theorem empiricalMeasureOfFintype_comp_equiv {κ' : Type*} [Fintype κ'] [Nonempty κ']
    (e : κ' ≃ κ) (x : κ → α) :
    empiricalMeasureOfFintype (x ∘ e) = empiricalMeasureOfFintype x := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    toFiniteMeasure_empiricalMeasureOfFintype, toFiniteMeasure_empiricalMeasureOfFintype,
    empiricalFiniteMeasure_comp_equiv]

/-- Pushing a finite empirical population forward along a measurable map gives the empirical
measure of the image population. -/
@[simp]
theorem map_empiricalMeasureOfFintype {β : Type*} [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (x : κ → α) :
    (empiricalMeasureOfFintype x).map f = empiricalMeasureOfFintype (f ∘ x) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map,
    ← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    toFiniteMeasure_empiricalMeasureOfFintype, toFiniteMeasure_empiricalMeasureOfFintype,
    ← map_empiricalFiniteMeasure hf, FiniteMeasure.toMeasure_map]

/-- On a discrete finite index type, a finite empirical population is the pushforward of the
uniform law on its indices. -/
theorem empiricalMeasureOfFintype_eq_map_uniformOn [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (x : κ → α) :
    (empiricalMeasureOfFintype x : Measure α) =
      (ProbabilityTheory.uniformOn (Set.univ : Set κ)).map x := by
  ext s hs
  rw [empiricalMeasureOfFintype_apply hs, Measure.map_apply (measurable_of_countable x) hs,
    ProbabilityTheory.uniformOn_univ]
  classical
  have hpreimage :
      x ⁻¹' s = (Finset.univ.filter fun i => x i ∈ s : Finset κ) := by
    ext i
    simp
  rw [hpreimage, Measure.count_apply_finset]
  simp only [Set.indicator_apply, Pi.one_apply]
  rw [← ENNReal.div_eq_inv_mul]
  congr 1
  norm_cast
  simp

/-- Integrating against a finite empirical population is averaging over its values. -/
theorem integral_empiricalMeasureOfFintype [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {x : κ → α} {f : α → E} (hf : StronglyMeasurable f) :
    ∫ y, f y ∂(empiricalMeasureOfFintype x : Measure α) =
      ((Fintype.card κ : ℕ) : ℝ)⁻¹ • ∑ i, f (x i) := by
  rw [← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    toFiniteMeasure_empiricalMeasureOfFintype, integral_empiricalFiniteMeasure hf]

/-- The Lebesgue integral against a finite empirical population is the average of the values. -/
theorem lintegral_empiricalMeasureOfFintype {x : κ → α} {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(empiricalMeasureOfFintype x : Measure α) =
      ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, f (x i) := by
  simp [lintegral_finsetSum_measure, lintegral_dirac' _ hf, Finset.mul_sum]

/-- Finite empirical distributions depend measurably on the population. -/
theorem measurable_empiricalMeasureOfFintype :
    Measurable (empiricalMeasureOfFintype : (κ → α) → ProbabilityMeasure α) :=
  (measurable_subtype_coe.comp measurable_empiricalFiniteMeasure).subtype_mk

/-- A finite empirical population is concentrated on the finite set of its values. -/
theorem exists_finset_ae_mem_empiricalMeasureOfFintype [MeasurableSingletonClass α]
    (x : κ → α) :
    ∃ s : Finset α, ∀ᵐ y ∂(empiricalMeasureOfFintype x : Measure α), y ∈ s := by
  classical
  refine ⟨Finset.univ.image x, ?_⟩
  rw [empiricalMeasureOfFintype_toMeasure, ae_finsetSum_measure_iff]
  intro i _
  exact Measure.ae_smul_measure (by simp) _

end FinitePopulation

/-- The empirical probability measure of the first `n + 1` terms of a sequence.

This is the `κ := Fin (n + 1)` case of `empiricalMeasureOfFintype`; the successor indexing is what
supplies the `Nonempty` instance, so no side condition is needed. -/
def empiricalMeasure (x : ℕ → α) (n : ℕ) : ProbabilityMeasure α :=
  empiricalMeasureOfFintype (fun i : Fin (n + 1) => x i)

/-- The measure underlying an empirical measure is the uniform finite sum of Dirac measures. -/
@[simp]
theorem empiricalMeasure_toMeasure (x : ℕ → α) (n : ℕ) : (empiricalMeasure x n : Measure α) =
      ∑ i ∈ Finset.range (n + 1), (((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (x i)) := by
  rw [empiricalMeasure, empiricalMeasureOfFintype_toMeasure]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range
    (fun i => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (x i)) (n + 1)

/-- An empirical measure is concentrated on a finite set. -/
theorem exists_finset_ae_mem_empiricalMeasure [MeasurableSingletonClass α]
    (x : ℕ → α) (n : ℕ) :
    ∃ s : Finset α, ∀ᵐ y ∂(empiricalMeasure x n : Measure α), y ∈ s :=
  exists_finset_ae_mem_empiricalMeasureOfFintype _

/-- Evaluation of an empirical measure on a measurable set is its empirical frequency. -/
theorem empiricalMeasure_apply {x : ℕ → α} {n : ℕ} {s : Set α} (hs : MeasurableSet s) :
    (empiricalMeasure x n : Measure α) s = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), s.indicator (1 : α → ℝ≥0∞) (x i) := by
  rw [empiricalMeasure_toMeasure]
  simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hs, Finset.mul_sum]

/-- The real-valued form of `empiricalMeasure_apply`. -/
theorem empiricalMeasure_apply_toReal {x : ℕ → α} {n : ℕ} {s : Set α} (hs : MeasurableSet s) :
    ((empiricalMeasure x n : Measure α) s).toReal = ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), s.indicator (1 : α → ℝ) (x i) := by
  rw [empiricalMeasure_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv]
  · rw [ENNReal.toReal_natCast, ENNReal.toReal_sum]
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hxi : x i ∈ s <;> simp [hxi]
    · intro i _
      by_cases hxi : x i ∈ s <;> simp [hxi]

omit [MeasurableSpace Ω] in
/-- Evaluation of a path's empirical measure, written as indicators on the sample space. -/
theorem empiricalMeasure_process_apply_toReal {X : ℕ → Ω → α} {ω : Ω} {n : ℕ}
    {s : Set α} (hs : MeasurableSet s) :
    ((empiricalMeasure (fun i => X i ω) n : Measure α) s).toReal = ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), (X i ⁻¹' s).indicator (1 : Ω → ℝ) ω := by
  rw [empiricalMeasure_apply_toReal hs]
  refine congrArg (fun z : ℝ => ((n + 1 : ℕ) : ℝ)⁻¹ * z) ?_
  apply Finset.sum_congr rfl
  intro i _
  by_cases hxi : X i ω ∈ s <;> simp [hxi]

/-- Integrating against an empirical measure is averaging over the sampled values. -/
theorem integral_empiricalMeasure [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {x : ℕ → α} {n : ℕ} {f : α → E} (hf : StronglyMeasurable f) :
    ∫ y, f y ∂(empiricalMeasure x n : Measure α) =
      ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (n + 1), f (x i) := by
  rw [empiricalMeasure_toMeasure, integral_finsetSum_measure]
  · simp_rw [integral_smul_measure, integral_dirac' f _ hf]
    rw [← Finset.smul_sum]
    congr 1
    rw [ENNReal.toReal_inv]
    norm_cast
  · intro i _
    exact (integrable_dirac' hf (by simp)).smul_measure (by simp)

/-- The Lebesgue integral against an empirical measure is the average of the sampled values. -/
theorem lintegral_empiricalMeasure {x : ℕ → α} {n : ℕ} {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(empiricalMeasure x n : Measure α) =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range (n + 1), f (x i) := by
  simp [lintegral_finsetSum_measure, lintegral_dirac' _ hf, Finset.mul_sum]

/-- Empirical measures depend measurably on a sequence of measurable observations. -/
theorem measurable_empiricalMeasure {X : ℕ → Ω → α}
    (n : ℕ) (hX : ∀ i ∈ Finset.range (n + 1), Measurable (X i)) :
    Measurable fun ω => empiricalMeasure (fun i => X i ω) n := by
  have hmeasure : Measurable fun ω =>
      (empiricalMeasure (fun i => X i ω) n : Measure α) := by
    simp_rw [empiricalMeasure_toMeasure]
    exact Finset.measurable_fun_sum _ fun i hi =>
      Measure.measurable_of_measurable_coe _ fun s hs => by
        simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
        exact measurable_const.mul (measurable_one.indicator (hX i hi hs))
  exact hmeasure.subtype_mk

end Probability

end TauCeti
