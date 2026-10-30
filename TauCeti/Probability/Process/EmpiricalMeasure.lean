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
# Empirical measures of sequences

This file defines the empirical finite measure `|κ|⁻¹ ∑ᵢ δ_{xᵢ}` of a family indexed by an
arbitrary finite type (`empiricalFiniteMeasure`). It is the zero measure for an empty family, is
invariant under reindexing, averages under concatenation with weights given by the sizes of the
pieces, commutes with pushforward, and depends measurably on the family. Empirical spectral
measures of matrices are built from it.

For a nonempty finite population it is bundled as the empirical probability measure
`empiricalMeasureOfFintype` and, as its `κ := Fin (n + 1)` case, of the first `n + 1` terms of a
sequence (`empiricalMeasure`), together with their evaluation, integration, and measurability API.
The API also records that empirical measures have finite support. The successor indexing is what
supplies the `Nonempty` instance for the sequence form, so it needs no side condition, and it
matches the shape used in limit theorems.

There is one construction, not three: the probability measures are *defined* from the empirical
finite measure, and the sequence form as a specialization, so they can never drift apart.

The probability measure `empiricalMeasureOfFintype` is the finite-population form used by
quantitative sampling arguments.

The construction is a uniform finite sum of Dirac measures.  It is the process-level prerequisite
for the empirical-measure form of de Finetti's theorem in the `Exchangeability` roadmap.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α Ω E : Type*} [MeasurableSpace α] [MeasurableSpace Ω]


section FiniteFamily

variable {κ κ' : Type*} [Fintype κ] [Fintype κ']

/-- The empirical finite measure `|κ|⁻¹ ∑ᵢ δ_{xᵢ}` of a family `x : κ → α` indexed by an arbitrary
finite type. It is a probability measure when `κ` is nonempty, and the zero measure when `κ` is
empty. -/
def empiricalFiniteMeasure (x : κ → α) : Measure α :=
  ∑ i, ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (x i)

theorem empiricalFiniteMeasure_def (x : κ → α) :
    empiricalFiniteMeasure x = ∑ i, ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (x i) :=
  (rfl)

/-- The empirical finite measure of an empty family is zero. -/
@[simp]
theorem empiricalFiniteMeasure_of_isEmpty [IsEmpty κ] (x : κ → α) :
    empiricalFiniteMeasure x = 0 := by
  simp [empiricalFiniteMeasure_def]

/-- Scaling the empirical finite measure by the size of the family recovers the sum of its Dirac
masses. This also holds for the empty family, where both sides vanish. -/
theorem card_smul_empiricalFiniteMeasure (x : κ → α) :
    ((Fintype.card κ : ℕ) : ℝ≥0∞) • empiricalFiniteMeasure x = ∑ i, Measure.dirac (x i) := by
  cases isEmpty_or_nonempty κ
  · simp
  · rw [empiricalFiniteMeasure_def, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ENNReal.mul_inv_cancel (by simp) (by simp), one_smul]

instance isProbabilityMeasure_empiricalFiniteMeasure [Nonempty κ] (x : κ → α) :
    IsProbabilityMeasure (empiricalFiniteMeasure x) := by
  refine ⟨?_⟩
  have hκ0 : ((Fintype.card κ : ℕ) : ℝ≥0∞) ≠ 0 := by simp
  have hκtop : ((Fintype.card κ : ℕ) : ℝ≥0∞) ≠ ∞ := by simp
  simpa [empiricalFiniteMeasure_def] using ENNReal.mul_inv_cancel hκ0 hκtop

instance isFiniteMeasure_empiricalFiniteMeasure (x : κ → α) :
    IsFiniteMeasure (empiricalFiniteMeasure x) := by
  cases isEmpty_or_nonempty κ
  · rw [empiricalFiniteMeasure_of_isEmpty]
    infer_instance
  · infer_instance

/-- Evaluation of an empirical finite measure on a measurable set is the empirical frequency of
the set. -/
theorem empiricalFiniteMeasure_apply {x : κ → α} {s : Set α} (hs : MeasurableSet s) :
    empiricalFiniteMeasure x s =
      ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, s.indicator (1 : α → ℝ≥0∞) (x i) := by
  simp only [empiricalFiniteMeasure_def, Measure.coe_finsetSum, Measure.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs, Finset.mul_sum]

/-- The empirical finite measure is invariant under reindexing the family by an equivalence. -/
@[simp]
theorem empiricalFiniteMeasure_comp_equiv (x : κ → α) (e : κ' ≃ κ) :
    empiricalFiniteMeasure (x ∘ e) = empiricalFiniteMeasure x := by
  simp only [empiricalFiniteMeasure_def, Fintype.card_congr e, Function.comp_apply]
  exact e.sum_comp fun i => ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (x i)

/-- The empirical finite measure of a concatenation is the average of the empirical finite
measures of the two pieces, weighted by their sizes. -/
theorem empiricalFiniteMeasure_sum_elim (x : κ → α) (y : κ' → α) :
    empiricalFiniteMeasure (Sum.elim x y) =
      (((Fintype.card κ : ℕ) : ℝ≥0∞) + Fintype.card κ')⁻¹ •
        (((Fintype.card κ : ℕ) : ℝ≥0∞) • empiricalFiniteMeasure x +
          ((Fintype.card κ' : ℕ) : ℝ≥0∞) • empiricalFiniteMeasure y) := by
  rw [card_smul_empiricalFiniteMeasure, card_smul_empiricalFiniteMeasure,
    empiricalFiniteMeasure_def, Fintype.sum_sum_type, Fintype.card_sum, Nat.cast_add, smul_add,
    Finset.smul_sum, Finset.smul_sum]
  simp

/-- The pushforward of an empirical finite measure along a measurable map is the empirical finite
measure of the image family. -/
theorem map_empiricalFiniteMeasure {β : Type*} [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (x : κ → α) :
    (empiricalFiniteMeasure x).map f = empiricalFiniteMeasure (f ∘ x) := by
  rw [empiricalFiniteMeasure_def, empiricalFiniteMeasure_def,
    ← Measure.mapₗ_apply_of_measurable hf, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Measure.mapₗ_apply_of_measurable hf, Measure.map_dirac' hf, Function.comp_apply]

/-- Integrating against an empirical finite measure averages the integrand over the family. -/
theorem integral_empiricalFiniteMeasure' [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {x : κ → α} {f : α → E} (hf : StronglyMeasurable f) :
    ∫ y, f y ∂empiricalFiniteMeasure x = ((Fintype.card κ : ℕ) : ℝ)⁻¹ • ∑ i, f (x i) := by
  rw [empiricalFiniteMeasure_def, integral_finsetSum_measure]
  · simp_rw [integral_smul_measure, integral_dirac' f _ hf]
    rw [← Finset.smul_sum, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · intro i _
    have : Nonempty κ := ⟨i⟩
    exact (integrable_dirac' hf (by simp)).smul_measure (by simp)

/-- Integrating against an empirical finite measure averages the integrand over the family. This
version needs no measurability of the integrand, since points are measurable. -/
theorem integral_empiricalFiniteMeasure [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSingletonClass α] (x : κ → α) (f : α → E) :
    ∫ y, f y ∂empiricalFiniteMeasure x = ((Fintype.card κ : ℕ) : ℝ)⁻¹ • ∑ i, f (x i) := by
  rw [empiricalFiniteMeasure_def, integral_finsetSum_measure]
  · simp_rw [integral_smul_measure, integral_dirac]
    rw [← Finset.smul_sum, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · intro i _
    have : Nonempty κ := ⟨i⟩
    exact (integrable_dirac (by simp)).smul_measure (by simp)

/-- The Lebesgue integral against an empirical finite measure is the average of the values. -/
theorem lintegral_empiricalFiniteMeasure {x : κ → α} {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂empiricalFiniteMeasure x =
      ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, f (x i) := by
  simp [empiricalFiniteMeasure_def, lintegral_finsetSum_measure, lintegral_dirac' _ hf,
    Finset.mul_sum]

/-- The empirical finite measure depends measurably on the family. -/
theorem measurable_empiricalFiniteMeasure :
    Measurable (empiricalFiniteMeasure : (κ → α) → Measure α) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [empiricalFiniteMeasure_apply hs]
  fun_prop

end FiniteFamily

section FinitePopulation

variable {κ : Type*} [Fintype κ] [Nonempty κ]

/-- The empirical probability measure of a nonempty finite population `x : κ → α`, bundling the
empirical finite measure `empiricalFiniteMeasure x`.

Unlike `empiricalMeasure`, its population can have an arbitrary nonempty finite index type rather
than a natural-number prefix. -/
def empiricalMeasureOfFintype (x : κ → α) : ProbabilityMeasure α :=
  ⟨empiricalFiniteMeasure x, inferInstance⟩

/-- The measure underlying a finite empirical population is its empirical finite measure. -/
@[simp]
theorem empiricalMeasureOfFintype_toMeasure (x : κ → α) :
    (empiricalMeasureOfFintype x : Measure α) = empiricalFiniteMeasure x :=
  (rfl)

/-- Evaluation of a finite empirical population on a measurable set is its empirical
frequency. -/
theorem empiricalMeasureOfFintype_apply {x : κ → α} {s : Set α} (hs : MeasurableSet s) :
    (empiricalMeasureOfFintype x : Measure α) s = ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ *
      ∑ i, s.indicator (1 : α → ℝ≥0∞) (x i) := by
  rw [empiricalMeasureOfFintype_toMeasure, empiricalFiniteMeasure_apply hs]

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
    [CompleteSpace E] {x : κ → α} {f : α → E} (hf : StronglyMeasurable f) :
    ∫ y, f y ∂(empiricalMeasureOfFintype x : Measure α) =
      ((Fintype.card κ : ℕ) : ℝ)⁻¹ • ∑ i, f (x i) := by
  rw [empiricalMeasureOfFintype_toMeasure, integral_empiricalFiniteMeasure' hf]

/-- The Lebesgue integral against a finite empirical population is the average of the values. -/
theorem lintegral_empiricalMeasureOfFintype {x : κ → α} {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(empiricalMeasureOfFintype x : Measure α) =
      ((Fintype.card κ : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, f (x i) := by
  rw [empiricalMeasureOfFintype_toMeasure, lintegral_empiricalFiniteMeasure hf]

/-- Finite empirical distributions depend measurably on the population. -/
theorem measurable_empiricalMeasureOfFintype :
    Measurable (empiricalMeasureOfFintype : (κ → α) → ProbabilityMeasure α) :=
  measurable_empiricalFiniteMeasure.subtype_mk

/-- A finite empirical population is concentrated on the finite set of its values. -/
theorem exists_finset_ae_mem_empiricalMeasureOfFintype [MeasurableSingletonClass α]
    (x : κ → α) :
    ∃ s : Finset α, ∀ᵐ y ∂(empiricalMeasureOfFintype x : Measure α), y ∈ s := by
  classical
  refine ⟨Finset.univ.image x, ?_⟩
  rw [empiricalMeasureOfFintype_toMeasure, empiricalFiniteMeasure_def, ae_finsetSum_measure_iff]
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
  rw [empiricalMeasure, empiricalMeasureOfFintype_toMeasure, empiricalFiniteMeasure_def]
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
