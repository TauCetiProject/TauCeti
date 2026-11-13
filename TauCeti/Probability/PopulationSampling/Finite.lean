/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Alexander Richard Towell
-/
module

public import TauCeti.Probability.PopulationSampling.Basic
public import TauCeti.Probability.Process.EmpiricalMeasure
public import TauCeti.Probability.UniformSampling
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Sampling finite populations with and without replacement

For a random finite population `x : κ → α` with law `ρ`, both sampling laws use
`samplePopulation`: draw an independent selection `k : ι → κ` and return `x ∘ k`.
`sampleWithoutReplacement` uses the uniform law on injective selections;
`sampleWithReplacement` uses independent uniform indices, equivalently the uniform law on all
selections. Neither construction assumes symmetry of the population law.

For a nonempty population index, sampling with replacement is the mixture over `ρ` of the finite
product laws of the empirical measures `empiricalMeasureOfFintype x`. The collision bound gives the
two eventwise comparisons between sampling with and without replacement, with error equal to
the uniform-measure mass of colliding index selections, and hence at most `choose |ι| 2 / |κ|`.
This mass is a collision probability when the selection space is nonempty.
These comparisons apply to arbitrary probability population laws and feed
quantitative approximation results for finite exchangeable processes.

If no injective selection exists, sampling without replacement is the zero measure. Sampling
with replacement is also zero when the population index is empty and the sample index is not.
Probability preservation is therefore stated with an embedding into the population index for
sampling without replacement, and with a nonempty selection space `ι → κ` for sampling with
replacement, including when both index types are empty.

Measurable observations of population values commute with both sampling laws. For deterministic
populations, this expresses sampling a population that factors through another as a pushforward
of the latter's sampling law, without separation assumptions on the value space.

## Main declarations

* `sampleWithoutReplacement`, `sampleWithReplacement`: the two finite sampling laws;
* `sampleWithoutReplacement_map`, `sampleWithReplacement_map`: measurable observations commute
  with sampling;
* `sampleWithoutReplacement_dirac_comp`, `sampleWithReplacement_dirac_comp`: their
  deterministic-population composition forms;
* `sampleWithoutReplacement_dirac_apply_singleton`,
  `sampleWithReplacement_dirac_apply_singleton`: singleton masses of sampled words as fibre counts;
* `pi_empiricalMeasureOfFintype_eq_map_uniformOn`: independent empirical draws as uniform
  selections;
* `sampleWithReplacement_eq_bind_pi_empiricalMeasureOfFintype`: the empirical-product mixture;
* `sampleWithoutReplacement_le_sampleWithReplacement_add`,
  `sampleWithReplacement_le_sampleWithoutReplacement_add`: the eventwise collision bounds.
* `sampleWithoutReplacement_le_sampleWithReplacement_add_collision`,
  `sampleWithReplacement_le_sampleWithoutReplacement_add_collision`: the stronger bounds that
  retain the exact collision event, before applying the union bound.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The law obtained by sampling a random finite population without replacement.

First draw a population `x : κ → α` with law `ρ`; independently and uniformly draw an injective
selection `k : ι → κ`; then return the sample `i ↦ x (k i)`. This is `samplePopulation` along the
uniform law on injective index maps. If no injective selection exists, Mathlib's `uniformOn`
convention makes this the zero measure.

The results below take the population index finite with measurable singletons: uniform counting
then distributes mass over finitely many injective selections. -/
def sampleWithoutReplacement {ι κ : Type*} [MeasurableSpace κ] (ρ : Measure (κ → α)) :
    Measure (ι → α) :=
  samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ

/-- Sampling without replacement is `samplePopulation` along uniform injective selections. -/
theorem sampleWithoutReplacement_def {ι κ : Type*} [MeasurableSpace κ] (ρ : Measure (κ → α)) :
    sampleWithoutReplacement (ι := ι) ρ =
      samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ :=
  (rfl)

/-- Sampling a deterministic population without replacement is the pushforward of uniform
injective selections. -/
@[simp]
theorem sampleWithoutReplacement_dirac {ι κ : Type*} [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (x : κ → α) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac x) =
      (uniformOn {k : ι → κ | Function.Injective k}).map (fun k i => x (k i)) := by
  rw [sampleWithoutReplacement_def, samplePopulation_dirac]

/-- Observing population values commutes with sampling without replacement. -/
theorem sampleWithoutReplacement_map {ι κ : Type*} [MeasurableSpace κ]
    [MeasurableSingletonClass κ] [Countable κ] (ρ : Measure (κ → α)) [SFinite ρ]
    {g : α → β} (hg : Measurable g) :
    sampleWithoutReplacement (ι := ι) (ρ.map (fun x i => g (x i))) =
      (sampleWithoutReplacement (ι := ι) ρ).map (fun y i => g (y i)) := by
  simp only [sampleWithoutReplacement_def, samplePopulation_map _ _ hg]

/-- Sampling an observed deterministic population without replacement is the observation's
pushforward of the original sampling law. -/
theorem sampleWithoutReplacement_dirac_comp {ι κ : Type*} [MeasurableSpace κ]
    [MeasurableSingletonClass κ] [Countable κ] (x : κ → α)
    {g : α → β} (hg : Measurable g) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (g ∘ x)) =
      (sampleWithoutReplacement (ι := ι) (Measure.dirac x)).map (fun y i => g (y i)) := by
  simp only [sampleWithoutReplacement_def, samplePopulation_dirac_comp _ _ hg]

/-- Sampling without replacement preserves probability mass whenever an injective selection
exists. -/
theorem isProbabilityMeasure_sampleWithoutReplacement {ι κ : Type*} [Finite κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] (ρ : Measure (κ → α))
    [IsProbabilityMeasure ρ] (e : ι ↪ κ) :
    IsProbabilityMeasure
      (sampleWithoutReplacement (ι := ι) (κ := κ) (α := α) ρ) := by
  have : Finite ι := Finite.of_injective e e.injective
  let E : Set (ι → κ) := {k | Function.Injective k}
  let _ : IsProbabilityMeasure (uniformOn E) :=
    isProbabilityMeasure_uniformOn (Set.toFinite E) ⟨e, e.injective⟩
  rw [sampleWithoutReplacement_def]
  infer_instance

section EmpiricalPopulation

variable {κ : Type*} [Fintype κ] [Nonempty κ] [MeasurableSpace κ]
  [MeasurableSingletonClass κ]

variable {ι : Type*} [Fintype ι]

/-- Independently sampling from a finite empirical population is the same as choosing a uniform
map into the population and reading the selected entries. -/
theorem pi_empiricalMeasureOfFintype_eq_map_uniformOn (x : κ → α) :
    (ProbabilityMeasure.pi fun _ : ι => empiricalMeasureOfFintype x).toMeasure =
      (uniformOn (Set.univ : Set (ι → κ))).map fun k i => x (k i) := by
  rw [ProbabilityMeasure.toMeasure_pi]
  simp_rw [empiricalMeasureOfFintype_eq_map_uniformOn]
  rw [← Measure.pi_map_pi fun _ : ι => (measurable_of_countable x).aemeasurable]
  rw [← uniformOn_pi (f := fun _ : ι => (Set.univ : Set κ))]
  congr 2
  simp

end EmpiricalPopulation

section Sampling

variable {ι κ : Type*} [MeasurableSpace κ]

/-- Sampling with replacement from a random finite population.

First draw a population `x : κ → α` with law `ρ`; independently draw the indices `k i : κ`,
`i : ι`, independently and uniformly; then return the sample `i ↦ x (k i)`. This is
`samplePopulation` along the `ι`-fold product of the uniform law on `κ`, which is the uniform law
on all index maps (`sampleWithReplacement_eq_samplePopulation_uniformOn`): the same construction
as `sampleWithoutReplacement` without the injectivity constraint. If `κ` is empty but `ι` is not,
no index map exists, and Mathlib's `uniformOn` convention makes this the zero measure.

The sample index is finite because the selection law is a finite product. Apart from the
finite-law instance, the results below take the population index finite with measurable
singletons. -/
def sampleWithReplacement [Fintype ι] (ρ : Measure (κ → α)) : Measure (ι → α) :=
  samplePopulation (Measure.pi fun _ : ι => uniformOn (Set.univ : Set κ)) ρ

/-- Sampling with replacement is `samplePopulation` along independent uniform indices. -/
theorem sampleWithReplacement_def [Fintype ι] (ρ : Measure (κ → α)) :
    sampleWithReplacement (ι := ι) ρ =
      samplePopulation (Measure.pi fun _ : ι => uniformOn (Set.univ : Set κ)) ρ :=
  (rfl)

/-- Sampling with replacement from a finite population law gives a finite law. -/
instance isFiniteMeasure_sampleWithReplacement [Fintype ι] (ρ : Measure (κ → α))
    [IsFiniteMeasure ρ] : IsFiniteMeasure (sampleWithReplacement (ι := ι) ρ) := by
  rw [sampleWithReplacement_def]
  infer_instance

variable [MeasurableSingletonClass κ]

/-- Sampling with replacement is `samplePopulation` along the uniform law on all index maps. -/
theorem sampleWithReplacement_eq_samplePopulation_uniformOn [Fintype ι] [Finite κ]
    (ρ : Measure (κ → α)) :
    sampleWithReplacement (ι := ι) ρ = samplePopulation (uniformOn (Set.univ : Set (ι → κ))) ρ := by
  rw [sampleWithReplacement_def, ← uniformOn_pi, Set.pi_univ]

/-- Sampling a deterministic population with replacement is the pushforward of uniform
selections, without an injectivity constraint. -/
@[simp]
theorem sampleWithReplacement_dirac [Fintype ι] [Finite κ] (x : κ → α) :
    sampleWithReplacement (ι := ι) (Measure.dirac x) =
      (uniformOn (Set.univ : Set (ι → κ))).map (fun k i => x (k i)) := by
  rw [sampleWithReplacement_eq_samplePopulation_uniformOn, samplePopulation_dirac]

/-- Observing population values commutes with sampling with replacement. -/
theorem sampleWithReplacement_map [Fintype ι] [Countable κ]
    (ρ : Measure (κ → α)) [SFinite ρ] {g : α → β} (hg : Measurable g) :
    sampleWithReplacement (ι := ι) (ρ.map (fun x i => g (x i))) =
      (sampleWithReplacement (ι := ι) ρ).map (fun y i => g (y i)) := by
  simp only [sampleWithReplacement_def, samplePopulation_map _ _ hg]

/-- Sampling an observed deterministic population with replacement is the observation's
pushforward of the original sampling law. -/
theorem sampleWithReplacement_dirac_comp [Fintype ι] [Countable κ] (x : κ → α)
    {g : α → β} (hg : Measurable g) :
    sampleWithReplacement (ι := ι) (Measure.dirac (g ∘ x)) =
      (sampleWithReplacement (ι := ι) (Measure.dirac x)).map (fun y i => g (y i)) := by
  simp only [sampleWithReplacement_def, samplePopulation_dirac_comp _ _ hg]

/-- Sampling with replacement from a random population preserves probability mass whenever a
selection exists. -/
theorem isProbabilityMeasure_sampleWithReplacement [Fintype ι] [Finite κ] [Nonempty (ι → κ)]
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (sampleWithReplacement (ι := ι) ρ) := by
  rw [sampleWithReplacement_eq_samplePopulation_uniformOn]
  infer_instance

/-- Sampling with replacement is the mixture of the finite product measures of the populations'
empirical distributions. -/
theorem sampleWithReplacement_eq_bind_pi_empiricalMeasureOfFintype [Fintype ι] [Fintype κ]
    [Nonempty κ] (ρ : Measure (κ → α)) [SFinite ρ] :
    sampleWithReplacement ρ =
      ρ.bind fun x =>
        (ProbabilityMeasure.pi fun _ : ι => empiricalMeasureOfFintype x).toMeasure := by
  simp_rw [sampleWithReplacement_eq_samplePopulation_uniformOn,
    samplePopulation_eq_bind_population, pi_empiricalMeasureOfFintype_eq_map_uniformOn]

section Singletons

variable [Fintype ι] [Fintype κ] [MeasurableSingletonClass α]

/-- For a deterministic population `x : κ → α`, the mass of a word `y : ι → α` under sampling
without replacement is the number of embeddings `f : ι ↪ κ` with `x ∘ f = y` divided by
`(card κ).descFactorial (card ι)`. When `card κ < card ι`, no embedding exists and both sides
vanish (since `(0 : ℝ≥0∞) / 0 = 0`). -/
theorem sampleWithoutReplacement_dirac_apply_singleton (x : κ → α) (y : ι → α) :
    sampleWithoutReplacement (Measure.dirac x) {y} =
      (Nat.card {f : ι ↪ κ // x ∘ f = y} : ℝ≥0∞) /
        (Fintype.card κ).descFactorial (Fintype.card ι) := by
  classical
  have hpre : (fun k : ι → κ => fun i => x (k i)) ⁻¹' {y} = {f : ι → κ | x ∘ f = y} := by
    ext f
    simp [Function.comp_def]
  have hinj : ({k : ι → κ | Function.Injective k} : Set (ι → κ)) =
      (({k : ι → κ | Function.Injective k} : Finset (ι → κ)) : Set (ι → κ)) := by
    simp
  have hevt : ({f : ι → κ | x ∘ f = y} : Set (ι → κ)) =
      (({f : ι → κ | x ∘ f = y} : Finset (ι → κ)) : Set (ι → κ)) := by
    simp
  have heq : {k : ι → κ // Function.Injective k ∧ x ∘ k = y} ≃ {f : ι ↪ κ // x ∘ f = y} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
      ((Equiv.subtypeInjectiveEquivEmbedding ι κ).subtypeEquiv fun _ => Iff.rfl)
  rw [sampleWithoutReplacement_dirac,
    Measure.map_apply (measurable_readPopulation x) (measurableSet_singleton y),
    hpre, hinj, hevt, uniformOn_apply_finset, ← Finset.filter_and,
    ← Fintype.card_subtype, ← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding ι κ), Fintype.card_embedding_eq,
    ← Nat.card_eq_fintype_card, Nat.card_congr heq]

/-- For a deterministic population `x : κ → α`, the mass of a word `y : ι → α` under sampling with
replacement is the number of index maps `f : ι → κ` with `x ∘ f = y` divided by
`(card κ) ^ (card ι)`. When `κ` is empty and `ι` is nonempty, both sides vanish. -/
theorem sampleWithReplacement_dirac_apply_singleton (x : κ → α) (y : ι → α) :
    sampleWithReplacement (Measure.dirac x) {y} =
      (Nat.card {f : ι → κ // x ∘ f = y} : ℝ≥0∞) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
  classical
  have hpre : (fun k : ι → κ => fun i => x (k i)) ⁻¹' {y} = {f : ι → κ | x ∘ f = y} := by
    ext f
    simp [Function.comp_def]
  rw [sampleWithReplacement_dirac,
    Measure.map_apply (measurable_readPopulation x) (measurableSet_singleton y),
    hpre, uniformOn_univ, Measure.count_apply_finite _ (Set.toFinite _),
    ← Set.ncard_eq_toFinset_card _, ← Nat.card_coe_set_eq, Set.coe_ofPred, Fintype.card_fun,
    Nat.cast_pow]

end Singletons

section Bounds

variable [Fintype ι] [Fintype κ]

omit [Fintype κ] in
/-- Sampling without replacement from a random finite population increases the mass of an
event by at most the uniform-measure mass of colliding index selections.
This mass is a collision probability when the selection space is nonempty. -/
theorem sampleWithoutReplacement_le_sampleWithReplacement_add_collision [Finite κ]
    {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    sampleWithoutReplacement ρ A ≤ sampleWithReplacement ρ A +
      uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k} := by
  -- First for measurable events, then for any event through a measurable hull.
  have key : ∀ B : Set (ι → α), MeasurableSet B →
      sampleWithoutReplacement ρ B ≤ sampleWithReplacement ρ B +
        uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k} := by
    intro B hB
    rw [sampleWithoutReplacement_def, sampleWithReplacement_eq_samplePopulation_uniformOn,
      samplePopulation_apply_population hB, samplePopulation_apply_population hB]
    let c := uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k}
    let f : (κ → α) → ℝ≥0∞ := fun x =>
      uniformOn (Set.univ : Set (ι → κ)) ((fun k i => x (k i)) ⁻¹' B)
    have hf : Measurable f := by
      exact measurable_measure_prodMk_right (measurable_reindexPopulation hB)
    calc
      (∫⁻ x, uniformOn {k : ι → κ | Function.Injective k}
          ((fun k i => x (k i)) ⁻¹' B) ∂ρ) ≤ ∫⁻ x, f x + c ∂ρ :=
        lintegral_mono fun x => uniformOn_injective_le_add _
      _ = (∫⁻ x, f x ∂ρ) + ∫⁻ _x, c ∂ρ := lintegral_add_left hf _
      _ = (∫⁻ x, f x ∂ρ) + c := by simp
  calc
    sampleWithoutReplacement ρ A
        ≤ sampleWithoutReplacement ρ (toMeasurable (sampleWithReplacement ρ) A) :=
      measure_mono (subset_toMeasurable _ _)
    _ ≤ sampleWithReplacement ρ (toMeasurable (sampleWithReplacement ρ) A) + _ :=
      key _ (measurableSet_toMeasurable _ _)
    _ = sampleWithReplacement ρ A + _ := by rw [measure_toMeasurable]

omit [Fintype κ] in
/-- Sampling with replacement from a random finite population increases the mass of an
event by at most the uniform-measure mass of colliding index selections.
This mass is a collision probability when the selection space is nonempty. -/
theorem sampleWithReplacement_le_sampleWithoutReplacement_add_collision [Finite κ]
    {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    sampleWithReplacement ρ A ≤ sampleWithoutReplacement ρ A +
      uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k} := by
  -- First for measurable events, then for any event through a measurable hull.
  have key : ∀ B : Set (ι → α), MeasurableSet B →
      sampleWithReplacement ρ B ≤ sampleWithoutReplacement ρ B +
        uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k} := by
    intro B hB
    rw [sampleWithoutReplacement_def, sampleWithReplacement_eq_samplePopulation_uniformOn,
      samplePopulation_apply_population hB, samplePopulation_apply_population hB]
    let c := uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k}
    let f : (κ → α) → ℝ≥0∞ := fun x =>
      uniformOn {k : ι → κ | Function.Injective k} ((fun k i => x (k i)) ⁻¹' B)
    have hf : Measurable f := by
      exact measurable_measure_prodMk_right (measurable_reindexPopulation hB)
    calc
      (∫⁻ x, uniformOn (Set.univ : Set (ι → κ))
          ((fun k i => x (k i)) ⁻¹' B) ∂ρ) ≤ ∫⁻ x, f x + c ∂ρ :=
        lintegral_mono fun x => uniformOn_univ_le_injective_add _
      _ = (∫⁻ x, f x ∂ρ) + ∫⁻ _x, c ∂ρ := lintegral_add_left hf _
      _ = (∫⁻ x, f x ∂ρ) + c := by simp
  calc
    sampleWithReplacement ρ A
        ≤ sampleWithReplacement ρ (toMeasurable (sampleWithoutReplacement ρ) A) :=
      measure_mono (subset_toMeasurable _ _)
    _ ≤ sampleWithoutReplacement ρ (toMeasurable (sampleWithoutReplacement ρ) A) + _ :=
      key _ (measurableSet_toMeasurable _ _)
    _ = sampleWithoutReplacement ρ A + _ := by rw [measure_toMeasurable]

/-- **Finite sampling bound, without replacement to with replacement.** For every event,
sampling without replacement from a random finite population has mass at most its
with-replacement mass plus the collision bound `choose |ι| 2 / |κ|`. -/
theorem sampleWithoutReplacement_le_sampleWithReplacement_add
    {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    sampleWithoutReplacement ρ A ≤ sampleWithReplacement ρ A +
      (Fintype.card ι).choose 2 / Fintype.card κ :=
  (sampleWithoutReplacement_le_sampleWithReplacement_add_collision A).trans
    (add_le_add le_rfl uniformOn_not_injective_le)

/-- **Finite sampling bound, with replacement to without replacement.** For every event,
sampling with replacement from a random finite population has mass at most its
without-replacement mass plus the collision bound `choose |ι| 2 / |κ|`. -/
theorem sampleWithReplacement_le_sampleWithoutReplacement_add
    {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    sampleWithReplacement ρ A ≤ sampleWithoutReplacement ρ A +
      (Fintype.card ι).choose 2 / Fintype.card κ :=
  (sampleWithReplacement_le_sampleWithoutReplacement_add_collision A).trans
    (add_le_add le_rfl uniformOn_not_injective_le)

end Bounds

end Sampling

end Probability

end TauCeti
