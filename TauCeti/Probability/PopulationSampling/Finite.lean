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
* `sampleWithoutReplacement_dirac_apply`, `sampleWithoutReplacement_dirac_apply_singleton`,
  `sampleWithReplacement_dirac_apply`, `sampleWithReplacement_dirac_apply_singleton`:
  event and singleton masses of sampled words as selection counts;
* `sampleWithoutReplacement_map`, `sampleWithReplacement_map`: measurable observations commute
  with sampling;
* `sampleWithoutReplacement_dirac_comp`, `sampleWithReplacement_dirac_comp`: their
  deterministic-population composition forms;
* `sampleWithoutReplacement_dirac_const`, `sampleWithReplacement_dirac_const`: a constant
  population is sampled as its constant word;
* `pi_empiricalMeasureOfFintype_eq_map_uniformOn`: independent empirical draws as uniform
  selections;
* `sampleWithReplacement_eq_bind_pi_empiricalMeasureOfFintype`: the empirical-product mixture;
* `sampleWithoutReplacement_le_sampleWithReplacement_add`,
  `sampleWithReplacement_le_sampleWithoutReplacement_add`: the eventwise collision bounds;
* `sampleWithoutReplacement_le_sampleWithReplacement_add_collision`,
  `sampleWithReplacement_le_sampleWithoutReplacement_add_collision`,
  `sampleWithoutReplacement_le_sampleWithReplacement_add_exact_collision`,
  `sampleWithReplacement_le_sampleWithoutReplacement_add_exact_collision`: the stronger bounds
  retaining the exact index-collision event and its falling-factorial formula;
* `sampleWithoutReplacement_eq_zero_of_isEmpty`, `sampleWithoutReplacement_eq_zero_of_card_lt`,
  `sampleWithReplacement_eq_zero_of_isEmpty`,
  `sampleWithoutReplacement_eq_sampleWithReplacement_of_subsingleton`: the infeasible and
  subsingleton-sample regimes.

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

Deterministic evaluation, probability-mass preservation, subsingleton-sample agreement, and
collision bounds below take `[Finite κ] [MeasurableSingletonClass κ]` (with `[Countable κ]`
sufficing for measurable observations), whereas finite-measure preservation and
infeasible-selection vanishing (`sampleWithoutReplacement_eq_zero_of_isEmpty`) require neither
(and `sampleWithoutReplacement_eq_zero_of_card_lt` needs only `[Fintype κ]`). -/
def sampleWithoutReplacement {ι κ : Type*} [MeasurableSpace κ] (ρ : Measure (κ → α)) :
    Measure (ι → α) :=
  samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ

/-- Sampling without replacement is `samplePopulation` along uniform injective selections. -/
theorem sampleWithoutReplacement_def {ι κ : Type*} [MeasurableSpace κ] (ρ : Measure (κ → α)) :
    sampleWithoutReplacement (ι := ι) ρ =
      samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ :=
  (rfl)

/-- Sampling without replacement from a finite population law gives a finite law. -/
instance isFiniteMeasure_sampleWithoutReplacement {ι κ : Type*} [MeasurableSpace κ]
    (ρ : Measure (κ → α)) [IsFiniteMeasure ρ] :
    IsFiniteMeasure (sampleWithoutReplacement (ι := ι) ρ) := by
  rw [sampleWithoutReplacement_def]
  infer_instance

/-- When no embedding `ι ↪ κ` exists, sampling without replacement is the zero measure. -/
@[simp high]
theorem sampleWithoutReplacement_eq_zero_of_isEmpty {ι κ : Type*} [MeasurableSpace κ]
    [IsEmpty (ι ↪ κ)] (ρ : Measure (κ → α)) :
    sampleWithoutReplacement (ι := ι) ρ = 0 := by
  simp [sampleWithoutReplacement_def]

/-- When the sample size exceeds the population size, no injective selection exists and sampling
without replacement is the zero measure. -/
theorem sampleWithoutReplacement_eq_zero_of_card_lt {ι κ : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace κ] (h : Fintype.card κ < Fintype.card ι) (ρ : Measure (κ → α)) :
    sampleWithoutReplacement (ι := ι) ρ = 0 := by
  have := Function.Embedding.isEmpty_of_card_lt h
  exact sampleWithoutReplacement_eq_zero_of_isEmpty ρ

/-- Sampling a deterministic population without replacement is the pushforward of uniform
injective selections. -/
@[simp]
theorem sampleWithoutReplacement_dirac {ι κ : Type*} [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (x : κ → α) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac x) =
      (uniformOn {k : ι → κ | Function.Injective k}).map (fun k i => x (k i)) := by
  rw [sampleWithoutReplacement_def, samplePopulation_dirac]

/-- Under without-replacement sampling from a deterministic finite population `x : κ → α`, the
mass of a measurable event `A` is the number of embeddings `f : ι ↪ κ` with `x ∘ f ∈ A` divided
by `|κ|.descFactorial |ι|`. When `|κ| < |ι|`, both sides are zero (`0 / 0 = 0` in `ℝ≥0∞`). -/
theorem sampleWithoutReplacement_dirac_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] (x : κ → α) {A : Set (ι → α)}
    (hA : MeasurableSet A) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac x) A =
      Nat.card {f : ι ↪ κ // x ∘ f ∈ A} /
        (Fintype.card κ).descFactorial (Fintype.card ι) := by
  classical
  simp only [sampleWithoutReplacement_dirac, Measure.map_apply (measurable_readPopulation x) hA]
  have hS : {k : ι → κ | Function.Injective k} =
      (({k : ι → κ | Function.Injective k} : Finset (ι → κ)) : Set (ι → κ)) := by simp
  have hT : (fun k i => x (k i)) ⁻¹' A =
      (({k : ι → κ | x ∘ k ∈ A} : Finset (ι → κ)) : Set (ι → κ)) := by
    ext k
    simp [Function.comp_def]
  have heq : {k : ι → κ // Function.Injective k ∧ x ∘ k ∈ A} ≃ {f : ι ↪ κ // x ∘ f ∈ A} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun k : ι → κ => Function.Injective k) (fun k : ι → κ => x ∘ k ∈ A)).symm.trans
      ((Equiv.subtypeInjectiveEquivEmbedding ι κ).subtypeEquiv fun _ => Iff.rfl)
  rw [← Nat.card_congr heq, hS, hT, uniformOn_apply_finset]
  simp [← Finset.filter_and, ← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding ι κ)]

/-- Under without-replacement sampling from a deterministic finite population `x : κ → α`, the
mass of a word `y : ι → α` is the number of embeddings `f : ι ↪ κ` with `x ∘ f = y` divided by
`|κ|.descFactorial |ι|`. When `|κ| < |ι|`, both sides are zero (`0 / 0 = 0` in `ℝ≥0∞`). -/
theorem sampleWithoutReplacement_dirac_apply_singleton {ι κ : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] [MeasurableSingletonClass α]
    (x : κ → α) (y : ι → α) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac x) {y} =
      Nat.card {f : ι ↪ κ // x ∘ f = y} /
        (Fintype.card κ).descFactorial (Fintype.card ι) :=
  sampleWithoutReplacement_dirac_apply x (measurableSet_singleton y)

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

/-- Sampling a constant population without replacement returns the constant word almost surely,
whenever an injective selection exists. -/
theorem sampleWithoutReplacement_dirac_const {ι κ : Type*} [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (e : ι ↪ κ) (c : α) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac fun _ : κ => c) =
      Measure.dirac fun _ => c := by
  have : Finite ι := Finite.of_injective e e.injective
  have := isProbabilityMeasure_uniformOn (Set.toFinite {k : ι → κ | Function.Injective k})
    ⟨e, e.injective⟩
  rw [sampleWithoutReplacement_dirac, Measure.map_const, measure_univ, one_smul]

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

The sample index is finite because the selection law is a finite product. Deterministic
evaluation, subsingleton-sample agreement, the empirical-product mixture, probability-mass
preservation, and collision bounds below take `[Finite κ] [MeasurableSingletonClass κ]` (with
`[Countable κ]` sufficing for measurable observations), whereas finite-measure preservation and
infeasible-selection vanishing require neither. -/
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

/-- When no selection `ι → κ` exists (i.e. `ι` is nonempty and `κ` is empty), sampling with
replacement is the zero measure. -/
@[simp high]
theorem sampleWithReplacement_eq_zero_of_isEmpty [Fintype ι] [IsEmpty (ι → κ)]
    (ρ : Measure (κ → α)) :
    sampleWithReplacement (ι := ι) ρ = 0 := by
  simp [sampleWithReplacement_def,
    Measure.eq_zero_of_isEmpty (Measure.pi fun _ : ι => uniformOn (Set.univ : Set κ))]

variable [MeasurableSingletonClass κ]

/-- Sampling with replacement is `samplePopulation` along the uniform law on all index maps. -/
theorem sampleWithReplacement_eq_samplePopulation_uniformOn [Fintype ι] [Finite κ]
    (ρ : Measure (κ → α)) :
    sampleWithReplacement (ι := ι) ρ = samplePopulation (uniformOn (Set.univ : Set (ι → κ))) ρ := by
  rw [sampleWithReplacement_def, ← uniformOn_pi, Set.pi_univ]

/-- On a subsingleton sample index (samples of size `0` or `1`), sampling without replacement and
sampling with replacement have the exact same law for every population law `ρ`. -/
@[simp]
theorem sampleWithoutReplacement_eq_sampleWithReplacement_of_subsingleton [Fintype ι]
    [Subsingleton ι] [Finite κ] (ρ : Measure (κ → α)) :
    sampleWithoutReplacement (ι := ι) ρ = sampleWithReplacement (ι := ι) ρ := by
  rw [sampleWithoutReplacement_def, sampleWithReplacement_eq_samplePopulation_uniformOn,
    uniformOn_injective_eq_uniformOn_univ_of_subsingleton]

/-- Sampling a deterministic population with replacement is the pushforward of uniform
selections, without an injectivity constraint. -/
@[simp]
theorem sampleWithReplacement_dirac [Fintype ι] [Finite κ] (x : κ → α) :
    sampleWithReplacement (ι := ι) (Measure.dirac x) =
      (uniformOn (Set.univ : Set (ι → κ))).map (fun k i => x (k i)) := by
  rw [sampleWithReplacement_eq_samplePopulation_uniformOn, samplePopulation_dirac]

/-- Under with-replacement sampling from a deterministic finite population `x : κ → α`, the
mass of a measurable event `A` is the number of index maps `f : ι → κ` with `x ∘ f ∈ A` divided
by `|κ| ^ |ι|`. When `ι → κ` is empty, both sides are zero (`0 / 0 = 0` in `ℝ≥0∞`). -/
theorem sampleWithReplacement_dirac_apply [Fintype ι] [Fintype κ] (x : κ → α)
    {A : Set (ι → α)} (hA : MeasurableSet A) :
    sampleWithReplacement (ι := ι) (Measure.dirac x) A =
      Nat.card {f : ι → κ // x ∘ f ∈ A} / (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
  classical
  have hpre : (fun k i => x (k i)) ⁻¹' A = {k : ι → κ | x ∘ k ∈ A} := by
    ext k
    simp [Function.comp_def]
  simp [Measure.map_apply (measurable_readPopulation x) hA, hpre, uniformOn_univ,
    Measure.count_apply_finite _ (Set.toFinite _), ← Fintype.card_subtype]

/-- Under with-replacement sampling from a deterministic finite population `x : κ → α`, the
mass of a word `y : ι → α` is the number of index maps `f : ι → κ` with `x ∘ f = y` divided by
`|κ| ^ |ι|`. When `ι → κ` is empty, both sides are zero (`0 / 0 = 0` in `ℝ≥0∞`). -/
theorem sampleWithReplacement_dirac_apply_singleton [Fintype ι] [Fintype κ]
    [MeasurableSingletonClass α] (x : κ → α) (y : ι → α) :
    sampleWithReplacement (ι := ι) (Measure.dirac x) {y} =
      Nat.card {f : ι → κ // x ∘ f = y} / (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι :=
  sampleWithReplacement_dirac_apply x (measurableSet_singleton y)

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

/-- Sampling a constant population with replacement returns the constant word almost surely,
whenever a selection exists. -/
theorem sampleWithReplacement_dirac_const [Fintype ι] [Finite κ] [Nonempty (ι → κ)] (c : α) :
    sampleWithReplacement (ι := ι) (Measure.dirac fun _ : κ => c) = Measure.dirac fun _ => c := by
  rw [sampleWithReplacement_dirac, Measure.map_const, measure_univ, one_smul]

/-- Sampling with replacement is the mixture of the finite product measures of the populations'
empirical distributions. -/
theorem sampleWithReplacement_eq_bind_pi_empiricalMeasureOfFintype [Fintype ι] [Fintype κ]
    [Nonempty κ] (ρ : Measure (κ → α)) [SFinite ρ] :
    sampleWithReplacement ρ =
      ρ.bind fun x =>
        (ProbabilityMeasure.pi fun _ : ι => empiricalMeasureOfFintype x).toMeasure := by
  simp_rw [sampleWithReplacement_eq_samplePopulation_uniformOn,
    samplePopulation_eq_bind_population, pi_empiricalMeasureOfFintype_eq_map_uniformOn]

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
  let c := uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k}
  rw [sampleWithoutReplacement_def, sampleWithReplacement_eq_samplePopulation_uniformOn]
  calc
    samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ A
        ≤ samplePopulation (uniformOn (Set.univ : Set (ι → κ))) ρ A + ∫⁻ _, c ∂ρ :=
          samplePopulation_le_add_lintegral (fun B hB => ae_of_all _ fun x => by
            rw [samplePopulation_dirac_apply hB, samplePopulation_dirac_apply hB]
            exact uniformOn_injective_le_add _) A
    _ = samplePopulation (uniformOn (Set.univ : Set (ι → κ))) ρ A + c := by simp

omit [Fintype κ] in
/-- Sampling with replacement from a random finite population increases the mass of an
event by at most the uniform-measure mass of colliding index selections.
This mass is a collision probability when the selection space is nonempty. -/
theorem sampleWithReplacement_le_sampleWithoutReplacement_add_collision [Finite κ]
    {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    sampleWithReplacement ρ A ≤ sampleWithoutReplacement ρ A +
      uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k} := by
  let c := uniformOn (Set.univ : Set (ι → κ)) {k | ¬ Function.Injective k}
  rw [sampleWithoutReplacement_def, sampleWithReplacement_eq_samplePopulation_uniformOn]
  calc
    samplePopulation (uniformOn (Set.univ : Set (ι → κ))) ρ A
        ≤ samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ A + ∫⁻ _, c ∂ρ :=
          samplePopulation_le_add_lintegral (fun B hB => ae_of_all _ fun x => by
            rw [samplePopulation_dirac_apply hB, samplePopulation_dirac_apply hB]
            exact uniformOn_univ_le_injective_add _) A
    _ = samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ A + c := by simp

/-- **Exact-collision finite sampling bound, without replacement to with replacement.** For every
event, sampling without replacement from a random finite population exceeds sampling with
replacement by at most `1 - (|κ|)_|ι| / |κ| ^ |ι|`. No nonemptiness assumption on `ι → κ` is
needed: when `ι → κ` is empty both sampling laws are zero and the error term is `1`. -/
theorem sampleWithoutReplacement_le_sampleWithReplacement_add_exact_collision
    {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    sampleWithoutReplacement ρ A ≤ sampleWithReplacement ρ A +
      (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) :=
  (sampleWithoutReplacement_le_sampleWithReplacement_add_collision A).trans
    (add_le_add le_rfl uniformOn_not_injective_le_one_sub_descFactorial_div_pow)

/-- **Exact-collision finite sampling bound, with replacement to without replacement.** For every
event, sampling with replacement from a random finite population exceeds sampling without
replacement by at most `1 - (|κ|)_|ι| / |κ| ^ |ι|`. -/
theorem sampleWithReplacement_le_sampleWithoutReplacement_add_exact_collision
    {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    sampleWithReplacement ρ A ≤ sampleWithoutReplacement ρ A +
      (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) :=
  (sampleWithReplacement_le_sampleWithoutReplacement_add_collision A).trans
    (add_le_add le_rfl uniformOn_not_injective_le_one_sub_descFactorial_div_pow)

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
