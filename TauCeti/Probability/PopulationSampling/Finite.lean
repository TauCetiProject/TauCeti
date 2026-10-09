/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
two eventwise comparisons between sampling with and without replacement, with error
`choose |ι| 2 / |κ|`. These comparisons apply to arbitrary probability population laws and feed
quantitative approximation results for finite exchangeable processes.

If no injective selection exists, sampling without replacement is the zero measure. Sampling
with replacement is also zero when the population index is empty and the sample index is not.
Probability preservation is therefore stated with an embedding into the population index for
sampling without replacement, and with a nonempty population index for sampling with replacement.

## Main declarations

* `sampleWithoutReplacement`, `sampleWithReplacement`: the two finite sampling laws;
* `pi_empiricalMeasureOfFintype_eq_map_uniformOn`: independent empirical draws as uniform
  selections;
* `sampleWithReplacement_eq_bind_pi_empiricalMeasureOfFintype`: the empirical-product mixture;
* `sampleWithoutReplacement_le_sampleWithReplacement_add`,
  `sampleWithReplacement_le_sampleWithoutReplacement_add`: the eventwise collision bounds.

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

variable {α : Type*} [MeasurableSpace α]

/-- The law obtained by sampling a random finite population without replacement.

First draw a population `x : κ → α` with law `ρ`; independently and uniformly draw an injective
selection `k : ι → κ`; then return the sample `i ↦ x (k i)`. This is `samplePopulation` along the
uniform law on injective index maps. If no injective selection exists, Mathlib's `uniformOn`
convention makes this the zero measure.

The population index is finite because uniform counting only distributes mass over finitely many
injective selections. -/
def sampleWithoutReplacement {ι κ : Type*} [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (ρ : Measure (κ → α)) : Measure (ι → α) :=
  samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ

/-- Sampling without replacement is `samplePopulation` along uniform injective selections. -/
theorem sampleWithoutReplacement_def {ι κ : Type*} [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (ρ : Measure (κ → α)) :
    sampleWithoutReplacement (ι := ι) ρ =
      samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ :=
  (rfl)

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

variable {ι κ : Type*} [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- Sampling with replacement from a random finite population.

First draw a population `x : κ → α` with law `ρ`; independently draw the indices `k i : κ`,
`i : ι`, independently and uniformly; then return the sample `i ↦ x (k i)`. This is
`samplePopulation` along the `ι`-fold product of the uniform law on `κ`, which is the uniform law
on all index maps (`sampleWithReplacement_eq_samplePopulation_uniformOn`): the same construction
as `sampleWithoutReplacement` without the injectivity constraint. If `κ` is empty but `ι` is not,
no index map exists, and Mathlib's `uniformOn` convention makes this the zero measure.

The sample index is finite because the selection law is a finite product. -/
def sampleWithReplacement [Fintype ι] [Finite κ] (ρ : Measure (κ → α)) : Measure (ι → α) :=
  samplePopulation (Measure.pi fun _ : ι => uniformOn (Set.univ : Set κ)) ρ

/-- Sampling with replacement is `samplePopulation` along independent uniform indices. -/
theorem sampleWithReplacement_def [Fintype ι] [Finite κ] (ρ : Measure (κ → α)) :
    sampleWithReplacement (ι := ι) ρ =
      samplePopulation (Measure.pi fun _ : ι => uniformOn (Set.univ : Set κ)) ρ :=
  (rfl)

/-- Sampling with replacement is `samplePopulation` along the uniform law on all index maps. -/
theorem sampleWithReplacement_eq_samplePopulation_uniformOn [Fintype ι] [Finite κ]
    (ρ : Measure (κ → α)) :
    sampleWithReplacement (ι := ι) ρ = samplePopulation (uniformOn (Set.univ : Set (ι → κ))) ρ := by
  rw [sampleWithReplacement_def, ← uniformOn_pi, Set.pi_univ]

/-- Sampling with replacement from a finite population law gives a finite law. -/
instance isFiniteMeasure_sampleWithReplacement [Fintype ι] [Finite κ] (ρ : Measure (κ → α))
    [IsFiniteMeasure ρ] : IsFiniteMeasure (sampleWithReplacement (ι := ι) ρ) := by
  rw [sampleWithReplacement_def]
  infer_instance

/-- Sampling with replacement from a random population preserves probability mass. -/
theorem isProbabilityMeasure_sampleWithReplacement [Fintype ι] [Finite κ] [Nonempty κ]
    (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (sampleWithReplacement (ι := ι) ρ) := by
  rw [sampleWithReplacement_def]
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

section Bounds

variable [Fintype ι] [Fintype κ]

/-- **Finite sampling bound, without replacement to with replacement.** For every measurable
event, sampling without replacement from a random finite population has mass at most its
with-replacement mass plus the collision bound `choose |ι| 2 / |κ|`. -/
theorem sampleWithoutReplacement_le_sampleWithReplacement_add
    {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ] {A : Set (ι → α)} (hA : MeasurableSet A) :
    sampleWithoutReplacement ρ A ≤ sampleWithReplacement ρ A +
      (Fintype.card ι).choose 2 / Fintype.card κ := by
  rw [sampleWithoutReplacement_def, sampleWithReplacement_eq_samplePopulation_uniformOn,
    samplePopulation_apply_population hA, samplePopulation_apply_population hA]
  let c : ℝ≥0∞ := (Fintype.card ι).choose 2 / Fintype.card κ
  let f : (κ → α) → ℝ≥0∞ := fun x =>
    uniformOn (Set.univ : Set (ι → κ)) ((fun k i => x (k i)) ⁻¹' A)
  have hf : Measurable f := by
    exact measurable_measure_prodMk_right (measurable_reindexPopulation hA)
  calc
    (∫⁻ x, uniformOn {k : ι → κ | Function.Injective k}
        ((fun k i => x (k i)) ⁻¹' A) ∂ρ) ≤ ∫⁻ x, f x + c ∂ρ :=
      lintegral_mono fun x => uniformOn_injective_le_add_choose_two_div _
    _ = (∫⁻ x, f x ∂ρ) + ∫⁻ _x, c ∂ρ := lintegral_add_left hf _
    _ = (∫⁻ x, f x ∂ρ) + c := by simp

/-- **Finite sampling bound, with replacement to without replacement.** For every measurable
event, sampling with replacement from a random finite population has mass at most its
without-replacement mass plus the collision bound `choose |ι| 2 / |κ|`. -/
theorem sampleWithReplacement_le_sampleWithoutReplacement_add
    {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ] {A : Set (ι → α)} (hA : MeasurableSet A) :
    sampleWithReplacement ρ A ≤ sampleWithoutReplacement ρ A +
      (Fintype.card ι).choose 2 / Fintype.card κ := by
  rw [sampleWithoutReplacement_def, sampleWithReplacement_eq_samplePopulation_uniformOn,
    samplePopulation_apply_population hA, samplePopulation_apply_population hA]
  let c : ℝ≥0∞ := (Fintype.card ι).choose 2 / Fintype.card κ
  let f : (κ → α) → ℝ≥0∞ := fun x =>
    uniformOn {k : ι → κ | Function.Injective k} ((fun k i => x (k i)) ⁻¹' A)
  have hf : Measurable f := by
    exact measurable_measure_prodMk_right (measurable_reindexPopulation hA)
  calc
    (∫⁻ x, uniformOn (Set.univ : Set (ι → κ))
        ((fun k i => x (k i)) ⁻¹' A) ∂ρ) ≤ ∫⁻ x, f x + c ∂ρ :=
      lintegral_mono fun x => uniformOn_univ_le_injective_add_choose_two_div _
    _ = (∫⁻ x, f x ∂ρ) + ∫⁻ _x, c ∂ρ := lintegral_add_left hf _
    _ = (∫⁻ x, f x ∂ρ) + c := by simp

end Bounds

end Sampling

end Probability

end TauCeti
