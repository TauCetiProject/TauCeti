/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Sampling a random population along a random selection

A *population* is a map `x : κ → α`, and a *selection* is an index map `k : ι → κ`; reading the
selected entries gives the sample `x ∘ k : ι → α`. This file builds the law of that sample when
the population and the selection are drawn independently: for a population law
`ρ : Measure (κ → α)` and a selection law `σ : Measure (ι → κ)`, `samplePopulation σ ρ` is the
pushforward of `σ.prod ρ` along `(k, x) ↦ x ∘ k`.

The population index is countable with measurable singletons, which is what makes the reindexing
map measurable for an arbitrary state space `α`. Finite sampling with and without replacement are
the cases where `σ` is uniform on all index maps, respectively on the injective ones
(`TauCeti.Probability.sampleWithReplacement`, `TauCeti.Probability.sampleWithoutReplacement`).

## Main declarations

* `measurable_reindexPopulation` — measurability of the joint selection/population evaluation;
* `samplePopulation` — sample a random population along an independent random selection;
* `samplePopulation_apply`, `samplePopulation_apply_population` — its evaluation by
  conditioning on the selection or on the population;
* `samplePopulation_eq_bind` — its form as a mixture, over the population law, of sampling each
  fixed population.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- Reindexing a population by a simultaneously supplied selection of its indices is measurable.

The measurable-space hypothesis on the population index is discrete: it lets the variable index
be split into countably many measurable fibres. -/
theorem measurable_reindexPopulation {ι κ : Type*} [Countable κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] :
    Measurable (fun p : (ι → κ) × (κ → α) => fun i : ι => p.2 (p.1 i)) := by
  refine Measurable.of_eval fun i => ?_
  intro s hs
  have hpreimage : (fun p : (ι → κ) × (κ → α) => p.2 (p.1 i)) ⁻¹' s =
      ⋃ j : κ, {p | p.1 i = j} ∩ {p | p.2 j ∈ s} := by
    ext p; simp
  rw [hpreimage]
  refine MeasurableSet.iUnion fun j => ?_
  have hselection : MeasurableSet
      ((fun p : (ι → κ) × (κ → α) => p.1 i) ⁻¹' {j}) :=
    ((measurable_pi_apply i).comp measurable_fst) (measurableSet_singleton j)
  have hpopulation : MeasurableSet
      ((fun p : (ι → κ) × (κ → α) => p.2 j) ⁻¹' s) :=
    ((measurable_pi_apply j).comp measurable_snd) hs
  simpa [Set.preimage] using hselection.inter hpopulation

section SamplePopulation

variable {ι κ : Type*} [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- Sampling a random population along an independent random selection of its indices.

First draw a population `x : κ → α` with law `ρ`; independently draw an index map `k : ι → κ` with
law `σ`; then return the sample `i ↦ x (k i)`. Sampling without replacement
(`sampleWithoutReplacement`) and with replacement (`sampleWithReplacement`) are the cases where
`σ` is uniform on the injective index maps, respectively on all of them.

The population index is countable with measurable singletons because that is what
`measurable_reindexPopulation` uses to make the reindexing map measurable for an arbitrary `α`;
the definition is the pushforward along that measurable map. -/
def samplePopulation (σ : Measure (ι → κ)) (ρ : Measure (κ → α)) : Measure (ι → α) :=
  let ν := σ.prod ρ
  let f := fun p : (ι → κ) × (κ → α) => fun i => p.2 (p.1 i)
  let hf : AEMeasurable f ν := measurable_reindexPopulation.aemeasurable
  Measure.mapₗ (hf.mk f) ν

/-- The defining pushforward form of `samplePopulation`. -/
theorem samplePopulation_def (σ : Measure (ι → κ)) (ρ : Measure (κ → α)) :
    samplePopulation σ ρ = (σ.prod ρ).map fun p i => p.2 (p.1 i) :=
  Measure.mapₗ_mk_apply_of_aemeasurable measurable_reindexPopulation.aemeasurable

/-- Sampling a probability population along a probability selection law is a probability law. -/
instance isProbabilityMeasure_samplePopulation (σ : Measure (ι → κ)) (ρ : Measure (κ → α))
    [IsProbabilityMeasure σ] [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (samplePopulation σ ρ) := by
  rw [samplePopulation_def]
  infer_instance

/-- Evaluating a sampled law by conditioning first on the selection: it averages the laws of the
selected entries of the population over the selection law. -/
theorem samplePopulation_apply {σ : Measure (ι → κ)} {ρ : Measure (κ → α)} [SFinite ρ]
    {A : Set (ι → α)} (hA : MeasurableSet A) :
    samplePopulation σ ρ A = ∫⁻ k, ρ ((fun x : κ → α => fun i => x (k i)) ⁻¹' A) ∂σ := by
  rw [samplePopulation_def, Measure.map_apply measurable_reindexPopulation hA,
    Measure.prod_apply (measurable_reindexPopulation hA)]
  -- The section of the joint preimage at `k` is, by definition, the reindexed preimage.
  rfl

/-- Evaluating a sampled law by conditioning first on the population: it averages, over the
population law, the selection probability of the event. -/
theorem samplePopulation_apply_population {σ : Measure (ι → κ)} [SFinite σ]
    {ρ : Measure (κ → α)} [SFinite ρ] {A : Set (ι → α)} (hA : MeasurableSet A) :
    samplePopulation σ ρ A = ∫⁻ x, σ ((fun k : ι → κ => fun i => x (k i)) ⁻¹' A) ∂ρ := by
  rw [samplePopulation_def, Measure.map_apply measurable_reindexPopulation hA,
    Measure.prod_apply_symm (measurable_reindexPopulation hA)]
  -- The section of the joint preimage at `x` is, by definition, the reindexed preimage.
  rfl

/-- Sampling a random population is the mixture, over the population law, of sampling each fixed
population along the selection law. -/
theorem samplePopulation_eq_bind (σ : Measure (ι → κ)) [SFinite σ] (ρ : Measure (κ → α))
    [SFinite ρ] :
    samplePopulation σ ρ = ρ.bind fun x => σ.map fun k i => x (k i) := by
  have hsample (x : κ → α) : Measurable fun k : ι → κ => fun i => x (k i) :=
    measurable_reindexPopulation.comp measurable_prodMk_right
  have hmix : Measurable fun x : κ → α => σ.map fun k : ι → κ => fun i => x (k i) := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    simp_rw [Measure.map_apply (hsample _) hA]
    exact measurable_measure_prodMk_right (measurable_reindexPopulation hA)
  ext A hA
  rw [samplePopulation_apply_population hA, Measure.bind_apply hA hmix.aemeasurable]
  exact lintegral_congr fun x => (Measure.map_apply (hsample x) hA).symm

end SamplePopulation

end Probability

end TauCeti
