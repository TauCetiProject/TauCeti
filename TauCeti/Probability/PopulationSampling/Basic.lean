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

Its evaluation and mixture lemmas take the population index countable with measurable
singletons, which is what makes the reindexing map measurable for an arbitrary state space `α`.
Finite sampling with and without replacement are the cases where `σ` is uniform on all index maps,
respectively on the injective ones (`TauCeti.Probability.sampleWithReplacement`,
`TauCeti.Probability.sampleWithoutReplacement`).

## Main declarations

* `measurable_reindexPopulation` — measurability of the joint selection/population evaluation;
* `samplePopulation` — sample a random population along an independent random selection;
* `samplePopulation_map` — measurable observations commute with sampling;
* `samplePopulation_dirac_comp` — its deterministic-population composition form;
* `samplePopulation_assoc` — iterated population sampling composes selection laws via
  `samplePopulation`;
* `samplePopulation_apply`, `samplePopulation_apply_population` — its evaluation by
  conditioning on the selection or on the population;
* `samplePopulation_eq_bind`, `samplePopulation_eq_bind_population` — its form as a mixture,
  over the selection law or over the population law, of the samples with that input fixed;
* `samplePopulation_le_add_lintegral` — integrating deterministic-population eventwise bounds
  across a random population law.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- Reindexing a population by a simultaneously supplied selection of its indices is measurable.

The measurable-space hypothesis on the population index is discrete: it lets the variable index
be split into countably many measurable fibres. -/
theorem measurable_reindexPopulation {ι κ : Type*} [Countable κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] :
    Measurable (fun p : (ι → κ) × (κ → α) => fun i : ι => p.2 (p.1 i)) :=
  Measurable.of_eval fun i =>
    (measurable_from_prod_countable_left (f := fun q : (κ → α) × κ => q.1 q.2)
      measurable_pi_apply).comp (f := fun p : (ι → κ) × (κ → α) => (p.2, p.1 i)) (by fun_prop)

section SamplePopulation

variable {ι κ : Type*} [MeasurableSpace κ]

/-- Sampling a random population along an independent random selection of its indices.

First draw a population `x : κ → α` with law `ρ`; independently draw an index map `k : ι → κ` with
law `σ`; then return the sample `i ↦ x (k i)`. Sampling without replacement
(`sampleWithoutReplacement`) and with replacement (`sampleWithReplacement`) are the cases where
`σ` is uniform on the injective index maps, respectively on all of them.

The definition is the pushforward `Measure.map` of `σ.prod ρ` along `(k, x) ↦ x ∘ k`. Following
`Measure.map`, when that map is not almost everywhere measurable the result is an arbitrary Dirac
mass, or zero if `σ.prod ρ = 0`. When the population index is countable with measurable singletons
the map is measurable for an arbitrary `α` (`measurable_reindexPopulation`), and the evaluation
and mixture lemmas below assume this. -/
def samplePopulation (σ : Measure (ι → κ)) (ρ : Measure (κ → α)) : Measure (ι → α) :=
  (σ.prod ρ).map fun p i => p.2 (p.1 i)

/-- The defining pushforward form of `samplePopulation`. -/
theorem samplePopulation_def (σ : Measure (ι → κ)) (ρ : Measure (κ → α)) :
    samplePopulation σ ρ = (σ.prod ρ).map fun p i => p.2 (p.1 i) :=
  (rfl)

/-- Sampling along the zero selection measure gives the zero measure. -/
@[simp]
theorem samplePopulation_zero_left (ρ : Measure (κ → α)) :
    samplePopulation (0 : Measure (ι → κ)) ρ = 0 := by
  simp [samplePopulation_def]

/-- Sampling the zero population measure gives the zero measure. -/
@[simp]
theorem samplePopulation_zero_right (σ : Measure (ι → κ)) :
    samplePopulation σ (0 : Measure (κ → α)) = 0 := by
  simp [samplePopulation_def]

/-- Sampling an s-finite population law along an s-finite selection law gives an s-finite law. -/
instance sfinite_samplePopulation (σ : Measure (ι → κ)) (ρ : Measure (κ → α))
    [SFinite σ] [SFinite ρ] :
    SFinite (samplePopulation σ ρ) := by
  rw [samplePopulation_def]
  infer_instance

/-- Sampling a finite population law along a finite selection law gives a finite law. -/
instance isFiniteMeasure_samplePopulation (σ : Measure (ι → κ)) (ρ : Measure (κ → α))
    [IsFiniteMeasure σ] [IsFiniteMeasure ρ] :
    IsFiniteMeasure (samplePopulation σ ρ) := by
  rw [samplePopulation_def]
  infer_instance

/-- Sampling a probability population along a probability selection law is a probability law. -/
instance isProbabilityMeasure_samplePopulation (σ : Measure (ι → κ)) (ρ : Measure (κ → α))
    [IsProbabilityMeasure σ] [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (samplePopulation σ ρ) := by
  rw [samplePopulation_def]
  infer_instance

variable [Countable κ] [MeasurableSingletonClass κ]

/-- Reading a fixed population along a varying selection is measurable. -/
theorem measurable_readPopulation (x : κ → α) :
    Measurable (fun k : ι → κ => fun i => x (k i)) :=
  measurable_reindexPopulation.comp measurable_prodMk_right

/-- Sampling a deterministic population is the pushforward of the selection law by reading
that population at the selected indices. -/
@[simp]
theorem samplePopulation_dirac (σ : Measure (ι → κ)) [SFinite σ] (x : κ → α) :
    samplePopulation σ (Measure.dirac x) = σ.map (fun k i => x (k i)) := by
  rw [samplePopulation_def, Measure.prod_dirac,
    Measure.map_map measurable_reindexPopulation measurable_prodMk_right]
  rfl

/-- Evaluating a sampled deterministic population on a measurable event is the selection mass
of its preimage. -/
theorem samplePopulation_dirac_apply {σ : Measure (ι → κ)} [SFinite σ] {x : κ → α}
    {A : Set (ι → α)} (hA : MeasurableSet A) :
    samplePopulation σ (Measure.dirac x) A = σ ((fun k : ι → κ => fun i => x (k i)) ⁻¹' A) := by
  rw [samplePopulation_dirac, Measure.map_apply (measurable_readPopulation x) hA]

/-- A measurable observation commutes with sampling along any selection law. The population law
need only be s-finite; no finiteness or normalization is required of the selection law. -/
theorem samplePopulation_map {β : Type*} [MeasurableSpace β] (σ : Measure (ι → κ))
    (ρ : Measure (κ → α)) [SFinite ρ] {g : α → β} (hg : Measurable g) :
    samplePopulation σ (ρ.map (fun x i => g (x i))) =
      (samplePopulation σ ρ).map (fun y i => g (y i)) := by
  have hκ : Measurable (fun x : κ → α => fun i => g (x i)) := by fun_prop
  have hι : Measurable (fun y : ι → α => fun i => g (y i)) := by fun_prop
  have hprod := Measure.map_prod_map σ ρ measurable_id hκ
  rw [Measure.map_id] at hprod
  rw [samplePopulation_def, hprod,
    Measure.map_map measurable_reindexPopulation (measurable_id.prodMap hκ),
    samplePopulation_def, Measure.map_map hι measurable_reindexPopulation]
  rfl

/-- Sampling an observed deterministic population along any selection law is the observation's
pushforward of the original sampling law. -/
theorem samplePopulation_dirac_comp {β : Type*} [MeasurableSpace β]
    (σ : Measure (ι → κ)) (x : κ → α) {g : α → β} (hg : Measurable g) :
    samplePopulation σ (Measure.dirac (g ∘ x)) =
      (samplePopulation σ (Measure.dirac x)).map (fun y i => g (y i)) := by
  have hκ : Measurable (fun y : κ → α => fun i => g (y i)) := by fun_prop
  simpa only [Measure.map_dirac' hκ, Function.comp_def] using
    samplePopulation_map σ (Measure.dirac x) hg

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

/-- Iterated population sampling is associative: sampling along `σ` and then independently along
`τ` is sampling once along the composite selection law `samplePopulation τ σ`. -/
theorem samplePopulation_assoc {ν : Type*} [MeasurableSpace ν] [Countable ν]
    [MeasurableSingletonClass ν] (τ : Measure (ι → κ)) (σ : Measure (κ → ν)) [SFinite σ]
    (ρ : Measure (ν → α)) [SFinite ρ] :
    samplePopulation τ (samplePopulation σ ρ) =
      samplePopulation (samplePopulation τ σ) ρ := by
  apply Measure.ext fun A hA => ?_
  have hmeas : Measurable (fun m : ι → ν => ρ ((fun x : ν → α => fun i => x (m i)) ⁻¹' A)) :=
    measurable_measure_prodMk_left (measurable_reindexPopulation hA)
  rw [samplePopulation_apply hA, samplePopulation_apply hA, samplePopulation_def τ σ,
    lintegral_map hmeas measurable_reindexPopulation,
    lintegral_prod (fun p : (ι → κ) × (κ → ν) =>
      ρ ((fun x : ν → α => fun i => x (p.2 (p.1 i))) ⁻¹' A))
      (hmeas.comp measurable_reindexPopulation).aemeasurable]
  refine lintegral_congr fun k => ?_
  have hk : Measurable (fun y : κ → α => fun i : ι => y (k i)) := by fun_prop
  rw [samplePopulation_apply (hk hA)]
  rfl

/-- Sampling a random population is the mixture, over the selection law, of reading each fixed
selection off the random population. -/
theorem samplePopulation_eq_bind (σ : Measure (ι → κ)) (ρ : Measure (κ → α)) [SFinite ρ] :
    samplePopulation σ ρ = σ.bind fun k => ρ.map fun x i => x (k i) := by
  rw [samplePopulation_def, Measure.prod_eq_of_sfinite, Measure.map_bind
    Measurable.map_prodMk_left.aemeasurable measurable_reindexPopulation.aemeasurable]
  simp_rw [Measure.map_map measurable_reindexPopulation measurable_prodMk_left, Function.comp_def]

/-- Sampling a random population is the mixture, over the population law, of sampling each fixed
population along the selection law. -/
theorem samplePopulation_eq_bind_population (σ : Measure (ι → κ)) [SFinite σ]
    (ρ : Measure (κ → α)) [SFinite ρ] :
    samplePopulation σ ρ = ρ.bind fun x => σ.map fun k i => x (k i) := by
  have hswap := measurable_reindexPopulation.comp (measurable_swap (α := κ → α) (β := ι → κ))
  rw [samplePopulation_def, ← Measure.prod_swap, Measure.map_map measurable_reindexPopulation
    measurable_swap, Measure.prod_eq_of_sfinite, Measure.map_bind
    Measurable.map_prodMk_left.aemeasurable hswap.aemeasurable]
  simp_rw [Measure.map_map hswap measurable_prodMk_left, Function.comp_def, Prod.swap_prod_mk]

/-- Integrating a populationwise upper bound on a measurable event across an s-finite population
law. No measurability hypothesis is required on the error function `g`. -/
theorem samplePopulation_le_add_lintegral_of_measurableSet
    {σ₁ σ₂ : Measure (ι → κ)} [SFinite σ₁] [SFinite σ₂] {ρ : Measure (κ → α)} [SFinite ρ]
    {g : (κ → α) → ℝ≥0∞} {A : Set (ι → α)} (hA : MeasurableSet A)
    (h : ∀ᵐ x ∂ρ, samplePopulation σ₁ (Measure.dirac x) A ≤
      samplePopulation σ₂ (Measure.dirac x) A + g x) :
    samplePopulation σ₁ ρ A ≤ samplePopulation σ₂ ρ A + ∫⁻ x, g x ∂ρ := by
  rw [samplePopulation_apply_population hA, samplePopulation_apply_population hA]
  have hf : Measurable (fun x : κ → α => σ₂ ((fun k i => x (k i)) ⁻¹' A)) :=
    measurable_measure_prodMk_right (measurable_reindexPopulation hA)
  calc
    (∫⁻ x, σ₁ ((fun k i => x (k i)) ⁻¹' A) ∂ρ)
        ≤ ∫⁻ x, σ₂ ((fun k i => x (k i)) ⁻¹' A) + g x ∂ρ := by
          refine lintegral_mono_ae (h.mono fun x hx => ?_)
          rwa [samplePopulation_dirac_apply hA, samplePopulation_dirac_apply hA] at hx
    _ = (∫⁻ x, σ₂ ((fun k i => x (k i)) ⁻¹' A) ∂ρ) + ∫⁻ x, g x ∂ρ :=
          lintegral_add_left hf g

/-- Integrating populationwise upper bounds on measurable events across an s-finite population law
yields an upper bound on every subset `A` (measurable or not). -/
theorem samplePopulation_le_add_lintegral
    {σ₁ σ₂ : Measure (ι → κ)} [SFinite σ₁] [SFinite σ₂] {ρ : Measure (κ → α)} [SFinite ρ]
    {g : (κ → α) → ℝ≥0∞}
    (h : ∀ B, MeasurableSet B → ∀ᵐ x ∂ρ,
      samplePopulation σ₁ (Measure.dirac x) B ≤
        samplePopulation σ₂ (Measure.dirac x) B + g x)
    (A : Set (ι → α)) :
    samplePopulation σ₁ ρ A ≤ samplePopulation σ₂ ρ A + ∫⁻ x, g x ∂ρ := by
  calc
    samplePopulation σ₁ ρ A
        ≤ samplePopulation σ₁ ρ (toMeasurable (samplePopulation σ₂ ρ) A) :=
          measure_mono (subset_toMeasurable _ _)
    _ ≤ samplePopulation σ₂ ρ (toMeasurable (samplePopulation σ₂ ρ) A) + ∫⁻ x, g x ∂ρ :=
          samplePopulation_le_add_lintegral_of_measurableSet
            (measurableSet_toMeasurable _ _) (h _ (measurableSet_toMeasurable _ _))
    _ = samplePopulation σ₂ ρ A + ∫⁻ x, g x ∂ρ := by rw [measure_toMeasurable]

end SamplePopulation

end Probability

end TauCeti
