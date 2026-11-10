/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PopulationSampling.Finite

/-!
# Observing sampled populations

A measurable observation of population values commutes with sampling: observing every entry
before choosing indices has the same law as observing the sampled word afterwards. This holds
for an arbitrary selection law (`samplePopulation_map` in
`TauCeti.Probability.PopulationSampling.Basic`); this file specializes it to sampling with or
without replacement.

For deterministic populations, these identities allow a population that factors through another
one to be sampled by pushing forward the latter's sampling law. In particular, identifying two
indices with equal population values reduces comparisons of sampling laws to comparisons on the
index space, without requiring any separation properties of the value space.
-/

public section

open MeasureTheory

namespace TauCeti.Probability

variable {ι κ α β : Type*} [MeasurableSpace κ] [MeasurableSingletonClass κ]
  [MeasurableSpace α] [MeasurableSpace β]

/-- Observing population values commutes with sampling without replacement. -/
theorem sampleWithoutReplacement_map [Countable κ] (ρ : Measure (κ → α)) [SFinite ρ]
    {g : α → β} (hg : Measurable g) :
    sampleWithoutReplacement (ι := ι) (ρ.map (fun x i => g (x i))) =
      (sampleWithoutReplacement (ι := ι) ρ).map (fun y i => g (y i)) := by
  simp only [sampleWithoutReplacement_def, samplePopulation_map _ _ hg]

/-- Observing population values commutes with sampling with replacement. -/
theorem sampleWithReplacement_map [Fintype ι] [Countable κ]
    (ρ : Measure (κ → α)) [SFinite ρ] {g : α → β} (hg : Measurable g) :
    sampleWithReplacement (ι := ι) (ρ.map (fun x i => g (x i))) =
      (sampleWithReplacement (ι := ι) ρ).map (fun y i => g (y i)) := by
  simp only [sampleWithReplacement_def, samplePopulation_map _ _ hg]

/-- Sampling an observed deterministic population without replacement is the observation's
pushforward of the original sampling law. -/
theorem sampleWithoutReplacement_dirac_comp [Countable κ] (x : κ → α)
    {g : α → β} (hg : Measurable g) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (g ∘ x)) =
      (sampleWithoutReplacement (ι := ι) (Measure.dirac x)).map (fun y i => g (y i)) := by
  have hκ : Measurable (fun y : κ → α => fun i => g (y i)) := by fun_prop
  simpa only [Measure.map_dirac' hκ, Function.comp_def] using
    sampleWithoutReplacement_map (ι := ι) (Measure.dirac x) hg

/-- Sampling an observed deterministic population with replacement is the observation's
pushforward of the original sampling law. -/
theorem sampleWithReplacement_dirac_comp [Fintype ι] [Countable κ] (x : κ → α)
    {g : α → β} (hg : Measurable g) :
    sampleWithReplacement (ι := ι) (Measure.dirac (g ∘ x)) =
      (sampleWithReplacement (ι := ι) (Measure.dirac x)).map (fun y i => g (y i)) := by
  have hκ : Measurable (fun y : κ → α => fun i => g (y i)) := by fun_prop
  simpa only [Measure.map_dirac' hκ, Function.comp_def] using
    sampleWithReplacement_map (ι := ι) (Measure.dirac x) hg

end TauCeti.Probability
