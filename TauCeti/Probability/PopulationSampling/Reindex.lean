/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Permutation
public import TauCeti.Probability.PopulationSampling.Finite

/-!
# Permutation representation and invariance of finite population sampling

Sampling a finite population without replacement can be realized by uniformly permuting the
population indices, and sampling with replacement depends only on the multiset of population
entries rather than their ordering:

* **Permutation representation:** reading a fixed finite population along an embedding composed
  with a uniformly random permutation has law `sampleWithoutReplacement`; in particular,
  uniformly permuting a deterministic population gives its full-population without-replacement
  law.
* **Reordering invariance:** uniformly reordering a random finite population via
  `sampleWithoutReplacement (ι := κ)` is absorbed on the left by `sampleWithReplacement` without
  nonemptiness assumptions.

## Main declarations

* `map_readPopulation_comp_uniformOn_perm`, `map_readPopulation_uniformOn_perm`: reading a fixed
  population along a uniform permutation as `sampleWithoutReplacement`.
* `sampleWithReplacement_sampleWithoutReplacement_self`: uniformly reordering a random finite
  population preserves subsequent sampling with replacement.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α]

/-- Reading a finite population along a fixed embedding composed with a uniform random
permutation gives the law of sampling that population without replacement. -/
theorem map_readPopulation_comp_uniformOn_perm {ι κ : Type*} [Finite κ]
    [MeasurableSpace (Equiv.Perm κ)] [MeasurableSingletonClass (Equiv.Perm κ)]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (x : κ → α) (e : ι ↪ κ) :
    (uniformOn (Set.univ : Set (Equiv.Perm κ))).map (fun σ i => x (σ (e i))) =
      sampleWithoutReplacement (ι := ι) (Measure.dirac x) := by
  have : Finite ι := Finite.of_injective e e.injective
  rw [sampleWithoutReplacement_dirac, ← e.map_uniformOn_perm,
    Measure.map_map (measurable_readPopulation x) (measurable_of_countable _)]
  rfl

/-- Uniformly permuting the indices of a deterministic finite population gives its
full-population without-replacement law. -/
theorem map_readPopulation_uniformOn_perm {κ : Type*} [Finite κ]
    [MeasurableSpace (Equiv.Perm κ)] [MeasurableSingletonClass (Equiv.Perm κ)]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] (x : κ → α) :
    (uniformOn (Set.univ : Set (Equiv.Perm κ))).map (fun σ i => x (σ i)) =
      sampleWithoutReplacement (ι := κ) (Measure.dirac x) := by
  simpa only [Function.Embedding.refl_apply] using
    map_readPopulation_comp_uniformOn_perm x (Function.Embedding.refl κ)

/-- Uniformly reordering a random finite population before sampling with replacement leaves the
sampled law unchanged. -/
@[simp]
theorem sampleWithReplacement_sampleWithoutReplacement_self {ι κ : Type*}
    [Fintype ι] [Finite κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (ρ : Measure (κ → α)) [SFinite ρ] :
    sampleWithReplacement (ι := ι) (sampleWithoutReplacement (ι := κ) ρ) =
      sampleWithReplacement (ι := ι) ρ := by
  let E : Set (κ → κ) := {l | Function.Injective l}
  let _ : IsProbabilityMeasure (uniformOn E) :=
    isProbabilityMeasure_uniformOn (Set.toFinite E) ⟨id, Function.injective_id⟩
  rw [sampleWithReplacement_eq_samplePopulation_uniformOn,
    sampleWithReplacement_eq_samplePopulation_uniformOn,
    sampleWithoutReplacement_def, samplePopulation_assoc]
  congr 1
  have hae : ∀ᵐ l ∂uniformOn E, Function.Injective l := by
    rw [ae_iff, uniformOn_eq_zero_iff (Set.toFinite E)]
    ext
    simp [E]
  have hmap : (fun l : κ → κ => (uniformOn (Set.univ : Set (ι → κ))).map (fun k i => l (k i)))
      =ᵐ[uniformOn E] fun _ => uniformOn (Set.univ : Set (ι → κ)) := by
    filter_upwards [hae] with l hl
    let e : κ ≃ κ := Equiv.ofBijective l (Finite.injective_iff_bijective.mp hl)
    convert (Equiv.arrowCongr (Equiv.refl ι) e).map_uniformOn_univ using 2
    ext k i
    simp [e]
  rw [samplePopulation_eq_bind_population, Measure.bind_congr_right hmap, Measure.bind_const]
  simp

end TauCeti.Probability
