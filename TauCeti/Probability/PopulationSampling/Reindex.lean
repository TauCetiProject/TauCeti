/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Permutation
public import TauCeti.Probability.PopulationSampling.Finite

/-!
# Reindexing and permutation invariance of finite population sampling

Sampling a finite population with or without replacement depends only on the multiset of
population entries, not on how the population is indexed. This file records three forms of that
symmetry:

* **Bijection invariance:** reindexing a random or deterministic population along `e : κ ≃ κ'`
  leaves both `sampleWithoutReplacement` and `sampleWithReplacement` unchanged.
* **Permutation representation:** reading a fixed finite population along an embedding composed
  with a uniformly random permutation has law `sampleWithoutReplacement`; in particular,
  uniformly permuting a deterministic population gives its full-population without-replacement
  law.
* **Iterated sampling:** sampling without replacement in two stages along `ι ↪ κ ↪ ν` agrees
  with sampling once from `ν`, and uniformly reordering a random finite population via
  `sampleWithoutReplacement (ι := κ)` is absorbed on the left by both `sampleWithoutReplacement`
  and `sampleWithReplacement` without nonemptiness assumptions.

## Main declarations

* `sampleWithoutReplacement_map_equiv`, `sampleWithReplacement_map_equiv`: bijection invariance
  for random populations, with deterministic forms `sampleWithoutReplacement_dirac_comp_equiv`
  and `sampleWithReplacement_dirac_comp_equiv`.
* `map_readPopulation_comp_uniformOn_perm`, `map_readPopulation_uniformOn_perm`: reading a fixed
  population along a uniform permutation as `sampleWithoutReplacement`.
* `sampleWithoutReplacement_sampleWithoutReplacement`: two-stage without-replacement sampling
  collapses to a single without-replacement sample when embeddings exist.
* `sampleWithoutReplacement_sampleWithoutReplacement_self`,
  `sampleWithReplacement_sampleWithoutReplacement_self`: uniformly reordering a random finite
  population preserves subsequent sampling without or with replacement.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α]

/-- Reindexing a random population by a bijection leaves sampling without replacement
unchanged. -/
theorem sampleWithoutReplacement_map_equiv {ι κ κ' : Type*}
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [MeasurableSpace κ'] [MeasurableSingletonClass κ'] [Finite κ']
    (ρ : Measure (κ' → α)) [SFinite ρ] (e : κ ≃ κ') :
    sampleWithoutReplacement (ι := ι) (ρ.map fun x j => x (e j)) =
      sampleWithoutReplacement (ι := ι) ρ := by
  have : Finite κ := Finite.of_equiv κ' e.symm
  rw [sampleWithoutReplacement_def, sampleWithoutReplacement_def,
    samplePopulation_map_reindex]
  congr 1
  by_cases hex : ∃ k : ι → κ, Function.Injective k
  · obtain ⟨k₀, hk₀⟩ := hex
    have : Finite ι := Finite.of_injective k₀ hk₀
    have hbij : Set.BijOn (fun (k : ι → κ) i => e (k i))
        {k | Function.Injective k} {k' | Function.Injective k'} :=
      ⟨fun _ hk => e.injective.comp hk,
        fun _ _ _ _ h => funext fun i => e.injective (congrFun h i),
        fun k' hk' => ⟨fun i => e.symm (k' i), e.symm.injective.comp hk',
          funext fun i => e.apply_symm_apply (k' i)⟩⟩
    exact hbij.map_uniformOn
  · have h₁ : {k : ι → κ | Function.Injective k} = ∅ :=
      Set.eq_empty_of_forall_notMem fun k hk => hex ⟨k, hk⟩
    have h₂ : {k' : ι → κ' | Function.Injective k'} = ∅ :=
      Set.eq_empty_of_forall_notMem fun k' hk' =>
        hex ⟨fun i => e.symm (k' i), e.symm.injective.comp hk'⟩
    simp [h₁, h₂]

/-- Reindexing a deterministic population by a bijection leaves sampling without replacement
unchanged. -/
theorem sampleWithoutReplacement_dirac_comp_equiv {ι κ κ' : Type*}
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [MeasurableSpace κ'] [MeasurableSingletonClass κ'] [Finite κ']
    (x : κ' → α) (e : κ ≃ κ') :
    sampleWithoutReplacement (ι := ι) (Measure.dirac (x ∘ e)) =
      sampleWithoutReplacement (ι := ι) (Measure.dirac x) := by
  have hpop : Measurable (fun y : κ' → α => fun j : κ => y (e j)) := by fun_prop
  simpa only [Measure.map_dirac' hpop, Function.comp_def] using
    sampleWithoutReplacement_map_equiv (ι := ι) (Measure.dirac x) e

/-- Reindexing a random population by a bijection leaves sampling with replacement unchanged. -/
theorem sampleWithReplacement_map_equiv {ι κ κ' : Type*} [Fintype ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [MeasurableSpace κ'] [MeasurableSingletonClass κ'] [Finite κ']
    (ρ : Measure (κ' → α)) [SFinite ρ] (e : κ ≃ κ') :
    sampleWithReplacement (ι := ι) (ρ.map fun x j => x (e j)) =
      sampleWithReplacement (ι := ι) ρ := by
  have : Finite κ := Finite.of_equiv κ' e.symm
  rw [sampleWithReplacement_eq_samplePopulation_uniformOn,
    sampleWithReplacement_eq_samplePopulation_uniformOn, samplePopulation_map_reindex]
  congr 1
  convert (Equiv.arrowCongr (Equiv.refl ι) e).map_uniformOn_univ using 2
  ext k i
  simp

/-- Reindexing a deterministic population by a bijection leaves sampling with replacement
unchanged. -/
theorem sampleWithReplacement_dirac_comp_equiv {ι κ κ' : Type*} [Fintype ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [MeasurableSpace κ'] [MeasurableSingletonClass κ'] [Finite κ']
    (x : κ' → α) (e : κ ≃ κ') :
    sampleWithReplacement (ι := ι) (Measure.dirac (x ∘ e)) =
      sampleWithReplacement (ι := ι) (Measure.dirac x) := by
  have hpop : Measurable (fun y : κ' → α => fun j : κ => y (e j)) := by fun_prop
  simpa only [Measure.map_dirac' hpop, Function.comp_def] using
    sampleWithReplacement_map_equiv (ι := ι) (Measure.dirac x) e

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
      sampleWithoutReplacement (ι := κ) (Measure.dirac x) :=
  map_readPopulation_comp_uniformOn_perm x (Function.Embedding.refl κ)

/-- Sampling without replacement from a finite population in two stages collapses to a single
without-replacement sample whenever injective selections exist at each stage. -/
theorem sampleWithoutReplacement_sampleWithoutReplacement {ι κ ν : Type*} [Finite ν]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [MeasurableSpace ν] [MeasurableSingletonClass ν]
    (ρ : Measure (ν → α)) [SFinite ρ] (e₁ : ι ↪ κ) (e₂ : κ ↪ ν) :
    sampleWithoutReplacement (ι := ι) (sampleWithoutReplacement (ι := κ) ρ) =
      sampleWithoutReplacement (ι := ι) ρ := by
  have : Finite κ := Finite.of_injective e₂ e₂.injective
  have : Finite ι := Finite.of_injective e₁ e₁.injective
  let E₁ : Set (ι → κ) := {k | Function.Injective k}
  let E₂ : Set (κ → ν) := {l | Function.Injective l}
  let _ : IsProbabilityMeasure (uniformOn E₁) :=
    isProbabilityMeasure_uniformOn (Set.toFinite E₁) ⟨e₁, e₁.injective⟩
  let _ : IsProbabilityMeasure (uniformOn E₂) :=
    isProbabilityMeasure_uniformOn (Set.toFinite E₂) ⟨e₂, e₂.injective⟩
  rw [sampleWithoutReplacement_def, sampleWithoutReplacement_def, sampleWithoutReplacement_def,
    samplePopulation_assoc]
  congr 1
  let _ : MeasurableSpace (Equiv.Perm ν) := ⊤
  have : MeasurableSingletonClass (Equiv.Perm ν) := ⟨fun _ => trivial⟩
  have hae : ∀ᵐ k ∂uniformOn E₁, Function.Injective k := by
    simpa only [E₁, uniformOn, Set.mem_ofPred_eq] using
      ae_cond_mem (μ := Measure.count) (Set.toFinite E₁).measurableSet
  have hmap (k : ι → κ) (hk : Function.Injective k) :
      (uniformOn E₂).map (fun l i => l (k i)) = uniformOn {m : ι → ν | Function.Injective m} := by
    have hmeas : Measurable (fun l : κ → ν => fun i : ι => l (k i)) := by fun_prop
    dsimp only [E₂]
    rw [← e₂.map_uniformOn_perm, Measure.map_map hmeas (measurable_of_countable _)]
    exact ((⟨k, hk⟩ : ι ↪ κ).trans e₂).map_uniformOn_perm
  apply Measure.ext fun A hA => ?_
  rw [samplePopulation_apply hA]
  calc
    ∫⁻ k, uniformOn E₂ ((fun l i => l (k i)) ⁻¹' A) ∂uniformOn E₁ =
        ∫⁻ _k, uniformOn {m : ι → ν | Function.Injective m} A ∂uniformOn E₁ := by
      apply lintegral_congr_ae
      filter_upwards [hae] with k hk
      have hmeas : Measurable (fun l : κ → ν => fun i : ι => l (k i)) := by fun_prop
      rw [← Measure.map_apply hmeas hA, hmap k hk]
    _ = uniformOn {m : ι → ν | Function.Injective m} A := by simp

/-- Uniformly reordering a random finite population before sampling without replacement leaves
the sampled law unchanged. -/
@[simp]
theorem sampleWithoutReplacement_sampleWithoutReplacement_self {ι κ : Type*} [Finite κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (ρ : Measure (κ → α)) [SFinite ρ] :
    sampleWithoutReplacement (ι := ι) (sampleWithoutReplacement (ι := κ) ρ) =
      sampleWithoutReplacement (ι := ι) ρ := by
  by_cases hex : ∃ k : ι → κ, Function.Injective k
  · obtain ⟨k, hk⟩ := hex
    exact sampleWithoutReplacement_sampleWithoutReplacement ρ ⟨k, hk⟩ (.refl κ)
  · have hempty : {k : ι → κ | Function.Injective k} = ∅ :=
      Set.eq_empty_of_forall_notMem fun k hk => hex ⟨k, hk⟩
    simp [sampleWithoutReplacement_def, hempty]

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
  rcases isEmpty_or_nonempty (ι → κ) with hE | _
  · have huniv : (Set.univ : Set (ι → κ)) = ∅ := Set.univ_eq_empty_iff.mpr hE
    simp [huniv]
  · have hae : ∀ᵐ l ∂uniformOn E, Function.Injective l := by
      simpa only [E, uniformOn, Set.mem_ofPred_eq] using
        ae_cond_mem (μ := Measure.count) (Set.toFinite E).measurableSet
    apply Measure.ext fun A hA => ?_
    rw [samplePopulation_apply_population hA]
    calc
      ∫⁻ l, uniformOn (Set.univ : Set (ι → κ)) ((fun k i => l (k i)) ⁻¹' A) ∂uniformOn E =
          ∫⁻ _l, uniformOn (Set.univ : Set (ι → κ)) A ∂uniformOn E := by
        apply lintegral_congr_ae
        filter_upwards [hae] with l hl
        let e : κ ≃ κ := Equiv.ofBijective l (Finite.injective_iff_bijective.mp hl)
        have hmap : (uniformOn (Set.univ : Set (ι → κ))).map (fun k i => l (k i)) =
            uniformOn (Set.univ : Set (ι → κ)) := by
          convert (Equiv.arrowCongr (Equiv.refl ι) e).map_uniformOn_univ using 2
          ext k i
          simp [e]
        rw [← Measure.map_apply (measurable_readPopulation l) hA, hmap]
      _ = uniformOn (Set.univ : Set (ι → κ)) A := by simp

end TauCeti.Probability
