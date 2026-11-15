/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Invariance
public import TauCeti.Probability.Kernel.Composition.Power

/-!
# Powers, marginals, and invariant measures of parallel kernels

Parallel composition evolves two coordinates independently. Its powers are the parallel
compositions of the coordinate powers, its coordinate marginals recover the coordinate kernels
when the opposite coordinate is Markov, and pushing a product measure through it gives the
product of the pushed-forward measures. Conversely, pushing an arbitrary joint measure through
`κ ∥ₖ η` pushes each coordinate marginal through its corresponding kernel when the other kernel
is Markov. Consequently, products of invariant measures are invariant, each marginal of an
invariant joint measure is invariant, and a product of nonzero finite measures is `(κ ∥ₖ η)`-
invariant if and only if both factors are invariant. These identities supply the transition,
marginal, and stationary laws of independent product chains without introducing a second
product-kernel construction.
-/

public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

/-- Independent coordinate evolution commutes with taking transition powers. -/
@[simp]
theorem parallelComp_pow (κ : Kernel α α) (η : Kernel β β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (n : ℕ) :
    (κ ∥ₖ η) ^ n = (κ ^ n) ∥ₖ (η ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, one_def] using (id_parallelComp_id (α := α) (β := β)).symm
  | succ n ih =>
    simpa only [Kernel.pow_add, pow_one, ih] using
      parallelComp_comp_parallelComp (κ := κ) (κ' := η) (η := κ ^ n) (η' := η ^ n)

/-- At any time, a product chain has the product of the two coordinate transition laws. -/
theorem parallelComp_pow_apply (κ : Kernel α α) (η : Kernel β β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (n : ℕ) (x : α × β) :
    ((κ ∥ₖ η) ^ n) x = ((κ ^ n) x.1).prod ((η ^ n) x.2) := by
  rw [parallelComp_pow, parallelComp_apply]

/-- Singleton transition masses of a product chain factor at each common time. -/
theorem parallelComp_pow_apply_singleton (κ : Kernel α α) (η : Kernel β β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (n : ℕ) (x y : α × β) :
    ((κ ∥ₖ η) ^ n) x {y} = (κ ^ n) x.1 {y.1} * (η ^ n) x.2 {y.2} := by
  rw [parallelComp_pow_apply, ← Set.singleton_prod_singleton, Measure.prod_prod]

/-- First marginal of a parallel composition when the second kernel is Markov. -/
@[simp]
theorem fst_parallelComp (κ : Kernel α γ) [IsSFiniteKernel κ]
    (η : Kernel β δ) [IsMarkovKernel η] :
    fst (κ ∥ₖ η) = prodMkRight β κ := by
  ext x : 1
  simp [fst_apply, parallelComp_apply]

/-- Second marginal of a parallel composition when the first kernel is Markov. -/
@[simp]
theorem snd_parallelComp (κ : Kernel α γ) [IsMarkovKernel κ]
    (η : Kernel β δ) [IsSFiniteKernel η] :
    snd (κ ∥ₖ η) = prodMkLeft α η := by
  ext x : 1
  simp [snd_apply, parallelComp_apply]

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

/-- Pushing independent coordinates through separate kernels preserves their product law. -/
theorem parallelComp_comp_prod (μ : Measure α) (ν : Measure β) [SFinite ν]
    (κ : Kernel α γ) (η : Kernel β δ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (κ ∥ₖ η) ∘ₘ (μ.prod ν) = (κ ∘ₘ μ).prod (η ∘ₘ ν) := by
  have key (x : α) : (κ ∥ₖ η) ∘ₘ ((dirac x).prod ν) = (κ x).prod (η ∘ₘ ν) := by
    have h : (κ ∥ₖ η) ∘ₘ ((dirac x).prod ν) = (κ ∘ₘ dirac x).prod (η ∘ₘ ν) := by
      rw [prod_comp_left, prod_comp_right, comp_assoc,
        Kernel.parallelComp_comp_parallelComp, Kernel.comp_id, Kernel.id_comp]
    simpa only [dirac_bind κ.measurable] using h
  have hprod : ∀ x : α, map (Prod.mk x) ν = (dirac x).prod ν := fun x => (dirac_prod x).symm
  rw [prod_eq_of_sfinite μ ν, prod_eq_of_sfinite (κ ∘ₘ μ) (η ∘ₘ ν),
    bind_bind (Measurable.map_prodMk_left (ν := ν)).aemeasurable (Kernel.aemeasurable _),
    bind_bind κ.aemeasurable (Measurable.map_prodMk_left (ν := η ∘ₘ ν)).aemeasurable]
  congr 1
  funext x
  rw [← prod_eq_of_sfinite (κ x) (η ∘ₘ ν), ← key x, hprod]

/-- Pushing any joint measure through `κ ∥ₖ η` advances its first marginal by `κ` when `η` is a
Markov kernel. No s-finiteness hypothesis on `ρ` is needed. -/
@[simp]
theorem fst_parallelComp_comp (ρ : Measure (α × β)) (κ : Kernel α γ) [IsSFiniteKernel κ]
    (η : Kernel β δ) [IsMarkovKernel η] :
    ((κ ∥ₖ η) ∘ₘ ρ).fst = κ ∘ₘ ρ.fst := by
  rw [fst, map_comp _ _ measurable_fst, ← Kernel.fst_eq, Kernel.fst_parallelComp,
    Kernel.prodMkRight, fst, ← deterministic_comp_eq_map measurable_fst, comp_assoc,
    Kernel.comp_deterministic_eq_comap]

/-- Pushing any joint measure through `κ ∥ₖ η` advances its second marginal by `η` when `κ` is a
Markov kernel. No s-finiteness hypothesis on `ρ` is needed. -/
@[simp]
theorem snd_parallelComp_comp (ρ : Measure (α × β)) (κ : Kernel α γ) [IsMarkovKernel κ]
    (η : Kernel β δ) [IsSFiniteKernel η] :
    ((κ ∥ₖ η) ∘ₘ ρ).snd = η ∘ₘ ρ.snd := by
  rw [snd, map_comp _ _ measurable_snd, ← Kernel.snd_eq, Kernel.snd_parallelComp,
    Kernel.prodMkLeft, snd, ← deterministic_comp_eq_map measurable_snd, comp_assoc,
    Kernel.comp_deterministic_eq_comap]

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

section SFinite

variable {κ : Kernel α α} {η : Kernel β β} [IsSFiniteKernel κ] [IsSFiniteKernel η]
  {μ : Measure α} {ν : Measure β}

/-- The product of invariant measures is invariant for independent coordinate evolution. -/
theorem Invariant.parallelComp (hκ : κ.Invariant μ) (hη : η.Invariant ν) :
    (κ ∥ₖ η).Invariant (μ.prod ν) := by
  by_cases hν : SFinite ν
  · rw [Invariant, Measure.parallelComp_comp_prod, hκ.def, hη.def]
  · rw [Invariant, Measure.prod_eq_zero_of_not_sfinite hν, Measure.bind_zero_left]

end SFinite

/-- The first marginal of a `(κ ∥ₖ η)`-invariant measure is `κ`-invariant when `η` is Markov. -/
theorem Invariant.fst_of_parallelComp {κ : Kernel α α} {η : Kernel β β}
    [IsSFiniteKernel κ] [IsMarkovKernel η] {ρ : Measure (α × β)}
    (hρ : (κ ∥ₖ η).Invariant ρ) :
    κ.Invariant ρ.fst := by
  rw [Invariant, ← Measure.fst_parallelComp_comp ρ κ η, hρ.def]

/-- The second marginal of a `(κ ∥ₖ η)`-invariant measure is `η`-invariant when `κ` is Markov. -/
theorem Invariant.snd_of_parallelComp {κ : Kernel α α} {η : Kernel β β}
    [IsMarkovKernel κ] [IsSFiniteKernel η] {ρ : Measure (α × β)}
    (hρ : (κ ∥ₖ η).Invariant ρ) :
    η.Invariant ρ.snd := by
  rw [Invariant, ← Measure.snd_parallelComp_comp ρ κ η, hρ.def]

section Markov

variable {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]

/-- A product of nonzero finite measures is `(κ ∥ₖ η)`-invariant if and only if each factor is
invariant for its coordinate kernel. Nonvanishing of both factors is essential since `0.prod ν = 0`
is always invariant. -/
theorem invariant_parallelComp_prod_iff_of_ne_zero {μ : Measure α} {ν : Measure β}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    (κ ∥ₖ η).Invariant (μ.prod ν) ↔ κ.Invariant μ ∧ η.Invariant ν := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ => h₁.parallelComp h₂⟩
  · have hfst := h.fst_of_parallelComp
    rw [Measure.fst, Measure.map_fst_prod] at hfst
    have hν0 : ν Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hν
    have hνtop : ν Set.univ ≠ ∞ := measure_ne_top ν Set.univ
    have hcancel : (ν Set.univ)⁻¹ • (ν Set.univ • μ) = μ := by
      rw [smul_smul, ENNReal.inv_mul_cancel hν0 hνtop, one_smul]
    rw [Invariant, ← hcancel, Measure.comp_smul, hfst.def]
  · have hsnd := h.snd_of_parallelComp
    rw [Measure.snd, Measure.map_snd_prod] at hsnd
    have hμ0 : μ Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hμ
    have hμtop : μ Set.univ ≠ ∞ := measure_ne_top μ Set.univ
    have hcancel : (μ Set.univ)⁻¹ • (μ Set.univ • ν) = ν := by
      rw [smul_smul, ENNReal.inv_mul_cancel hμ0 hμtop, one_smul]
    rw [Invariant, ← hcancel, Measure.comp_smul, hsnd.def]

/-- A product of probability measures is `(κ ∥ₖ η)`-invariant if and only if both factors are
invariant for their coordinate kernels. -/
@[simp]
theorem invariant_parallelComp_prod_iff (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (κ ∥ₖ η).Invariant (μ.prod ν) ↔ κ.Invariant μ ∧ η.Invariant ν :=
  invariant_parallelComp_prod_iff_of_ne_zero
    (IsProbabilityMeasure.ne_zero μ) (IsProbabilityMeasure.ne_zero ν)

/-- The parallel product of two Markov kernels admits an invariant probability measure if and only
if each coordinate kernel admits an invariant probability measure. -/
theorem exists_invariant_probability_parallelComp_iff (κ : Kernel α α) (η : Kernel β β)
    [IsMarkovKernel κ] [IsMarkovKernel η] :
    (∃ ρ : Measure (α × β), IsProbabilityMeasure ρ ∧ (κ ∥ₖ η).Invariant ρ) ↔
      (∃ π₁ : Measure α, IsProbabilityMeasure π₁ ∧ κ.Invariant π₁) ∧
        (∃ π₂ : Measure β, IsProbabilityMeasure π₂ ∧ η.Invariant π₂) := by
  refine ⟨fun ⟨ρ, hprob, hinv⟩ =>
    ⟨⟨ρ.fst, inferInstance, hinv.fst_of_parallelComp⟩,
      ⟨ρ.snd, inferInstance, hinv.snd_of_parallelComp⟩⟩, ?_⟩
  rintro ⟨⟨π₁, _, h₁⟩, ⟨π₂, _, h₂⟩⟩
  exact ⟨π₁.prod π₂, inferInstance, h₁.parallelComp h₂⟩

end Markov

end ProbabilityTheory.Kernel
