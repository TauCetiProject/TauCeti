/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.RadonNikodym

import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# The conditional chain rule for relative entropy

Mathlib's chain rule `InformationTheory.klDiv_compProd_eq_add` writes the relative entropy of two
composition-products as
`klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`,
leaving the conditional term as the relative entropy of two measures on the product. This file
identifies that term with the average of the relative entropies of the kernels,
`klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ`, which gives the conditional chain rule
`klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + ∫⁻ a, klDiv (κ a) (η a) ∂μ`.

The obstruction is measurability of `a ↦ klDiv (κ a) (η a)`. When the target `β` is countably
generated (or the source `α` is countable), Mathlib's kernel Radon–Nikodym derivative
`ProbabilityTheory.Kernel.rnDeriv κ η` is jointly measurable and is a version of each
`∂(κ a)/∂(η a)`, and the set of `a` with `κ a ≪ η a` is measurable. Writing `klDiv` as the
integral of `klFun` of that derivative gives the measurability. The identification of the
conditional term holds for finite kernels, since the mass corrections built into `klDiv` are
carried along by `klFun`; the chain rule itself inherits the Markov-kernel hypothesis of
Mathlib's `InformationTheory.klDiv_compProd_eq_add`.

Disintegrating a finite measure on `α × Ω` with standard Borel `Ω` along its first marginal gives
the form used for laws of pairs: the relative entropy of `ρ` against `σ` is that of their first
marginals plus the averaged relative entropy of their conditional laws, and it equals the first
term exactly when the conditional laws agree almost everywhere. In entropic optimal transport this
is the step that reduces an entropy minimization over laws of paths, or of triples, to one over
their endpoint couplings.

Relative entropy also tensorizes: for finite `μ₁, ν₁` and probability measures `μ₂, ν₂`,
`klDiv (μ₁.prod μ₂) (ν₁.prod ν₂) = klDiv μ₁ ν₁ + μ₁ univ * klDiv μ₂ ν₂`. This needs no hypothesis
on the measurable spaces.

## Main statements

* `ProbabilityTheory.Kernel.measurable_klDiv`: `a ↦ klDiv (κ a) (η a)` is measurable for finite
  kernels into a countably generated space.
* `TauCeti.klDiv_compProd_right`: `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ`.
* `TauCeti.klDiv_compProd_eq_add_lintegral`: the conditional chain rule
  `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + ∫⁻ a, klDiv (κ a) (η a) ∂μ`.
* `TauCeti.klDiv_compProd_eq_klDiv_iff`: when `klDiv μ ν` is finite, the chain rule loses nothing
  exactly when `κ a = η a` for `μ`-almost every `a`.
* `TauCeti.klDiv_eq_klDiv_fst_add_lintegral_condKernel` and `TauCeti.klDiv_eq_klDiv_fst_iff`: the
  same two statements for finite measures on `α × Ω`, through their conditional kernels.
* `TauCeti.klDiv_prod_prod_eq_add` and `TauCeti.klDiv_prod_prod`: tensorization of relative
  entropy over products.

## Implementation notes

The computation of `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` follows Mathlib's proof of
`InformationTheory.klDiv_compProd_left`, with `ProbabilityTheory.rnDeriv_measure_compProd_right`
in place of its left-hand analogue.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006,
  Theorem 2.5.3, for the chain rule for relative entropy.
* C. Léonard, *A survey of the Schrödinger problem and some of its connections with optimal
  transport*, Discrete Contin. Dyn. Syst. 34 (2014), for the disintegration of relative entropy
  along the endpoint marginal, which reduces the dynamic Schrödinger problem to the static one.
-/

public section

open MeasureTheory InformationTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ η : Kernel α β}
  [MeasurableSpace.CountableOrCountablyGenerated α β] [IsFiniteKernel κ] [IsFiniteKernel η]

/-- Where `κ a ≪ η a`, the relative entropy of `κ a` against `η a` is the integral of `klFun` of
the jointly measurable kernel Radon–Nikodym derivative `κ.rnDeriv η`. -/
theorem klDiv_eq_lintegral_klFun_of_ac {a : α} (h : κ a ≪ η a) :
    klDiv (κ a) (η a) = ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂η a := by
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac h]
  refine lintegral_congr_ae ?_
  filter_upwards [rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb
  rw [hb]

variable (κ η) in
/-- The relative entropy `a ↦ klDiv (κ a) (η a)` of two finite kernels is measurable when the
target is countably generated or the source is countable. -/
@[fun_prop]
theorem measurable_klDiv : Measurable fun a ↦ klDiv (κ a) (η a) := by
  classical
  have h : (fun a ↦ klDiv (κ a) (η a)) = fun a ↦
      if κ a ≪ η a then ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂η a else ∞ := by
    ext a
    split_ifs with ha
    · exact klDiv_eq_lintegral_klFun_of_ac ha
    · exact klDiv_of_not_ac ha
  rw [h]
  refine Measurable.ite (measurableSet_absolutelyContinuous κ η) ?_ measurable_const
  exact Measurable.lintegral_kernel_prod_right
    (measurable_klFun.comp (measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal

end ProbabilityTheory.Kernel

namespace TauCeti

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}
  {κ η : Kernel α β}

section CompProd

variable [MeasurableSpace.CountableOrCountablyGenerated α β]

/-- The relative entropy of two composition-products with the same first marginal is the
average of the relative entropies of the two kernels. -/
theorem klDiv_compProd_right [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  by_cases h : ∀ᵐ a ∂μ, κ a ≪ η a
  · rw [klDiv_eq_lintegral_klFun_of_ac (Measure.absolutelyContinuous_compProd_right_iff.2 h)]
    calc ∫⁻ p, ENNReal.ofReal (klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal) ∂(μ ⊗ₘ η)
      _ = ∫⁻ p, ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal) ∂(μ ⊗ₘ η) := by
        refine lintegral_congr_ae ?_
        filter_upwards [rnDeriv_measure_compProd_right μ κ η] with p hp
        rw [hp]
      _ = ∫⁻ a, ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂η a ∂μ :=
        Measure.lintegral_compProd
          (measurable_klFun.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal
      _ = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [h] with a ha
        rw [Kernel.klDiv_eq_lintegral_klFun_of_ac ha]
  · -- Both sides are infinite: the kernels fail to be absolutely continuous on a set of
    -- positive `μ`-measure, where the integrand is `∞`.
    rw [klDiv_of_not_ac (mt Measure.absolutelyContinuous_compProd_right_iff.1 h), eq_comm]
    exact lintegral_eq_top_of_measure_eq_top_ne_zero (Kernel.measurable_klDiv κ η).aemeasurable
      fun h0 ↦ h (ae_iff.2 (measure_mono_null (fun a ha ↦ klDiv_of_not_ac ha) h0))

/-- **Chain rule** for relative entropy, with the conditional term written as the average of the
relative entropies of the two kernels:
`klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + ∫⁻ a, klDiv (κ a) (η a) ∂μ`. -/
theorem klDiv_compProd_eq_add_lintegral [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ]
    [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  rw [klDiv_compProd_eq_add, klDiv_compProd_right]

/-- When `klDiv μ ν` is finite, the relative entropy of `μ ⊗ₘ κ` against `ν ⊗ₘ η` reduces to
`klDiv μ ν` exactly when the kernels agree `μ`-almost everywhere. -/
theorem klDiv_compProd_eq_klDiv_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ]
    [IsMarkovKernel η] (h : klDiv μ ν ≠ ∞) :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν ↔ ∀ᵐ a ∂μ, κ a = η a := by
  rw [klDiv_compProd_eq_add_lintegral]
  nth_rw 2 [← add_zero (klDiv μ ν)]
  rw [ENNReal.add_right_inj h, lintegral_eq_zero_iff (Kernel.measurable_klDiv κ η)]
  simp only [Filter.EventuallyEq, Pi.zero_apply, klDiv_eq_zero_iff]

end CompProd

section CondKernel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [Nonempty Ω]
  {ρ σ : Measure (α × Ω)} [IsFiniteMeasure ρ] [IsFiniteMeasure σ]

/-- **Disintegration of relative entropy**: for finite measures on `α × Ω` with `Ω` standard
Borel, the relative entropy is that of the first marginals plus the averaged relative entropy of
the conditional laws. -/
theorem klDiv_eq_klDiv_fst_add_lintegral_condKernel :
    klDiv ρ σ = klDiv ρ.fst σ.fst + ∫⁻ a, klDiv (ρ.condKernel a) (σ.condKernel a) ∂ρ.fst := by
  conv_lhs => rw [← ρ.disintegrate ρ.condKernel, ← σ.disintegrate σ.condKernel]
  exact klDiv_compProd_eq_add_lintegral

/-- When the first marginals have finite relative entropy, the relative entropy of finite
measures on `α × Ω` equals that of their first marginals exactly when their conditional laws
agree almost everywhere. -/
theorem klDiv_eq_klDiv_fst_iff (h : klDiv ρ.fst σ.fst ≠ ∞) :
    klDiv ρ σ = klDiv ρ.fst σ.fst ↔ ∀ᵐ a ∂ρ.fst, ρ.condKernel a = σ.condKernel a := by
  have key := klDiv_compProd_eq_klDiv_iff (κ := ρ.condKernel) (η := σ.condKernel) h
  rwa [ρ.disintegrate ρ.condKernel, σ.disintegrate σ.condKernel] at key

end CondKernel

section Prod

variable {μ' ν' : Measure β}

/-- Taking the product with a common finite measure on the right scales relative entropy by the
mass of that measure. -/
@[simp]
theorem klDiv_prod_left [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ρ : Measure β)
    [IsFiniteMeasure ρ] : klDiv (μ.prod ρ) (ν.prod ρ) = ρ univ * klDiv μ ν := by
  rcases eq_zero_or_neZero ρ with rfl | hρ
  · simp
  -- Write `ρ` as a multiple of a probability measure, for which this is Mathlib's
  -- `klDiv_compProd_left` with a constant kernel.
  obtain ⟨c, ρ₁, _, rfl⟩ : ∃ (c : ℝ≥0) (ρ₁ : Measure β), IsProbabilityMeasure ρ₁ ∧ ρ = c • ρ₁ :=
    ⟨(ρ univ).toNNReal, (ρ univ)⁻¹ • ρ, inferInstance, by
      rw [← smul_assoc, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_toNNReal (measure_ne_top ρ univ),
        ENNReal.mul_inv_cancel (NeZero.ne (ρ univ)) (measure_ne_top ρ univ), one_smul]⟩
  rw [Measure.prod_smul_right, Measure.prod_smul_right, klDiv_smul_same, ← Measure.compProd_const,
    ← Measure.compProd_const, klDiv_compProd_left]
  simp

/-- Taking the product with a common finite measure on the left scales relative entropy by the
mass of that measure. -/
@[simp]
theorem klDiv_prod_right (ρ : Measure α) [IsFiniteMeasure ρ] [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] : klDiv (ρ.prod μ') (ρ.prod ν') = ρ univ * klDiv μ' ν' := by
  rw [← klDiv_prod_left (μ := μ') (ν := ν') ρ]
  -- Swapping the factors is a measurable involution, so data processing applies both ways.
  refine le_antisymm ?_ ?_
  · simpa [Measure.prod_swap] using klDiv_map_le (μ'.prod ρ) (ν'.prod ρ) measurable_swap
  · simpa [Measure.prod_swap] using klDiv_map_le (ρ.prod μ') (ρ.prod ν') measurable_swap

/-- **Tensorization** of relative entropy: for finite `μ, ν` and probability measures `μ', ν'`,
`klDiv (μ.prod μ') (ν.prod ν') = klDiv μ ν + μ univ * klDiv μ' ν'`. -/
theorem klDiv_prod_prod_eq_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsProbabilityMeasure μ']
    [IsProbabilityMeasure ν'] :
    klDiv (μ.prod μ') (ν.prod ν') = klDiv μ ν + μ univ * klDiv μ' ν' := by
  rw [← Measure.compProd_const, ← Measure.compProd_const, klDiv_compProd_eq_add,
    Measure.compProd_const, Measure.compProd_const, klDiv_prod_right]

/-- **Tensorization** of relative entropy for probability measures:
`klDiv (μ.prod μ') (ν.prod ν') = klDiv μ ν + klDiv μ' ν'`. -/
theorem klDiv_prod_prod [IsProbabilityMeasure μ] [IsFiniteMeasure ν] [IsProbabilityMeasure μ']
    [IsProbabilityMeasure ν'] : klDiv (μ.prod μ') (ν.prod ν') = klDiv μ ν + klDiv μ' ν' := by
  rw [klDiv_prod_prod_eq_add, measure_univ, one_mul]

end Prod

end TauCeti
