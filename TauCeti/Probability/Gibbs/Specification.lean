/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.Probability.Kernel.Proper
public import Mathlib.Probability.Notation
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import TauCeti.MeasureTheory.Group.ErgodicExtreme
public import TauCeti.Probability.Kernel.Invariance
public import TauCeti.Probability.Gibbs.Subshift

/-!
# Specifications and Gibbs measures on a subshift

Let `X` be a subshift of configurations `I → S` (`TauCeti.Subshift`). A *specification* on `X`
is a family `γ = (γ_Λ)`, indexed by the finite sets `Λ ⊆ I`, of Markov kernels
`γ_Λ : Kernel[𝓕_{Λᶜ}] X X`, measurable on the source for the exterior σ-algebra `𝓕_{Λᶜ}`, each
proper (`γ_Λ(C ∩ B | ω) = 1_B(ω) γ_Λ(C | ω)` for exterior events `B`) and consistent:
`γ_Λ ∘ₖ γ_Δ = γ_Δ` for `Λ ⊆ Δ`, with `γ_Λ` read as a kernel for the full σ-algebra on its source.
Mathlib's `∘ₖ` applies its right factor first, so this says that resampling `Δ` and then `Λ` is
resampling `Δ`. A measure `μ` is Gibbs for `γ` when `μ.bind γ_Λ = μ` for every finite `Λ`.

## Main definitions

* `TauCeti.Specification X`: specifications on a subshift `X`.
* `TauCeti.Specification.IsGibbs γ μ`: `μ` is Gibbs for `γ`.
* `TauCeti.Specification.IsEquivariant γ`: `γ` commutes with the action of `Γ`.
* `TauCeti.Specification.gibbsInvariant γ`: the `Γ`-invariant probability measures that are
  Gibbs for `γ`.

## Main results

* `TauCeti.Specification.isGibbs_iff_forall_ae_eq_condExp`: a finite measure is Gibbs if and only
  if each `γ_Λ(C | ·)` is a version of the conditional expectation of `1_C` given `𝓕_{Λᶜ}`.
* `TauCeti.Specification.convex_setOf_isGibbs`, `convex_setOf_isProbabilityMeasure_isGibbs`,
  `convex_gibbsInvariant`: the Gibbs measures form a convex cone, and the Gibbs probability
  measures and the invariant Gibbs probability measures form convex sets.
* `TauCeti.Specification.IsGibbs.map_smul`: for an equivariant specification, the Gibbs measures
  are mapped to Gibbs measures by the action.

## References

The definitions follow Sheffield, *Random surfaces*, Astérisque 304 (2005), Section 1.1.2. The
kernel formulation of a specification, with its consistency stated as a composition of kernels,
and the kernel-invariance form of the Gibbs property are those of the GibbsMeasure project of
Y. Dillies and M. Cipollina (https://github.com/YaelDillies/gibbs-measure,
`GibbsMeasure/Specification.lean`, Apache 2.0), adapted to subshifts.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {Γ I S : Type*} [Group Γ] [MulAction Γ I] [TopologicalSpace S] [MeasurableSpace S]

/-- A specification on a subshift: a family, indexed by the finite sets `Λ`, of Markov kernels
measurable for the exterior σ-algebra `𝓕_{Λᶜ}` on the source, each proper, and consistent:
`γ_Λ ∘ₖ γ_Δ = γ_Δ` for `Λ ⊆ Δ`, with `γ_Λ` read as a kernel for the full σ-algebra on its
source. -/
structure Specification (X : Subshift Γ I S) where
  /-- The kernel `γ_Λ` of a finite set `Λ`. -/
  kernel (Λ : Finset I) : Kernel[X.exterior Λ] X X
  /-- Each kernel is Markov. -/
  isMarkovKernel (Λ : Finset I) : IsMarkovKernel (kernel Λ)
  /-- Each kernel is proper: `γ_Λ (C ∩ B | ω) = 1_B(ω) γ_Λ (C | ω)` for exterior events `B`. -/
  isProper (Λ : Finset I) : (kernel Λ).IsProper
  /-- Consistency: resampling `Δ` and then `Λ ⊆ Δ` is resampling `Δ`. -/
  comp_eq ⦃Λ Δ : Finset I⦄ (h : Λ ⊆ Δ) :
    (kernel Λ).comap id (measurable_id'' (X.exterior_le Λ)) ∘ₖ kernel Δ = kernel Δ

namespace Specification

attribute [instance] isMarkovKernel

variable {X : Subshift Γ I S} (γ : Specification X) {μ ν : Measure X}

/-- Two specifications with the same kernels are equal. -/
@[ext]
theorem ext {γ γ' : Specification X} (h : ∀ Λ, γ.kernel Λ = γ'.kernel Λ) : γ = γ' := by
  obtain ⟨κ, _, _, _⟩ := γ
  obtain ⟨κ', _, _, _⟩ := γ'
  obtain rfl : κ = κ' := funext h
  rfl

/-- `ω ↦ γ_Λ(· | ω)` is measurable for the full σ-algebra on `X`. -/
theorem measurable_kernel (Λ : Finset I) : Measurable (γ.kernel Λ : X → Measure X) :=
  (γ.kernel Λ).measurable.mono (X.exterior_le Λ) le_rfl

/-- A measure is Gibbs for a specification when `μ.bind γ_Λ = μ` for every finite `Λ`. -/
def IsGibbs (μ : Measure X) : Prop :=
  ∀ Λ : Finset I, μ.bind (γ.kernel Λ) = μ

/-- Unfolding `Specification.IsGibbs`. -/
theorem isGibbs_iff : γ.IsGibbs μ ↔ ∀ Λ : Finset I, μ.bind (γ.kernel Λ) = μ :=
  Iff.rfl

/-- A measure is Gibbs if and only if it is invariant under each `γ_Λ`, read as a kernel for the
full σ-algebra on its source. -/
theorem isGibbs_iff_forall_invariant :
    γ.IsGibbs μ ↔
      ∀ Λ : Finset I, ((γ.kernel Λ).comap id (measurable_id'' (X.exterior_le Λ))).Invariant μ :=
  Iff.rfl

variable {γ} in
/-- Sums of Gibbs measures are Gibbs. -/
theorem IsGibbs.add (hμ : γ.IsGibbs μ) (hν : γ.IsGibbs ν) : γ.IsGibbs (μ + ν) :=
  γ.isGibbs_iff_forall_invariant.2 fun Λ =>
    (γ.isGibbs_iff_forall_invariant.1 hμ Λ).add (γ.isGibbs_iff_forall_invariant.1 hν Λ)

variable {γ} in
/-- Multiples of Gibbs measures are Gibbs. -/
theorem IsGibbs.smul (hμ : γ.IsGibbs μ) (c : ℝ≥0∞) : γ.IsGibbs (c • μ) :=
  γ.isGibbs_iff_forall_invariant.2 fun Λ => (γ.isGibbs_iff_forall_invariant.1 hμ Λ).smul c

/-- The Gibbs measures of a specification form a convex cone. -/
theorem convex_setOf_isGibbs : Convex ℝ≥0∞ {μ : Measure X | γ.IsGibbs μ} :=
  fun _ hμ _ hν a b _ _ _ => (hμ.smul a).add (hν.smul b)

/-- The Gibbs probability measures of a specification form a convex set. -/
theorem convex_setOf_isProbabilityMeasure_isGibbs :
    Convex ℝ≥0∞ {μ : Measure X | IsProbabilityMeasure μ ∧ γ.IsGibbs μ} := by
  rintro μ ⟨hμ₁, hμ⟩ ν ⟨hν₁, hν⟩ a b - - hab
  refine ⟨⟨?_⟩, γ.convex_setOf_isGibbs hμ hν zero_le zero_le hab⟩
  simp [hab]

/-- A finite measure is Gibbs for a specification if and only if, for every finite `Λ` and
measurable `C`, `ω ↦ γ_Λ(C | ω)` is a version of the conditional expectation of `1_C` given the
exterior σ-algebra `𝓕_{Λᶜ}`. -/
theorem isGibbs_iff_forall_ae_eq_condExp [IsFiniteMeasure μ] :
    γ.IsGibbs μ ↔ ∀ (Λ : Finset I) ⦃C : Set X⦄, MeasurableSet C →
      (fun ω => (γ.kernel Λ ω C).toReal) =ᵐ[μ] μ⟦C | X.exterior Λ⟧ := by
  have hm := X.exterior_le
  -- Integrals of `γ_Λ(C | ·)` are the real parts of the corresponding lower integrals.
  have hint : ∀ (Λ : Finset I) ⦃C : Set X⦄, MeasurableSet C → ∀ s,
      ∫ ω in s, (γ.kernel Λ ω C).toReal ∂μ = (∫⁻ ω in s, γ.kernel Λ ω C ∂μ).toReal :=
    fun Λ C hC s => integral_toReal
      (((γ.kernel Λ).measurable_coe hC).mono (hm Λ) le_rfl).aemeasurable
      (.of_forall fun ω => measure_lt_top _ _)
  constructor
  · intro hμ Λ C hC
    have hg : Measurable[X.exterior Λ] fun ω => (γ.kernel Λ ω C).toReal :=
      ((γ.kernel Λ).measurable_coe hC).ennreal_toReal
    have hgi : Integrable (fun ω => (γ.kernel Λ ω C).toReal) μ :=
      .of_bound (hg.mono (hm Λ) le_rfl).aestronglyMeasurable 1 <| .of_forall fun ω => by
        simpa using ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    refine ae_eq_condExp_of_forall_setIntegral_eq (hm Λ)
      ((integrable_const (1 : ℝ)).indicator hC) (fun s _ _ => hgi.integrableOn)
      (fun s hs _ => ?_) hg.stronglyMeasurable.aestronglyMeasurable
    -- By properness, the integral over an exterior `s` is `(μ.bind γ_Λ) (C ∩ s) = μ (C ∩ s)`.
    have hprop : ∫⁻ ω in s, γ.kernel Λ ω C ∂μ = μ (C ∩ s) := by
      rw [(γ.isProper Λ).setLIntegral_eq_comp (hm Λ) hC hs]
      exact congrArg (· (C ∩ s)) (hμ Λ)
    rw [hint Λ hC s, hprop, integral_indicator_const _ hC]
    simp [Measure.restrict_apply hC, Measure.real]
  · intro h Λ
    ext C hC
    have hfin : ∫⁻ ω, γ.kernel Λ ω C ∂μ ≠ ∞ :=
      ((lintegral_mono fun ω => prob_le_one).trans_lt (by simp)).ne
    -- Integrating the conditional expectation of `1_C` over the whole space gives `μ C`.
    have hcond : ∫ ω, (γ.kernel Λ ω C).toReal ∂μ = μ.real C := by
      rw [integral_congr_ae (h Λ hC), integral_condExp (hm Λ), integral_indicator_const _ hC]
      simp
    rw [Measure.bind_apply hC (γ.measurable_kernel Λ).aemeasurable,
      ← ENNReal.toReal_eq_toReal_iff' hfin (measure_ne_top μ C)]
    have hall := hint Λ hC univ
    rw [Measure.restrict_univ] at hall
    rw [← hall]
    exact hcond

section Equivariant

variable [DecidableEq I]

/-- A specification is equivariant when `γ_{gΛ}(gC | g • ω) = γ_Λ(C | ω)`: the push-forward of
`γ_Λ(· | ω)` by `g` is `γ_{gΛ}(· | g • ω)`, where `gΛ` is the image of `Λ` under `g`. -/
def IsEquivariant : Prop :=
  ∀ (g : Γ) (Λ : Finset I) (ω : X),
    (γ.kernel Λ ω).map (g • ·) = γ.kernel (g • Λ) (g • ω)

/-- Unfolding `Specification.IsEquivariant`. -/
theorem isEquivariant_iff :
    γ.IsEquivariant ↔ ∀ (g : Γ) (Λ : Finset I) (ω : X),
      (γ.kernel Λ ω).map (g • ·) = γ.kernel (g • Λ) (g • ω) :=
  Iff.rfl

/-- For an equivariant specification, the image of a Gibbs measure under the action of any
`g : Γ` is Gibbs. -/
theorem IsGibbs.map_smul {γ : Specification X} (hγ : γ.IsEquivariant) (hμ : γ.IsGibbs μ)
    (g : Γ) : γ.IsGibbs (μ.map (g • ·)) := fun Λ => by
  set Λ' := g⁻¹ • Λ
  have hΛ : g • Λ' = Λ := smul_inv_smul g Λ
  have hg : Measurable (g • · : X → X) := measurable_const_smul g
  have hκ : (fun ω => γ.kernel Λ (g • ω)) = fun ω => (γ.kernel Λ' ω).map (g • ·) :=
    funext fun ω => by rw [hγ g Λ' ω, hΛ]
  rw [Measure.bind_map hg.aemeasurable (γ.measurable_kernel Λ).aemeasurable, hκ,
    ← Measure.map_bind (γ.measurable_kernel Λ').aemeasurable hg.aemeasurable, hμ Λ']

end Equivariant

/-- The invariant Gibbs measures `𝒢_inv(γ)`: the `Γ`-invariant probability measures that are
Gibbs for `γ`. -/
def gibbsInvariant : Set (Measure X) :=
  {μ | μ ∈ TauCeti.MeasureTheory.invariantMeasuresOfMeasureUnivEq Γ X 1 ∧ γ.IsGibbs μ}

/-- Membership in the invariant Gibbs measures. -/
@[simp]
theorem mem_gibbsInvariant_iff :
    μ ∈ γ.gibbsInvariant ↔ SMulInvariantMeasure Γ X μ ∧ μ univ = 1 ∧ γ.IsGibbs μ := by
  simp [gibbsInvariant, and_assoc]

/-- The invariant Gibbs measures form a convex set. -/
theorem convex_gibbsInvariant : Convex ℝ≥0∞ γ.gibbsInvariant :=
  TauCeti.MeasureTheory.convex_invariantMeasuresOfMeasureUnivEq.inter γ.convex_setOf_isGibbs

end Specification

end TauCeti
