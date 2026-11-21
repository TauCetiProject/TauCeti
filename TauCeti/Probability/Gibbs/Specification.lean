/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.SymbolicDynamics.Subshift
public import TauCeti.MeasureTheory.Group.ErgodicExtreme
public import Mathlib.Probability.Kernel.Proper
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Specifications and Gibbs measures on a subshift

Let `X` be a subshift of configurations `I → S` (`TauCeti.Subshift`). A *specification* on `X`
(`TauCeti.Specification X`) is a family of Markov kernels `γ_Λ`, indexed by the finite sets
`Λ ⊆ I`, where `γ_Λ (· | ω)` is the law of a configuration resampled inside `Λ` given the
configuration `ω` outside `Λ`. Formally:

* `γ_Λ` is a kernel from `X` with the exterior σ-algebra `𝓕_{Λᶜ}` (`TauCeti.Subshift.exterior`)
  to `X` with the trace of the product σ-algebra, so `ω ↦ γ_Λ (C | ω)` depends only on the
  coordinates of `ω` outside `Λ`;
* each `γ_Λ` is proper (Mathlib's `ProbabilityTheory.Kernel.IsProper`):
  `γ_Λ (C ∩ B | ω) = 1_B(ω) γ_Λ (C | ω)` for exterior events `B`, so `γ_Λ (· | ω)` keeps the
  configuration outside `Λ`;
* the family is consistent: `γ_Λ ∘ₖ γ_Δ = γ_Δ` for `Λ ⊆ Δ`, that is, resampling `Δ` and then
  `Λ` is resampling `Δ`.

A measure `μ` is Gibbs for `γ` (`TauCeti.Specification.IsGibbs`) when `μ.bind γ_Λ = μ` for every
finite `Λ`. These are the DLR equations of statistical mechanics: for probability measures,
`μ` is Gibbs iff each `γ_Λ (C | ·)` is a version of the conditional probability of `C` given the
configuration outside `Λ` (`TauCeti.Specification.isGibbs_iff_ae_eq_condExp`). By consistency it
suffices to check the equations on a cofinal family of finite sets
(`TauCeti.Specification.isGibbs_of_forall_exists_subset`).

The Gibbs probability measures form a convex set (`TauCeti.Specification.convex_gibbsMeasures`),
as do the invariant ones (`TauCeti.Specification.gibbsInvariant`, a subset of Tau Ceti's convex
set `TauCeti.MeasureTheory.invariantMeasuresOfMeasureUnivEq` of invariant probability measures).
For an equivariant specification the action of `Γ` preserves the Gibbs measures
(`TauCeti.Specification.IsGibbs.map_smul`).
Reweighting a Gibbs measure by a density measurable for every exterior σ-algebra, such as a
tail-measurable density, gives a Gibbs measure (`TauCeti.Specification.IsGibbs.withDensity`);
this is the step of the face property of invariant Gibbs measures that involves the
specification.

The definition follows Georgii, *Gibbs measures and phase transitions* (2nd ed., 2011),
Chapter 1, and Sheffield, *Random surfaces* (Astérisque 304, 2005), Section 1.1.2.
Its shape, with kernels `Kernel[cylinderEvents Λᶜ]` and the consistency equation
`(γ Λ).comap id _ ∘ₖ γ Δ = γ Δ`, is that of the specifications of the GibbsMeasure project of
Yaël Dillies and Matteo Cipollina (`github.com/YaelDillies/gibbs-measure`, file
`GibbsMeasure/Specification.lean`), which live on the full product space; here they live on a
subshift, and the Markov property and properness are fields of the structure.
-/

public section

open MeasureTheory ProbabilityTheory Set TauCeti.MeasureTheory
open scoped ENNReal Pointwise

namespace TauCeti

variable {Γ I S : Type*} [Group Γ] [MulAction Γ I] [TopologicalSpace S] [MeasurableSpace S]

/-- A specification on a subshift `X`: a family, indexed by the finite sets `Λ`, of Markov kernels
`γ_Λ` measurable for the exterior σ-algebra `𝓕_{Λᶜ}` on the source, each proper, and consistent:
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

variable {X : Subshift Γ I S}

@[ext]
theorem ext {γ γ' : Specification X} (h : ∀ Λ, γ.kernel Λ = γ'.kernel Λ) : γ = γ' := by
  obtain ⟨κ, _, _, _⟩ := γ
  obtain ⟨κ', _, _, _⟩ := γ'
  obtain rfl : κ = κ' := funext h
  rfl

variable (γ : Specification X)

instance (Λ : Finset I) : IsMarkovKernel (γ.kernel Λ) :=
  γ.isMarkovKernel Λ

/-- Each kernel of a specification is measurable for the full σ-algebra on its source. -/
theorem measurable_kernel (Λ : Finset I) : Measurable (γ.kernel Λ) :=
  (γ.kernel Λ).measurable.mono (X.exterior_le Λ) le_rfl

/-- The mass `γ_Λ (C | ω)` of a measurable set is a measurable function of `ω` for the full
σ-algebra. -/
theorem measurable_kernel_apply (Λ : Finset I) {C : Set X} (hC : MeasurableSet C) :
    Measurable fun ω => γ.kernel Λ ω C :=
  ((γ.kernel Λ).measurable_coe hC).mono (X.exterior_le Λ) le_rfl

/-- Properness of the kernels of a specification. -/
theorem kernel_apply_inter (Λ : Finset I) {C B : Set X} (hC : MeasurableSet C)
    (hB : MeasurableSet[X.exterior Λ] B) (ω : X) :
    γ.kernel Λ ω (C ∩ B) = B.indicator 1 ω * γ.kernel Λ ω C :=
  (γ.isProper Λ).inter_eq_indicator_mul (X.exterior_le Λ) hC hB ω

/-- The kernel `γ_Λ (· | ω)` gives an exterior event mass `1` if `ω` lies in it and `0`
otherwise. -/
theorem kernel_apply_of_measurableSet_exterior (Λ : Finset I) {B : Set X}
    (hB : MeasurableSet[X.exterior Λ] B) (ω : X) : γ.kernel Λ ω B = B.indicator 1 ω := by
  simpa using γ.kernel_apply_inter Λ MeasurableSet.univ hB ω

/-- Consistency of a specification, for measures: resampling `Δ` and then `Λ ⊆ Δ` is
resampling `Δ`. -/
theorem bind_bind_kernel_of_subset {Λ Δ : Finset I} (h : Λ ⊆ Δ) (μ : Measure X) :
    (μ.bind (γ.kernel Δ)).bind (γ.kernel Λ) = μ.bind (γ.kernel Δ) := by
  rw [Measure.bind_bind (γ.measurable_kernel Δ).aemeasurable
    (γ.measurable_kernel Λ).aemeasurable]
  congr 1
  funext ω
  have := DFunLike.congr_fun (γ.comp_eq h) ω
  rwa [Kernel.comp_apply, Kernel.coe_comap, Function.comp_id] at this

/-- A measure `μ` is Gibbs for a specification `γ` when `μ.bind γ_Λ = μ` for every finite `Λ`:
resampling any finite set according to `γ` leaves `μ` unchanged. -/
def IsGibbs (μ : Measure X) : Prop :=
  ∀ Λ : Finset I, μ.bind (γ.kernel Λ) = μ

variable {γ} {μ ν : Measure X}

theorem isGibbs_iff : γ.IsGibbs μ ↔ ∀ Λ : Finset I, μ.bind (γ.kernel Λ) = μ :=
  Iff.rfl

theorem IsGibbs.bind_kernel (hμ : γ.IsGibbs μ) (Λ : Finset I) : μ.bind (γ.kernel Λ) = μ :=
  hμ Λ

/-- A measure is Gibbs iff it is invariant (Mathlib's `ProbabilityTheory.Kernel.Invariant`) under
every kernel `γ_Λ`, read as a kernel for the full σ-algebra on its source. -/
theorem isGibbs_iff_invariant :
    γ.IsGibbs μ ↔
      ∀ Λ : Finset I, ((γ.kernel Λ).comap id (measurable_id'' (X.exterior_le Λ))).Invariant μ := by
  simp only [isGibbs_iff, Kernel.Invariant, Kernel.coe_comap, Function.comp_id]

/-- By consistency, a measure is Gibbs as soon as the equations `μ.bind γ_Δ = μ` hold for a
cofinal family of finite sets `Δ`. -/
theorem isGibbs_of_forall_exists_subset
    (h : ∀ Λ : Finset I, ∃ Δ, Λ ⊆ Δ ∧ μ.bind (γ.kernel Δ) = μ) : γ.IsGibbs μ := by
  intro Λ
  obtain ⟨Δ, hΛΔ, hΔ⟩ := h Λ
  calc μ.bind (γ.kernel Λ) = (μ.bind (γ.kernel Δ)).bind (γ.kernel Λ) := by rw [hΔ]
    _ = μ := by rw [γ.bind_bind_kernel_of_subset hΛΔ, hΔ]

/-- **The DLR equations.** For a Gibbs measure `μ`, the integral of `γ_Λ (C | ·)` over an
exterior event `B` is `μ (C ∩ B)`. -/
theorem IsGibbs.setLIntegral_kernel (hμ : γ.IsGibbs μ) (Λ : Finset I) {C B : Set X}
    (hC : MeasurableSet C) (hB : MeasurableSet[X.exterior Λ] B) :
    ∫⁻ ω in B, γ.kernel Λ ω C ∂μ = μ (C ∩ B) := by
  rw [(γ.isProper Λ).setLIntegral_eq_comp (X.exterior_le Λ) hC hB, hμ Λ]

/-- For a Gibbs measure `μ`, the integral of `γ_Λ (C | ·)` is `μ C`. -/
theorem IsGibbs.lintegral_kernel (hμ : γ.IsGibbs μ) (Λ : Finset I) {C : Set X}
    (hC : MeasurableSet C) : ∫⁻ ω, γ.kernel Λ ω C ∂μ = μ C := by
  simpa using hμ.setLIntegral_kernel Λ hC (@MeasurableSet.univ _ (X.exterior Λ))

/-- **Gibbs measures are those whose conditional probabilities are given by the specification.**
A finite measure `μ` is Gibbs for `γ` iff for every finite `Λ` and every measurable `C`, the
function `γ_Λ (C | ·)` is a version of the conditional expectation of `1_C` given the exterior
σ-algebra `𝓕_{Λᶜ}`. -/
theorem isGibbs_iff_ae_eq_condExp [IsFiniteMeasure μ] :
    γ.IsGibbs μ ↔ ∀ (Λ : Finset I) (C : Set X), MeasurableSet C →
      (fun ω => (γ.kernel Λ ω).real C) =ᵐ[μ] μ[C.indicator 1 | X.exterior Λ] := by
  have hκ (Λ : Finset I) {C : Set X} (hC : MeasurableSet C) :
      Measurable[X.exterior Λ] fun ω => (γ.kernel Λ ω).real C :=
    ((γ.kernel Λ).measurable_coe hC).ennreal_toReal
  -- The function `γ_Λ (C | ·)` takes values in `[0, 1]`, so it is integrable and its integral is
  -- the real part of its lower integral.
  have hint (Λ : Finset I) {C : Set X} (hC : MeasurableSet C) :
      Integrable (fun ω => (γ.kernel Λ ω).real C) μ :=
    (integrable_const (1 : ℝ)).mono'
      (γ.measurable_kernel_apply Λ hC).ennreal_toReal.aestronglyMeasurable <|
        ae_of_all _ fun _ => by
          rw [Real.norm_of_nonneg measureReal_nonneg]
          exact measureReal_le_one
  have hreal (Λ : Finset I) {C : Set X} (hC : MeasurableSet C) (ν : Measure X) :
      ∫ ω, (γ.kernel Λ ω).real C ∂ν = (∫⁻ ω, γ.kernel Λ ω C ∂ν).toReal :=
    integral_toReal (γ.measurable_kernel_apply Λ hC).aemeasurable
      (ae_of_all _ fun _ => measure_lt_top _ _)
  refine ⟨fun hμ Λ C hC => ?_, fun h Λ => ?_⟩
  · refine ae_eq_condExp_of_forall_setIntegral_eq (X.exterior_le Λ)
      ((integrable_const (1 : ℝ)).indicator hC) (fun _ _ _ => (hint Λ hC).integrableOn)
      (fun B hB _ => ?_) (hκ Λ hC).aestronglyMeasurable
    rw [hreal Λ hC, hμ.setLIntegral_kernel Λ hC hB, setIntegral_indicator hC]
    simp [measureReal_def, inter_comm]
  · ext C hC
    rw [Measure.bind_apply hC (γ.measurable_kernel Λ).aemeasurable]
    refine (ENNReal.toReal_eq_toReal_iff' ?_ (measure_ne_top μ C)).1 ?_
    · exact ne_top_of_le_ne_top (measure_ne_top μ univ)
        ((lintegral_mono fun _ => prob_le_one).trans_eq lintegral_one)
    · calc (∫⁻ ω, γ.kernel Λ ω C ∂μ).toReal = ∫ ω, (γ.kernel Λ ω).real C ∂μ :=
          (hreal Λ hC μ).symm
        _ = ∫ ω, (μ[C.indicator 1 | X.exterior Λ]) ω ∂μ := integral_congr_ae (h Λ C hC)
        _ = ∫ ω, C.indicator 1 ω ∂μ := integral_condExp (X.exterior_le Λ)
        _ = (μ C).toReal := by simp [integral_indicator_one hC, measureReal_def]

/-- A sum of Gibbs measures is Gibbs. -/
theorem IsGibbs.add (hμ : γ.IsGibbs μ) (hν : γ.IsGibbs ν) : γ.IsGibbs (μ + ν) := by
  rw [isGibbs_iff_invariant] at hμ hν ⊢
  intro Λ
  rw [Kernel.Invariant, Measure.comp_add, hμ Λ, hν Λ]

/-- A multiple of a Gibbs measure is Gibbs. -/
theorem IsGibbs.smul (hμ : γ.IsGibbs μ) (c : ℝ≥0∞) : γ.IsGibbs (c • μ) := fun Λ => by
  rw [Measure.bind_smul _ _ (γ.measurable_kernel Λ).aemeasurable, hμ Λ]

/-- **Reweighting by a tail density.** If `μ` is Gibbs and `f` is measurable for the exterior
σ-algebra of every finite set, as a tail-measurable density is, then `f • μ` is Gibbs. -/
theorem IsGibbs.withDensity (hμ : γ.IsGibbs μ) {f : X → ℝ≥0∞}
    (hf : ∀ Λ : Finset I, Measurable[X.exterior Λ] f) : γ.IsGibbs (μ.withDensity f) := by
  intro Λ
  have hfm : Measurable f := (hf Λ).mono (X.exterior_le Λ) le_rfl
  ext C hC
  have hCf : Measurable fun ω => f ω * C.indicator 1 ω := hfm.mul (measurable_one.indicator hC)
  -- Properness pulls the exterior-measurable density inside each kernel.
  have hprop (ω : X) :
      f ω * γ.kernel Λ ω C = ∫⁻ ω', f ω' * C.indicator 1 ω' ∂(γ.kernel Λ ω) := by
    rw [(γ.isProper Λ).lintegral_mul (X.exterior_le Λ) (measurable_one.indicator hC) (hf Λ),
      lintegral_indicator_one hC]
  rw [Measure.bind_apply hC (γ.measurable_kernel Λ).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hfm (γ.measurable_kernel_apply Λ hC),
    withDensity_apply _ hC]
  simp only [Pi.mul_apply, hprop]
  rw [← Measure.lintegral_bind (γ.measurable_kernel Λ).aemeasurable hCf.aemeasurable, hμ Λ,
    ← lintegral_indicator hC]
  congr 1 with ω
  by_cases hω : ω ∈ C <;> simp [hω]

/-- The zero measure is Gibbs. -/
@[simp]
theorem isGibbs_zero : γ.IsGibbs 0 := fun _ => Measure.bind_zero_left _

variable (γ)

/-- The Gibbs measures `𝒢(γ)` of a specification: the probability measures that are Gibbs. -/
def gibbsMeasures : Set (Measure X) :=
  {μ | IsProbabilityMeasure μ ∧ γ.IsGibbs μ}

/-- The invariant Gibbs measures `𝒢_inv(γ)`: the invariant probability measures that are
Gibbs. -/
def gibbsInvariant : Set (Measure X) :=
  {μ | μ ∈ invariantMeasuresOfMeasureUnivEq Γ X 1 ∧ γ.IsGibbs μ}

variable {γ}

@[simp]
theorem mem_gibbsMeasures_iff : μ ∈ γ.gibbsMeasures ↔ IsProbabilityMeasure μ ∧ γ.IsGibbs μ :=
  Iff.rfl

@[simp]
theorem mem_gibbsInvariant_iff :
    μ ∈ γ.gibbsInvariant ↔ μ ∈ invariantMeasuresOfMeasureUnivEq Γ X 1 ∧ γ.IsGibbs μ :=
  Iff.rfl

/-- The invariant Gibbs measures are Gibbs measures. -/
theorem gibbsInvariant_subset_gibbsMeasures : γ.gibbsInvariant ⊆ γ.gibbsMeasures :=
  fun _ h => ⟨⟨(mem_invariantMeasuresOfMeasureUnivEq_iff.1 h.1).2⟩, h.2⟩

variable (γ)

/-- The Gibbs measures of a specification form a convex set. -/
theorem convex_gibbsMeasures : Convex ℝ≥0∞ γ.gibbsMeasures := by
  rintro μ ⟨hμ, hγμ⟩ ν ⟨hν, hγν⟩ a b - - hab
  refine ⟨⟨?_⟩, (hγμ.smul a).add (hγν.smul b)⟩
  simp [hab]

/-- The invariant Gibbs measures of a specification form a convex set. -/
theorem convex_gibbsInvariant : Convex ℝ≥0∞ γ.gibbsInvariant := by
  rintro μ ⟨hμ, hγμ⟩ ν ⟨hν, hγν⟩ a b ha hb hab
  exact ⟨convex_invariantMeasuresOfMeasureUnivEq hμ hν ha hb hab,
    (hγμ.smul a).add (hγν.smul b)⟩

/-- A specification is equivariant when moving the boundary condition by `g` moves the resampled
law: `γ_{g • Λ} (g • C | g • ω) = γ_Λ (C | ω)`, stated as the push-forward of `γ_Λ (· | ω)` by
`g` being `γ_{g • Λ} (· | g • ω)`. -/
def IsEquivariant [DecidableEq I] : Prop :=
  ∀ (g : Γ) (Λ : Finset I) (ω : X), (γ.kernel Λ ω).map (g • ·) = γ.kernel (g • Λ) (g • ω)

variable {γ}

theorem isEquivariant_iff [DecidableEq I] :
    γ.IsEquivariant ↔
      ∀ (g : Γ) (Λ : Finset I) (ω : X), (γ.kernel Λ ω).map (g • ·) = γ.kernel (g • Λ) (g • ω) :=
  Iff.rfl

/-- For an equivariant specification, the action of `Γ` preserves the Gibbs measures. -/
theorem IsGibbs.map_smul [DecidableEq I] (hγ : γ.IsEquivariant) (hμ : γ.IsGibbs μ) (g : Γ) :
    γ.IsGibbs (μ.map (g • ·)) := by
  intro Λ
  have hg : Measurable fun ω : X => g • ω := measurable_const_smul g
  have hk (ω : X) : γ.kernel Λ (g • ω) = (γ.kernel (g⁻¹ • Λ) ω).map (g • ·) := by
    rw [hγ g, smul_inv_smul g Λ]
  rw [Measure.bind_map hg.aemeasurable (γ.measurable_kernel Λ).aemeasurable, funext hk,
    ← Measure.map_bind (γ.measurable_kernel _).aemeasurable hg.aemeasurable, hμ]

/-- For an equivariant specification, the action of `Γ` preserves `𝒢(γ)`. -/
theorem map_smul_mem_gibbsMeasures [DecidableEq I] (hγ : γ.IsEquivariant)
    (hμ : μ ∈ γ.gibbsMeasures) (g : Γ) : μ.map (g • ·) ∈ γ.gibbsMeasures :=
  have := hμ.1
  ⟨inferInstance, hμ.2.map_smul hγ g⟩

end Specification

end TauCeti
