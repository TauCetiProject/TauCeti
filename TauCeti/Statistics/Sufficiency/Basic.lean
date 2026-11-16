/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Sufficient and minimal sufficient statistics

This file defines sufficient and minimal sufficient statistics for parametric families of measures
and develops the disintegration integration identities and conditional-expectation characterization
of sufficiency:

* `TauCeti.IsSufficientStatistic P T`: `T : X → S` is measurable and there exists a single Markov
  kernel `K : Kernel S X` disintegrating every joint law `(P θ).map (fun x ↦ (T x, x))` as
  `(P θ).map T ⊗ₘ K`.
* `TauCeti.IsMinimalSufficientStatistic P T`: `T` is sufficient and factors `P θ`-almost everywhere
  through every sufficient statistic `U : X → S'` via a measurable map `φ : S' → S`.
* Disintegration identities for any s-finite measure `μ` and s-finite kernel `K` with
  `μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K`: marginal reconstruction `K ∘ₘ μ.map T = μ`,
  Lebesgue and Bochner iterated integral identities (including the product form
  `∫ x, g (T x) * φ x ∂μ = ∫ x, g (T x) * ∫ y, φ y ∂K (T x) ∂μ`), conditional expectation
  identification `μ[φ | comap T _] =ᵐ[μ] fun x ↦ ∫ y, φ y ∂K (T x)`, and preservation under
  mixtures `P ∘ₘ Λ`.
* `TauCeti.isSufficientStatistic_iff_exists_condExp_ae_eq`: on a nonempty standard Borel space `X`,
  a measurable statistic `T` is sufficient for a family of probability laws `P` if and only if
  every bounded measurable `φ : X → ℝ` admits a single measurable `ψ : S → ℝ` with
  `(P θ)[φ | comap T _] =ᵐ[P θ] ψ ∘ T` for all `θ`.

## References

* J. Pfanzagl, *Parametric Statistical Theory*, de Gruyter (1994), Definitions 1.1.1 (p. 2) and
  1.4.1 (p. 12), Corollary 1.3.11 (p. 10).
* M. J. Schervish, *Theory of Statistics*, Springer (1995), Definitions 2.8 (p. 85) and 2.28
  (p. 92).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace TauCeti

variable {Θ X S S' F : Type*} [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace S']

/-! ### Sufficient statistics -/

/-- A statistic `T : X → S` is sufficient for a family of measures `P : Θ → Measure X` if `T` is
measurable and there exists a single Markov kernel `K : Kernel S X` disintegrating every joint
law `(P θ).map (fun x ↦ (T x, x))` as `(P θ).map T ⊗ₘ K`. -/
def IsSufficientStatistic (P : Θ → Measure X) (T : X → S) : Prop :=
  Measurable T ∧ ∃ K : Kernel S X, IsMarkovKernel K ∧
    ∀ θ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K

/-- Unfolding lemma for `IsSufficientStatistic`. -/
theorem isSufficientStatistic_def {P : Θ → Measure X} {T : X → S} :
    IsSufficientStatistic P T ↔
      Measurable T ∧ ∃ K : Kernel S X, IsMarkovKernel K ∧
        ∀ θ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K :=
  (Iff.rfl)

/-- A sufficient statistic is measurable. -/
@[fun_prop]
theorem IsSufficientStatistic.measurable {P : Θ → Measure X} {T : X → S}
    (h : IsSufficientStatistic P T) : Measurable T :=
  h.1

/-- A sufficient statistic admits a parameter-free Markov kernel disintegrating every joint law
of `(T, id)`. -/
theorem IsSufficientStatistic.exists_kernel {P : Θ → Measure X} {T : X → S}
    (h : IsSufficientStatistic P T) :
    ∃ K : Kernel S X, IsMarkovKernel K ∧
      ∀ θ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K :=
  h.2

/-- The identity statistic is sufficient for every family of s-finite measures. -/
theorem isSufficientStatistic_id (P : Θ → Measure X) [∀ θ, SFinite (P θ)] :
    IsSufficientStatistic P id := by
  refine ⟨measurable_id, Kernel.id, inferInstance, fun θ ↦ ?_⟩
  rw [Measure.map_id, Kernel.id, Measure.compProd_deterministic measurable_id]
  rfl

/-- Any constant statistic is sufficient for a constant nonempty family of probability measures. -/
theorem isSufficientStatistic_const [Nonempty Θ] {P : Θ → Measure X}
    [∀ θ, IsProbabilityMeasure (P θ)] (hconst : ∀ θ₁ θ₂, P θ₁ = P θ₂) (s₀ : S) :
    IsSufficientStatistic P (fun _ ↦ s₀) := by
  let θ₀ : Θ := Classical.arbitrary Θ
  have hpair : Measurable fun x : X ↦ (s₀, x) := measurable_const.prodMk measurable_id
  refine ⟨measurable_const, Kernel.const S (P θ₀), inferInstance, fun θ ↦ ?_⟩
  rw [hconst θ θ₀]
  ext A hA
  rw [Measure.map_apply hpair hA, Measure.compProd_apply hA]
  have hmap : (P θ₀).map (fun _ : X ↦ s₀) = Measure.dirac s₀ := by
    rw [Measure.map_const, measure_univ, one_smul]
  rw [hmap, lintegral_dirac' _ (Kernel.measurable_kernel_prodMk_left hA), Kernel.const_apply]

/-- Composing a sufficient statistic with a measurable equivalence preserves sufficiency. -/
theorem IsSufficientStatistic.comp_measurableEquiv {P : Θ → Measure X} [∀ θ, SFinite (P θ)]
    {T : X → S} (h : IsSufficientStatistic P T) (e : S ≃ᵐ S') :
    IsSufficientStatistic P (e ∘ T) := by
  obtain ⟨hT, K, hK, hdis⟩ := h
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  refine ⟨e.measurable.comp hT, K.comap e.symm e.symm.measurable, inferInstance, fun θ ↦ ?_⟩
  ext A hA
  have hA' : MeasurableSet (Prod.map e id ⁻¹' A) := (e.measurable.prodMap measurable_id) hA
  have hmap1 : (P θ).map (fun x ↦ ((e ∘ T) x, x)) =
      ((P θ).map (fun x ↦ (T x, x))).map (Prod.map e id) := by
    rw [Measure.map_map (e.measurable.prodMap measurable_id) hpair]
    rfl
  rw [hmap1, Measure.map_apply (e.measurable.prodMap measurable_id) hA, hdis θ,
    Measure.compProd_apply hA', Measure.compProd_apply hA, ← Measure.map_map e.measurable hT,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hA) e.measurable]
  refine lintegral_congr fun s ↦ ?_
  rw [Kernel.comap_apply, e.symm_apply_apply]
  rfl

/-- A measurable statistic agreeing almost everywhere under every `P θ` with a sufficient statistic
is itself sufficient. -/
theorem IsSufficientStatistic.of_ae_eq {P : Θ → Measure X} {T₁ T₂ : X → S}
    (h : IsSufficientStatistic P T₁) (hT₂ : Measurable T₂) (hae : ∀ θ, T₁ =ᵐ[P θ] T₂) :
    IsSufficientStatistic P T₂ := by
  obtain ⟨_, K, hK, hdis⟩ := h
  refine ⟨hT₂, K, hK, fun θ ↦ ?_⟩
  have hpair : (fun x ↦ (T₁ x, x)) =ᵐ[P θ] fun x ↦ (T₂ x, x) :=
    (hae θ).mono fun x hx ↦ congrArg (·, x) hx
  rw [← Measure.map_congr hpair, ← Measure.map_congr (hae θ)]
  exact hdis θ

/-! ### Minimal sufficient statistics -/

/-- A statistic `T : X → S` is minimal sufficient for `P : Θ → Measure X` if it is sufficient and
factors almost everywhere under every `P θ` through every sufficient statistic `U : X → S'` via a
measurable map `φ : S' → S`. -/
def IsMinimalSufficientStatistic.{u, v, w, r} {Θ : Type u} {X : Type v} {S : Type w}
    [MeasurableSpace X] [MeasurableSpace S] (P : Θ → Measure X) (T : X → S) : Prop :=
  IsSufficientStatistic P T ∧ ∀ (S' : Type r) [MeasurableSpace S'] (U : X → S'),
    IsSufficientStatistic P U → ∃ φ : S' → S, Measurable φ ∧ ∀ θ, T =ᵐ[P θ] φ ∘ U

/-- Unfolding lemma for `IsMinimalSufficientStatistic`. -/
theorem isMinimalSufficientStatistic_def.{u, v, w, r} {Θ : Type u} {X : Type v} {S : Type w}
    [MeasurableSpace X] [MeasurableSpace S] {P : Θ → Measure X} {T : X → S} :
    IsMinimalSufficientStatistic.{u, v, w, r} P T ↔
      IsSufficientStatistic P T ∧ ∀ (S' : Type r) [MeasurableSpace S'] (U : X → S'),
        IsSufficientStatistic P U → ∃ φ : S' → S, Measurable φ ∧ ∀ θ, T =ᵐ[P θ] φ ∘ U :=
  (Iff.rfl)

/-- A minimal sufficient statistic is sufficient. -/
theorem IsMinimalSufficientStatistic.isSufficientStatistic {P : Θ → Measure X} {T : X → S}
    (h : IsMinimalSufficientStatistic P T) : IsSufficientStatistic P T :=
  h.1

/-- A minimal sufficient statistic factors almost everywhere through any sufficient statistic via
a measurable map. -/
theorem IsMinimalSufficientStatistic.exists_ae_eq_comp.{u, v, w, r} {Θ : Type u} {X : Type v}
    {S : Type w} [MeasurableSpace X] [MeasurableSpace S] {P : Θ → Measure X} {T : X → S}
    (h : IsMinimalSufficientStatistic.{u, v, w, r} P T) {S' : Type r} [MeasurableSpace S']
    {U : X → S'} (hU : IsSufficientStatistic P U) :
    ∃ φ : S' → S, Measurable φ ∧ ∀ θ, T =ᵐ[P θ] φ ∘ U :=
  h.2 S' U hU

/-- Any constant statistic is minimal sufficient for a constant nonempty family of probability
measures. -/
theorem isMinimalSufficientStatistic_const [Nonempty Θ] {P : Θ → Measure X}
    [∀ θ, IsProbabilityMeasure (P θ)] (hconst : ∀ θ₁ θ₂, P θ₁ = P θ₂) (s₀ : S) :
    IsMinimalSufficientStatistic P (fun _ ↦ s₀) :=
  ⟨isSufficientStatistic_const hconst s₀, fun _ _ _ _ ↦
    ⟨fun _ ↦ s₀, measurable_const, fun _ ↦ Filter.EventuallyEq.rfl⟩⟩

/-- Composing a minimal sufficient statistic with a measurable equivalence preserves minimal
sufficiency. -/
theorem IsMinimalSufficientStatistic.comp_measurableEquiv.{u, v, w, w', r} {Θ : Type u}
    {X : Type v} {S : Type w} {S' : Type w'} [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace S'] {P : Θ → Measure X} [∀ θ, SFinite (P θ)] {T : X → S}
    (h : IsMinimalSufficientStatistic.{u, v, w, r} P T) (e : S ≃ᵐ S') :
    IsMinimalSufficientStatistic.{u, v, w', r} P (e ∘ T) := by
  refine ⟨h.isSufficientStatistic.comp_measurableEquiv e, fun U_ty _ U hU ↦ ?_⟩
  obtain ⟨φ, hφ, hfac⟩ := h.exists_ae_eq_comp hU
  exact ⟨e ∘ φ, e.measurable.comp hφ, fun θ ↦ (hfac θ).fun_comp e⟩

/-- A measurable statistic agreeing almost everywhere under every `P θ` with a minimal sufficient
statistic is itself minimal sufficient. -/
theorem IsMinimalSufficientStatistic.of_ae_eq.{u, v, w, r} {Θ : Type u} {X : Type v} {S : Type w}
    [MeasurableSpace X] [MeasurableSpace S] {P : Θ → Measure X} {T₁ T₂ : X → S}
    (h : IsMinimalSufficientStatistic.{u, v, w, r} P T₁) (hT₂ : Measurable T₂)
    (hae : ∀ θ, T₁ =ᵐ[P θ] T₂) :
    IsMinimalSufficientStatistic.{u, v, w, r} P T₂ := by
  refine ⟨h.isSufficientStatistic.of_ae_eq hT₂ hae, fun S' _ U hU ↦ ?_⟩
  obtain ⟨φ, hφ, hfac⟩ := h.exists_ae_eq_comp hU
  exact ⟨φ, hφ, fun θ ↦ (hae θ).symm.trans (hfac θ)⟩

/-! ### Disintegration and integration identities -/

section Disintegration

variable {μ : Measure X} [SFinite μ] {T : X → S} {K : Kernel S X} [IsSFiniteKernel K]

/-- Reconstructing `μ` from a disintegration `μ.map (T, id) = μ.map T ⊗ₘ K`: composing the kernel
with the marginal law `μ.map T` recovers `μ`. -/
theorem comp_map_eq_self_of_map_prodMk_eq_compProd (hT : Measurable T)
    (h : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K) :
    K ∘ₘ μ.map T = μ := by
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  rw [← Measure.snd_compProd, ← h, Measure.snd, Measure.map_map measurable_snd hpair]
  exact Measure.map_id

/-- Lebesgue integral disintegration identity for `μ.map (T, id) = μ.map T ⊗ₘ K`. -/
theorem lintegral_eq_lintegral_lintegral_of_map_prodMk_eq_compProd (hT : Measurable T)
    (h : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K) {f : S × X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (T x, x) ∂μ = ∫⁻ x, ∫⁻ y, f (T x, y) ∂K (T x) ∂μ := by
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  have hmeas : Measurable fun s ↦ ∫⁻ y, f (s, y) ∂K s :=
    Measurable.lintegral_kernel_prod_right' hf
  rw [← lintegral_map hf hpair, h, Measure.lintegral_compProd hf, lintegral_map hmeas hT]

section Bochner

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Bochner integral disintegration identity for `μ.map (T, id) = μ.map T ⊗ₘ K`. -/
theorem integral_eq_integral_integral_of_map_prodMk_eq_compProd (hT : Measurable T)
    (h : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K) {f : S × X → F}
    (hfm : AEStronglyMeasurable f (μ.map (fun x ↦ (T x, x))))
    (hf : Integrable (fun x ↦ f (T x, x)) μ) :
    ∫ x, f (T x, x) ∂μ = ∫ x, ∫ y, f (T x, y) ∂K (T x) ∂μ := by
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  have hf_map : Integrable f (μ.map (fun x ↦ (T x, x))) :=
    (integrable_map_measure hfm hpair.aemeasurable).mpr hf
  have hf_cp : Integrable f (μ.map T ⊗ₘ K) := h ▸ hf_map
  have hinner : AEStronglyMeasurable (fun s ↦ ∫ y, f (s, y) ∂K s) (μ.map T) := by
    have h1 := hf_cp.aestronglyMeasurable.integral_kernel_compProd
    simpa [Measure.compProd, Kernel.prodMkLeft_apply, Kernel.const_apply] using h1
  rw [← MeasureTheory.integral_map hpair.aemeasurable hfm, h, Measure.integral_compProd hf_cp,
    MeasureTheory.integral_map hT.aemeasurable hinner]

/-- Product-form Bochner integration identity under a disintegration `μ.map (T, id) = μ.map T ⊗ₘ K`,
with scalar multiplication `g (T x) • φ x`. -/
theorem integral_smul_eq_integral_smul_integral_of_map_prodMk_eq_compProd (hT : Measurable T)
    (h : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K) {g : S → ℝ} (hg : Measurable g)
    {φ : X → F} (hφ : StronglyMeasurable φ) (hint : Integrable (fun x ↦ g (T x) • φ x) μ) :
    ∫ x, g (T x) • φ x ∂μ = ∫ x, g (T x) • ∫ y, φ y ∂K (T x) ∂μ := by
  have hf : StronglyMeasurable fun p : S × X ↦ g p.1 • φ p.2 :=
    (hg.comp measurable_fst).stronglyMeasurable.smul (hφ.comp_measurable measurable_snd)
  simpa [integral_smul] using
    integral_eq_integral_integral_of_map_prodMk_eq_compProd hT h hf.aestronglyMeasurable hint

/-- Product-form Bochner integration identity for bounded measurable real functions under a
disintegration of a finite measure. -/
theorem integral_mul_eq_integral_mul_integral_of_map_prodMk_eq_compProd [IsFiniteMeasure μ]
    (hT : Measurable T) (h : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K)
    {g : S → ℝ} (hg : Measurable g) (hgb : ∃ C, ∀ s, |g s| ≤ C)
    {φ : X → ℝ} (hφ : Measurable φ) (hφb : ∃ C, ∀ x, |φ x| ≤ C) :
    ∫ x, g (T x) * φ x ∂μ = ∫ x, g (T x) * ∫ y, φ y ∂K (T x) ∂μ := by
  obtain ⟨Cg, hCg⟩ := hgb
  obtain ⟨Cφ, hCφ⟩ := hφb
  have hint : Integrable (fun x ↦ g (T x) * φ x) μ := by
    refine Integrable.of_bound ((hg.comp hT).mul hφ).aestronglyMeasurable (Cg * Cφ)
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hCg (T x)) (hCφ x) (abs_nonneg _) ((abs_nonneg _).trans (hCg (T x)))
  simpa [smul_eq_mul] using
    integral_smul_eq_integral_smul_integral_of_map_prodMk_eq_compProd hT h hg
      hφ.stronglyMeasurable hint

/-- Conditional expectation given `σ(T)` equals integration against a disintegrating kernel `K`. -/
theorem condExp_ae_eq_integral_of_map_prodMk_eq_compProd [CompleteSpace F]
    (hT : Measurable T) [SigmaFinite (μ.trim hT.comap_le)]
    (h : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K)
    {φ : X → F} (hφ : Integrable φ μ) :
    μ[φ | MeasurableSpace.comap T inferInstance] =ᵐ[μ] fun x ↦ ∫ y, φ y ∂K (T x) := by
  let φ' : X → F := hφ.aestronglyMeasurable.mk φ
  have hφ'm : StronglyMeasurable φ' := hφ.aestronglyMeasurable.stronglyMeasurable_mk
  have hφ'ae : φ =ᵐ[μ] φ' := hφ.aestronglyMeasurable.ae_eq_mk
  have hcomp : K ∘ₘ μ.map T = μ := comp_map_eq_self_of_map_prodMk_eq_compProd hT h
  have hinner_ae : (fun x ↦ ∫ y, φ' y ∂K (T x)) =ᵐ[μ] fun x ↦ ∫ y, φ y ∂K (T x) := by
    have hae_s : ∀ᵐ s ∂μ.map T, φ =ᵐ[K s] φ' :=
      Measure.ae_ae_of_ae_comp (p := fun y ↦ φ y = φ' y) (hcomp.symm ▸ hφ'ae)
    exact (ae_of_ae_map hT.aemeasurable hae_s).mono fun _ hs ↦
      integral_congr_ae (Filter.EventuallyEq.symm hs)
  have hgm : StronglyMeasurable[MeasurableSpace.comap T inferInstance]
      (fun x ↦ ∫ y, φ' y ∂K (T x)) :=
    hφ'm.integral_kernel.comp_measurable (Measurable.of_comap_le le_rfl)
  have hφ'int : Integrable φ' μ := hφ.congr hφ'ae
  have hg_int : Integrable (fun x ↦ ∫ y, φ' y ∂K (T x)) μ := by
    have hφ'cp : Integrable (fun p : S × X ↦ φ' p.2) (μ.map T ⊗ₘ K) := by
      rw [Measure.integrable_compProd_snd_iff (hcomp.symm ▸ hφ'int.aestronglyMeasurable)]
      rwa [hcomp]
    have hint_s : Integrable (fun s ↦ ∫ y, φ' y ∂K s) (μ.map T) := by
      simpa [Measure.compProd, Kernel.prodMkLeft_apply, Kernel.const_apply] using
        hφ'cp.integral_compProd
    exact (integrable_map_measure hφ'm.integral_kernel.aestronglyMeasurable hT.aemeasurable).mp
      hint_s
  refine (ae_eq_condExp_of_forall_setIntegral_eq hT.comap_le hφ
    (fun _ _ _ ↦ hg_int.integrableOn) (fun A hA _ ↦ ?_)
    hgm.aestronglyMeasurable).symm.trans hinner_ae
  rcases hA with ⟨B, hB, rfl⟩
  have hBφ : Integrable (fun x ↦ B.indicator (fun _ ↦ (1 : ℝ)) (T x) • φ' x) μ := by
    have h1 : (fun x ↦ B.indicator (fun _ ↦ (1 : ℝ)) (T x) • φ' x) =
        (T ⁻¹' B).indicator φ' := by
      ext x
      by_cases hx : T x ∈ B <;> simp [hx]
    rw [h1]
    exact hφ'int.indicator (hT hB)
  have hset1 : ∫ x in T ⁻¹' B, ∫ y, φ' y ∂K (T x) ∂μ =
      ∫ x, B.indicator (fun _ ↦ (1 : ℝ)) (T x) • ∫ y, φ' y ∂K (T x) ∂μ := by
    rw [← integral_indicator (hT hB)]
    congr 1 with x
    by_cases hx : T x ∈ B <;> simp [hx]
  have hset2 : ∫ x in T ⁻¹' B, φ' x ∂μ =
      ∫ x, B.indicator (fun _ ↦ (1 : ℝ)) (T x) • φ' x ∂μ := by
    rw [← integral_indicator (hT hB)]
    congr 1 with x
    by_cases hx : T x ∈ B <;> simp [hx]
  rw [hset1,
    ← integral_smul_eq_integral_smul_integral_of_map_prodMk_eq_compProd hT h
      (measurable_const.indicator hB) hφ'm hBφ,
    ← hset2]
  exact setIntegral_congr_ae (hT hB) (hφ'ae.symm.mono fun _ hx _ ↦ hx)

end Bochner

/-- Disintegration is preserved under mixtures `P ∘ₘ Λ`: if `K` disintegrates `(P θ).map (T, id)`
for `Λ`-almost every `θ`, then `K` disintegrates `(P ∘ₘ Λ).map (T, id)`. -/
theorem map_prodMk_comp_eq_compProd [MeasurableSpace Θ] {P : Kernel Θ X} [IsSFiniteKernel P]
    {Λ : Measure Θ} [SFinite Λ] (hT : Measurable T)
    (h : ∀ᵐ θ ∂Λ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K) :
    (P ∘ₘ Λ).map (fun x ↦ (T x, x)) = (P ∘ₘ Λ).map T ⊗ₘ K := by
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  ext A hA
  rw [Measure.map_comp Λ P hpair, Measure.bind_apply hA (Kernel.aemeasurable _),
    Measure.compProd_apply hA, Measure.map_comp Λ P hT,
    Measure.lintegral_bind (Kernel.aemeasurable _)
      (Kernel.measurable_kernel_prodMk_left hA).aemeasurable]
  refine lintegral_congr_ae (h.mono fun θ hθ ↦ ?_)
  dsimp only
  rw [Kernel.map_apply _ hpair, Kernel.map_apply _ hT, hθ, Measure.compProd_apply hA]

end Disintegration

/-! ### Conditional-expectation characterization of sufficiency -/

/-- If `T` is sufficient for a family of finite measures `P`, then every strongly measurable
function `φ : X → F` integrable under each `P θ` admits a single strongly measurable function
`ψ : S → F` whose composition `ψ ∘ T` equals `(P θ)[φ | σ(T)]` almost everywhere for every `θ`. -/
theorem IsSufficientStatistic.exists_condExp_ae_eq [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {P : Θ → Measure X} [∀ θ, IsFiniteMeasure (P θ)] {T : X → S}
    (h : IsSufficientStatistic P T) {φ : X → F} (hφ : StronglyMeasurable φ)
    (hint : ∀ θ, Integrable φ (P θ)) :
    ∃ ψ : S → F, StronglyMeasurable ψ ∧
      ∀ θ, (P θ)[φ | MeasurableSpace.comap T inferInstance] =ᵐ[P θ] ψ ∘ T := by
  obtain ⟨hT, K, hK, hdis⟩ := h
  exact ⟨fun s ↦ ∫ y, φ y ∂K s, hφ.integral_kernel, fun θ ↦
    condExp_ae_eq_integral_of_map_prodMk_eq_compProd hT (hdis θ) (hint θ)⟩

/-- On a nonempty standard Borel space `X`, if every bounded measurable `φ : X → ℝ` has a
parameter-free measurable version `ψ ∘ T` of the conditional expectation `(P θ)[φ | σ(T)]`,
then `T` is sufficient for the family of probability laws `P`. -/
theorem isSufficientStatistic_of_exists_condExp_ae_eq [StandardBorelSpace X] [Nonempty X]
    {P : Θ → Measure X} [∀ θ, IsProbabilityMeasure (P θ)] {T : X → S} (hT : Measurable T)
    (hce : ∀ φ : X → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
      ∃ ψ : S → ℝ, Measurable ψ ∧
        ∀ θ, (P θ)[φ | MeasurableSpace.comap T inferInstance] =ᵐ[P θ] ψ ∘ T) :
    IsSufficientStatistic P T := by
  let e : X → ℝ := embeddingReal X
  have he : MeasurableEmbedding e := measurableEmbedding_embeddingReal X
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  have hchoice : ∀ q : ℚ, ∃ ψ : S → ℝ, Measurable ψ ∧
      ∀ θ, (P θ)[(e ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) |
        MeasurableSpace.comap T inferInstance] =ᵐ[P θ] ψ ∘ T := by
    intro q
    refine hce _ (measurable_const.indicator (he.measurable measurableSet_Iic)) ⟨1, fun x ↦ ?_⟩
    by_cases hx : x ∈ e ⁻¹' Iic (q : ℝ) <;> simp [hx]
  choose ψ hψm hψce using hchoice
  let f : Unit × S → ℚ → ℝ := fun p q ↦ ψ q p.2
  have hfm : Measurable f := measurable_pi_iff.mpr fun q ↦ (hψm q).comp measurable_snd
  let F : Unit × S → StieltjesFunction ℝ := stieltjesOfMeasurableRat f hfm
  let η : Kernel (Unit × S) ℝ :=
    { toFun := fun p ↦ (F p).measure
      measurable' := StieltjesFunction.measurable_measure (measurable_stieltjesOfMeasurableRat hfm)
        (tendsto_stieltjesOfMeasurableRat_atBot hfm)
        (tendsto_stieltjesOfMeasurableRat_atTop hfm) }
  have hη : IsMarkovKernel η :=
    ⟨fun p ↦ (F p).isProbabilityMeasure (tendsto_stieltjesOfMeasurableRat_atBot hfm p)
      (tendsto_stieltjesOfMeasurableRat_atTop hfm p)⟩
  let Kunit : Kernel (Unit × S) X := Kernel.borelMarkovFromReal X η
  let K : Kernel S X := Kunit.comap (fun s ↦ ((), s)) (measurable_const.prodMk measurable_id)
  refine ⟨hT, K, inferInstance, fun θ ↦ ?_⟩
  let κ : Kernel Unit (S × X) := Kernel.const Unit ((P θ).map (fun x ↦ (T x, x)))
  let ρ : Measure (S × ℝ) := (P θ).map (fun x ↦ (T x, e x))
  have hρfst : ρ.fst = (P θ).map T := by
    rw [Measure.fst, Measure.map_map measurable_fst (hT.prodMk he.measurable)]
    rfl
  have hκ' : Kernel.map κ (Prod.map (id : S → S) e) = Kernel.const Unit ρ := by
    ext u A _
    rw [Kernel.map_apply _ (measurable_id.prodMap he.measurable), Kernel.const_apply,
      Kernel.const_apply, Measure.map_map (measurable_id.prodMap he.measurable) hpair]
    rfl
  have hsetInt : ∀ (q : ℚ) {A : Set S}, MeasurableSet A →
      ∫ s in A, ψ q s ∂ρ.fst = ρ.real (A ×ˢ Iic (q : ℝ)) := by
    intro q A hA
    have hφint : Integrable ((e ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ))) (P θ) := by
      refine Integrable.of_bound
        (measurable_const.indicator (he.measurable measurableSet_Iic)).aestronglyMeasurable 1
        (ae_of_all _ fun x ↦ ?_)
      by_cases hx : x ∈ e ⁻¹' Iic (q : ℝ) <;> simp [hx]
    have hψ_ae : (fun x ↦ ψ q (T x)) =ᵐ[P θ]
        (P θ)[(e ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) |
          MeasurableSpace.comap T inferInstance] := (hψce q θ).symm
    calc ∫ s in A, ψ q s ∂ρ.fst
      _ = ∫ s in A, ψ q s ∂(P θ).map T := by rw [hρfst]
      _ = ∫ x in T ⁻¹' A, ψ q (T x) ∂P θ :=
          setIntegral_map hA (hψm q).aestronglyMeasurable hT.aemeasurable
      _ = ∫ x in T ⁻¹' A,
            (P θ)[(e ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) |
              MeasurableSpace.comap T inferInstance] x ∂P θ :=
          setIntegral_congr_ae (hT hA) (hψ_ae.mono fun _ hx _ ↦ hx)
      _ = ∫ x in T ⁻¹' A, (e ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) x ∂P θ :=
          setIntegral_condExp hT.comap_le hφint ⟨A, hA, rfl⟩
      _ = (P θ).real (T ⁻¹' A ∩ e ⁻¹' Iic (q : ℝ)) := by
          rw [setIntegral_indicator (he.measurable measurableSet_Iic), setIntegral_const,
            smul_eq_mul, mul_one]
      _ = ρ.real (A ×ˢ Iic (q : ℝ)) := by
          rw [Measure.real, Measure.real,
            Measure.map_apply (hT.prodMk he.measurable) (hA.prod measurableSet_Iic)]
          rfl
  have hint : ∀ q : ℚ, Integrable (ψ q) ρ.fst := by
    intro q
    rw [hρfst, integrable_map_measure (hψm q).aestronglyMeasurable hT.aemeasurable]
    exact integrable_condExp.congr (hψce q θ)
  have hpre : IsRatCondKernelCDF (fun p r ↦ (preCDF ρ r p.2).toReal)
      (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) :=
    isRatCondKernelCDF_preCDF ρ
  have hae_eq_pre : ∀ᵐ s ∂ρ.fst, ∀ q : ℚ, ψ q s = (preCDF ρ q s).toReal := by
    rw [ae_all_iff]
    intro q
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (μ := ρ.fst)
      (fun _ _ _ ↦ (hint q).integrableOn)
      (fun _ _ _ ↦ (hpre.integrable () q).integrableOn) (fun A hA _ ↦ ?_)
    rw [hsetInt q hA]
    simpa [Kernel.const_apply] using (hpre.setIntegral () hA q).symm
  have hRat : IsRatCondKernelCDF f (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) :=
    { measurable := hfm
      isRatStieltjesPoint_ae := fun u ↦ by
        cases u
        filter_upwards [hae_eq_pre, hpre.isRatStieltjesPoint_ae ()] with s hseq hsp
        have hf_eq : f ((), s) = fun q ↦ (preCDF ρ q s).toReal := funext hseq
        exact ⟨hf_eq ▸ hsp.mono, hf_eq ▸ hsp.tendsto_atTop_one,
          hf_eq ▸ hsp.tendsto_atBot_zero, hf_eq ▸ hsp.iInf_rat_gt_eq⟩
      integrable := fun _ q ↦ hint q
      setIntegral := fun _ _ hA q ↦ hsetInt q hA }
  have hCond : IsCondKernelCDF F (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) :=
    isCondKernelCDF_stieltjesOfMeasurableRat hRat
  have htoK : hCond.toKernel F = η := by
    ext p A _
    rfl
  have hfst_const : Kernel.fst (Kernel.const Unit ρ) = Kernel.const Unit ρ.fst := by
    ext u A hA
    rw [Kernel.fst_apply, Kernel.const_apply, Kernel.const_apply, Measure.fst_apply hA,
      Measure.map_apply measurable_fst hA]
  have hη_dis : Kernel.fst (Kernel.map κ (Prod.map (id : S → S) e)) ⊗ₖ η =
      Kernel.map κ (Prod.map (id : S → S) e) := by
    rw [hκ', hfst_const, ← htoK]
    exact compProd_toKernel hCond
  have hKunit_dis : Kernel.fst κ ⊗ₖ Kunit = κ :=
    Kernel.compProd_fst_borelMarkovFromReal κ η hη_dis
  have heval := congrArg (fun k : Kernel Unit (S × X) ↦ k ()) hKunit_dis
  rw [Kernel.const_apply] at heval
  rw [← heval]
  ext A hA
  rw [Kernel.compProd_apply hA, Measure.compProd_apply hA, Kernel.fst_apply, Kernel.const_apply]
  have hfst : Measure.map Prod.fst ((P θ).map (fun x ↦ (T x, x))) = (P θ).map T := by
    rw [Measure.map_map measurable_fst hpair]
    rfl
  rw [hfst]
  rfl

/-- **Conditional-expectation characterization of sufficiency** (Pfanzagl, Corollary 1.3.11):
on a nonempty standard Borel space `X`, a measurable statistic `T` is sufficient for a family of
probability measures `P` if and only if every bounded measurable function `φ : X → ℝ` admits a
parameter-free measurable `ψ : S → ℝ` with `(P θ)[φ | σ(T)] =ᵐ[P θ] ψ ∘ T` for all `θ`. -/
theorem isSufficientStatistic_iff_exists_condExp_ae_eq [StandardBorelSpace X] [Nonempty X]
    {P : Θ → Measure X} [∀ θ, IsProbabilityMeasure (P θ)] {T : X → S} (hT : Measurable T) :
    IsSufficientStatistic P T ↔
      ∀ φ : X → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
        ∃ ψ : S → ℝ, Measurable ψ ∧
          ∀ θ, (P θ)[φ | MeasurableSpace.comap T inferInstance] =ᵐ[P θ] ψ ∘ T := by
  refine ⟨fun h φ hφ ⟨C, hC⟩ ↦ ?_, isSufficientStatistic_of_exists_condExp_ae_eq hT⟩
  have hint : ∀ θ, Integrable φ (P θ) := fun θ ↦
    Integrable.of_bound hφ.aestronglyMeasurable C
      (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hC x)
  obtain ⟨ψ, hψ, hce⟩ := h.exists_condExp_ae_eq hφ.stronglyMeasurable hint
  exact ⟨ψ, hψ.measurable, hce⟩

end TauCeti
