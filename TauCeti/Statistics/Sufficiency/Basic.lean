/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

import Mathlib.Probability.Kernel.MeasurableIntegral
import TauCeti.Probability.Kernel.Composition.MeasureCompProd
import TauCeti.Probability.Kernel.Disintegration.CDFToKernel
import TauCeti.Probability.Kernel.Disintegration.Map
import TauCeti.Probability.Kernel.Disintegration.StandardBorel

/-!
# Sufficient and minimal sufficient statistics

This file defines sufficient and minimal sufficient statistics for parametric families of measures
and develops the conditional-expectation characterization of sufficiency:

* `TauCeti.IsSufficientStatistic P T`: `T : X → S` is measurable and there exists a single Markov
  kernel `K : Kernel S X` disintegrating every joint law `(P θ).map (fun x ↦ (T x, x))` as
  `(P θ).map T ⊗ₘ K`.
* `TauCeti.IsMinimalSufficientStatistic.{u, v, w, r} P T`: `T` is sufficient and factors
  `P θ`-almost everywhere through every sufficient statistic `U : X → S'` whose codomain
  `S' : Type r` lies in the explicit universe parameter `r`, via a measurable map `φ : S' → S`.
* `TauCeti.isSufficientStatistic_iff_exists_condExp_ae_eq`: on a nonempty standard Borel space `X`,
  a measurable statistic `T` is sufficient for a family of finite measures `P` if and only if
  every bounded measurable `φ : X → ℝ` admits a single measurable `ψ : S → ℝ` with
  `(P θ)[φ | comap T _] =ᵐ[P θ] ψ ∘ T` for all `θ`.

The generic disintegration infrastructure used here lives in
`TauCeti.Probability.Kernel.Disintegration.Map`,
`TauCeti.Probability.Kernel.Disintegration.CDFToKernel`, and
`TauCeti.Probability.Kernel.Disintegration.StandardBorel`. The converse direction
(`TauCeti.isSufficientStatistic_of_exists_condExp_ae_eq`) adapts Mathlib's `condKernelReal`
construction (`stieltjesOfMeasurableRat`, `isRatCondKernelCDF_preCDF`,
`isCondKernelCDF_stieltjesOfMeasurableRat`, `compProd_toKernel`, and `Kernel.borelMarkovFromReal`
from `Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean`, `CDFToKernel.lean`,
`MeasurableStieltjes.lean`, and `CondCDF.lean`), replacing `preCDF` with the parameter-free
conditional-expectation versions.

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
  simp only [id_eq]

/-- A constant statistic is sufficient for a nonempty family of probability measures if and only
if all measures in the family are equal. -/
theorem isSufficientStatistic_const_iff [Nonempty Θ] {P : Θ → Measure X}
    [∀ θ, IsProbabilityMeasure (P θ)] (s₀ : S) :
    IsSufficientStatistic P (fun _ ↦ s₀) ↔ ∀ θ₁ θ₂, P θ₁ = P θ₂ := by
  refine ⟨fun h θ₁ θ₂ ↦ ?_, fun hconst ↦ ?_⟩
  · obtain ⟨_, K, _, hdis⟩ := h
    have hrec (θ : Θ) : P θ = K ∘ₘ Measure.dirac s₀ := by
      have hmap : (P θ).map (fun _ : X ↦ s₀) = Measure.dirac s₀ := by
        rw [Measure.map_const, measure_univ, one_smul]
      rw [← comp_map_eq_self_of_map_prodMk_eq_compProd measurable_const (hdis θ), hmap]
    exact (hrec θ₁).trans (hrec θ₂).symm
  · let θ₀ : Θ := Classical.arbitrary Θ
    have hpair : Measurable fun x : X ↦ (s₀, x) := measurable_const.prodMk measurable_id
    refine ⟨measurable_const, Kernel.const S (P θ₀), inferInstance, fun θ ↦ ?_⟩
    rw [hconst θ θ₀]
    ext A hA
    rw [Measure.map_apply hpair hA, Measure.compProd_apply hA]
    have hmap : (P θ₀).map (fun _ : X ↦ s₀) = Measure.dirac s₀ := by
      rw [Measure.map_const, measure_univ, one_smul]
    rw [hmap, lintegral_dirac' _ (Kernel.measurable_kernel_prodMk_left hA), Kernel.const_apply]

/-- Any constant statistic is sufficient for a constant nonempty family of probability measures. -/
theorem isSufficientStatistic_const [Nonempty Θ] {P : Θ → Measure X}
    [∀ θ, IsProbabilityMeasure (P θ)] (hconst : ∀ θ₁ θ₂, P θ₁ = P θ₂) (s₀ : S) :
    IsSufficientStatistic P (fun _ ↦ s₀) :=
  (isSufficientStatistic_const_iff s₀).mpr hconst

/-- Composing a sufficient statistic with a measurable equivalence preserves sufficiency. -/
theorem IsSufficientStatistic.comp_measurableEquiv {P : Θ → Measure X} [∀ θ, SFinite (P θ)]
    {T : X → S} (h : IsSufficientStatistic P T) (e : S ≃ᵐ S') :
    IsSufficientStatistic P (e ∘ T) := by
  obtain ⟨hT, K, hK, hdis⟩ := h
  refine ⟨e.measurable.comp hT, K.comap e.symm e.symm.measurable, inferInstance, fun θ ↦ ?_⟩
  have hK' : (K.comap e.symm e.symm.measurable).comap e e.measurable = K := by
    rw [← Kernel.comap_comp_right]
    simp
  calc (P θ).map (fun x ↦ ((e ∘ T) x, x))
    _ = ((P θ).map (fun x ↦ (T x, x))).map (Prod.map e id) :=
        (Measure.map_map (e.measurable.prodMap measurable_id) (hT.prodMk measurable_id)).symm
    _ = ((P θ).map T ⊗ₘ K).map (Prod.map e id) := by rw [hdis θ]
    _ = ((P θ).map T ⊗ₘ (K.comap e.symm e.symm.measurable).comap e e.measurable).map
          (Prod.map e id) := by rw [hK']
    _ = ((P θ).map T).map e ⊗ₘ K.comap e.symm e.symm.measurable :=
        Measure.map_prodMap_compProd_comap _ _ e.measurable
    _ = (P θ).map (e ∘ T) ⊗ₘ K.comap e.symm e.symm.measurable := by
        rw [Measure.map_map e.measurable hT]

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

/-- A statistic `T : X → S` is minimal sufficient for `P : Θ → Measure X` (with respect to the
explicit universe parameter `r`) if it is sufficient and factors almost everywhere under every
`P θ` through every sufficient statistic `U : X → S'` whose codomain `S' : Type r` lies in
universe `r`, via a measurable map `φ : S' → S`. -/
def IsMinimalSufficientStatistic.{u, v, w, r} {Θ : Type u} {X : Type v} {S : Type w}
    [MeasurableSpace X] [MeasurableSpace S] (P : Θ → Measure X) (T : X → S) : Prop :=
  IsSufficientStatistic P T ∧ ∀ (S' : Type r) [MeasurableSpace S'] (U : X → S'),
    IsSufficientStatistic P U → ∃ φ : S' → S, Measurable φ ∧ ∀ θ, T =ᵐ[P θ] φ ∘ U

/-- Unfolding lemma for `IsMinimalSufficientStatistic.{u, v, w, r}`, making explicit the
quantification over sufficient statistics with codomain `S' : Type r` in universe `r`. -/
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

/-- A minimal sufficient statistic `IsMinimalSufficientStatistic.{u, v, w, r} P T` factors almost
everywhere through any sufficient statistic `U : X → S'` whose codomain `S' : Type r` lies in
universe `r`, via a measurable map `φ : S' → S`. -/
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

/-- A constant statistic is minimal sufficient for a nonempty family of probability measures if and
only if all measures in the family are equal. -/
theorem isMinimalSufficientStatistic_const_iff [Nonempty Θ] {P : Θ → Measure X}
    [∀ θ, IsProbabilityMeasure (P θ)] (s₀ : S) :
    IsMinimalSufficientStatistic P (fun _ ↦ s₀) ↔ ∀ θ₁ θ₂, P θ₁ = P θ₂ :=
  ⟨fun h ↦ (isSufficientStatistic_const_iff s₀).mp h.isSufficientStatistic,
    fun hconst ↦ isMinimalSufficientStatistic_const hconst s₀⟩

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
then `T` is sufficient for the family of finite measures `P`.

Adapts Mathlib's `condKernelReal` construction (`stieltjesOfMeasurableRat`,
`isRatCondKernelCDF_preCDF`, `isCondKernelCDF_stieltjesOfMeasurableRat`, `compProd_toKernel`,
and `Kernel.borelMarkovFromReal`), via `ProbabilityTheory.kernelOfMeasurableRat`,
`ProbabilityTheory.compProd_fst_kernelOfMeasurableRat_of_forall_setIntegral_eq`, and
`MeasureTheory.Measure.compProd_fst_borelMarkovFromReal`, replacing `preCDF` with the
parameter-free conditional expectations of the rational half-line indicators
`1_{embeddingReal X ≤ q}`. -/
theorem isSufficientStatistic_of_exists_condExp_ae_eq [StandardBorelSpace X] [Nonempty X]
    {P : Θ → Measure X} [∀ θ, IsFiniteMeasure (P θ)] {T : X → S} (hT : Measurable T)
    (hce : ∀ φ : X → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
      ∃ ψ : S → ℝ, Measurable ψ ∧
        ∀ θ, (P θ)[φ | MeasurableSpace.comap T inferInstance] =ᵐ[P θ] ψ ∘ T) :
    IsSufficientStatistic P T := by
  let e : X → ℝ := embeddingReal X
  have he : MeasurableEmbedding e := measurableEmbedding_embeddingReal X
  -- Phase 1: choose parameter-free measurable conditional-expectation versions `ψ q` for
  -- the rational half-line indicators `1_{e ≤ q}`.
  have hchoice : ∀ q : ℚ, ∃ ψ : S → ℝ, Measurable ψ ∧
      ∀ θ, (P θ)[(e ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) |
        MeasurableSpace.comap T inferInstance] =ᵐ[P θ] ψ ∘ T := fun q ↦
    hce _ (measurable_const.indicator (he.measurable measurableSet_Iic)) ⟨1, fun x ↦ by
      rw [← Real.norm_eq_abs]
      exact (norm_indicator_le_norm_self (s := e ⁻¹' Iic (q : ℝ))
        (f := fun _ ↦ (1 : ℝ)) (a := x)).trans_eq norm_one⟩
  choose ψ hψm hψce using hchoice
  -- Phase 2: build a single parameter-free Markov kernel `K` from `ψ` via
  -- `kernelOfMeasurableRat` and `Kernel.borelMarkovFromReal`.
  let f : S → ℚ → ℝ := fun s q ↦ ψ q s
  have hfm : Measurable f := measurable_pi_iff.mpr hψm
  let η : Kernel S ℝ := kernelOfMeasurableRat f hfm
  let K : Kernel S X := Kernel.borelMarkovFromReal X η
  -- Phase 3: for each `θ`, verify that `η` disintegrates `(P θ).map (T, e)` via the set-integral
  -- identity, then transport the disintegration back to `(P θ).map (T, id)`.
  refine ⟨hT, K, inferInstance, fun θ ↦ ?_⟩
  let ρX : Measure (S × X) := (P θ).map (fun x ↦ (T x, x))
  let ρ : Measure (S × ℝ) := (P θ).map (fun x ↦ (T x, e x))
  have hρXfst : ρX.fst = (P θ).map T := Measure.fst_map_prodMk hT measurable_id'
  have hρfst : ρ.fst = (P θ).map T := Measure.fst_map_prodMk hT he.measurable
  have hρeq : ρX.map (Prod.map (id : S → S) e) = ρ := by
    rw [Measure.map_map (measurable_id.prodMap he.measurable) (hT.prodMk measurable_id')]
    simp only [ρ, Function.comp_def, Prod.map_apply, id_eq]
  have hint : ∀ q : ℚ, Integrable (fun s ↦ f s q) ρ.fst := fun q ↦ by
    rw [hρfst, integrable_map_measure (hψm q).aestronglyMeasurable hT.aemeasurable]
    exact integrable_condExp.congr (hψce q θ)
  have hreal : ρ.fst ⊗ₘ η = ρ :=
    compProd_fst_kernelOfMeasurableRat_of_forall_setIntegral_eq hfm hint fun hA q ↦
      setIntegral_fst_map_prodMk_eq_measureReal_of_condExp_ae_eq hT he.measurable
        measurableSet_Iic (hψm q).aestronglyMeasurable (hψce q θ) hA
  have hX : ρX.fst ⊗ₘ K = ρX :=
    Measure.compProd_fst_borelMarkovFromReal ρX η (by rw [hρXfst, ← hρfst, hreal, hρeq])
  rw [← hρXfst, hX]

/-- **Conditional-expectation characterization of sufficiency** (Pfanzagl, Corollary 1.3.11):
on a nonempty standard Borel space `X`, a measurable statistic `T` is sufficient for a family of
finite measures `P` if and only if every bounded measurable function `φ : X → ℝ` admits a
parameter-free measurable `ψ : S → ℝ` with `(P θ)[φ | σ(T)] =ᵐ[P θ] ψ ∘ T` for all `θ`. -/
theorem isSufficientStatistic_iff_exists_condExp_ae_eq [StandardBorelSpace X] [Nonempty X]
    {P : Θ → Measure X} [∀ θ, IsFiniteMeasure (P θ)] {T : X → S} (hT : Measurable T) :
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
