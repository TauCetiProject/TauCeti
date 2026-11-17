/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import TauCeti.Probability.Kernel.Disintegration.Map

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
  a measurable statistic `T` is sufficient for a family of probability laws `P` if and only if
  every bounded measurable `φ : X → ℝ` admits a single measurable `ψ : S → ℝ` with
  `(P θ)[φ | comap T _] =ᵐ[P θ] ψ ∘ T` for all `θ`.

The generic measure- and kernel-theoretic disintegration identities used here live in
`TauCeti.Probability.Kernel.Disintegration.Map`. The converse direction
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
    simp only [Function.comp_def, Prod.map_apply, id_eq]
  rw [hmap1, Measure.map_apply (e.measurable.prodMap measurable_id) hA, hdis θ,
    Measure.compProd_apply hA', Measure.compProd_apply hA, ← Measure.map_map e.measurable hT,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hA) e.measurable]
  refine lintegral_congr fun s ↦ ?_
  rw [Kernel.comap_apply, e.symm_apply_apply]
  simp only [Set.preimage_preimage, Prod.map_apply, id_eq]

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

/-- Set-integral identity for a conditional-expectation version `ψ ∘ T` of the indicator
`1_{e ≤ q}`: integrating `ψ` over `A` under the first marginal of `ρ = P.map (T, e)` gives the
real joint mass `ρ.real (A ×ˢ Iic q)`. -/
private theorem setIntegral_eq_measureReal_prod_Iic_of_condExp_ae_eq {P : Measure X}
    [IsProbabilityMeasure P] {T : X → S} (hT : Measurable T) {e : X → ℝ} (he : Measurable e)
    {q : ℚ} {ψ : S → ℝ} (hψ : Measurable ψ)
    (hce : P[(e ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) |
      MeasurableSpace.comap T inferInstance] =ᵐ[P] ψ ∘ T)
    {A : Set S} (hA : MeasurableSet A) :
    ∫ s in A, ψ s ∂(P.map (fun x ↦ (T x, e x))).fst =
      (P.map (fun x ↦ (T x, e x))).real (A ×ˢ Iic (q : ℝ)) := by
  have hρfst : (P.map (fun x ↦ (T x, e x))).fst = P.map T := by
    rw [Measure.fst, Measure.map_map measurable_fst (hT.prodMk he)]
    simp only [Function.comp_def]
  have hφint : Integrable ((e ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ))) P :=
    Integrable.of_bound
      (measurable_const.indicator (he measurableSet_Iic)).aestronglyMeasurable 1
      (ae_of_all _ fun x ↦
        (norm_indicator_le_norm_self (s := e ⁻¹' Iic (q : ℝ))
          (f := fun _ ↦ (1 : ℝ)) (a := x)).trans_eq norm_one)
  calc ∫ s in A, ψ s ∂(P.map (fun x ↦ (T x, e x))).fst
    _ = ∫ s in A, ψ s ∂P.map T := by rw [hρfst]
    _ = ∫ x in T ⁻¹' A, ψ (T x) ∂P :=
        setIntegral_map hA hψ.aestronglyMeasurable hT.aemeasurable
    _ = ∫ x in T ⁻¹' A,
          P[(e ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) |
            MeasurableSpace.comap T inferInstance] x ∂P :=
        setIntegral_congr_ae (hT hA) (hce.symm.mono fun _ hx _ ↦ hx)
    _ = ∫ x in T ⁻¹' A, (e ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) x ∂P :=
        setIntegral_condExp hT.comap_le hφint ⟨A, hA, rfl⟩
    _ = P.real (T ⁻¹' A ∩ e ⁻¹' Iic (q : ℝ)) := by
        rw [setIntegral_indicator (he measurableSet_Iic), setIntegral_const, smul_eq_mul, mul_one]
    _ = (P.map (fun x ↦ (T x, e x))).real (A ×ˢ Iic (q : ℝ)) := by
        rw [Measure.real, Measure.real,
          Measure.map_apply (hT.prodMk he) (hA.prod measurableSet_Iic), Set.mk_preimage_prod]

/-- A measurable rational family `ψ : ℚ → S → ℝ` matching the set integrals of `ρ.real (· ×ˢ Iic q)`
agrees `ρ.fst`-almost everywhere with `preCDF ρ` and therefore defines an `IsRatCondKernelCDF` for
`Kernel.const Unit ρ`. -/
private theorem isRatCondKernelCDF_of_forall_setIntegral_eq (ρ : Measure (S × ℝ))
    [IsFiniteMeasure ρ] {ψ : ℚ → S → ℝ} (hψm : ∀ q, Measurable (ψ q))
    (hint : ∀ q, Integrable (ψ q) ρ.fst)
    (hsetInt : ∀ (q : ℚ) {A : Set S}, MeasurableSet A →
      ∫ s in A, ψ q s ∂ρ.fst = ρ.real (A ×ˢ Iic (q : ℝ))) :
    IsRatCondKernelCDF (fun (p : Unit × S) q ↦ ψ q p.2)
      (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) := by
  have hfm : Measurable fun (p : Unit × S) q ↦ ψ q p.2 :=
    measurable_pi_iff.mpr fun q ↦ (hψm q).comp measurable_snd
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
  exact
    { measurable := hfm
      isRatStieltjesPoint_ae := fun u ↦ by
        cases u
        filter_upwards [hae_eq_pre, hpre.isRatStieltjesPoint_ae ()] with s hseq hsp
        have hf_eq : (fun q ↦ ψ q s) = fun q ↦ (preCDF ρ q s).toReal := funext hseq
        refine ⟨hf_eq ▸ hsp.mono, hf_eq ▸ hsp.tendsto_atTop_one,
          hf_eq ▸ hsp.tendsto_atBot_zero, fun t ↦ ?_⟩
        simpa only [hseq] using hsp.iInf_rat_gt_eq t
      integrable := fun _ q ↦ hint q
      setIntegral := fun _ _ hA q ↦ hsetInt q hA }

/-- Markov kernel into `ℝ` built from a measurable rational CDF family via Mathlib's
`stieltjesOfMeasurableRat`, independent of any particular law in the statistical family. -/
private def kernelOfMeasurableRat (f : Unit × S → ℚ → ℝ) (hfm : Measurable f) :
    Kernel (Unit × S) ℝ where
  toFun p := (stieltjesOfMeasurableRat f hfm p).measure
  measurable' := StieltjesFunction.measurable_measure (measurable_stieltjesOfMeasurableRat hfm)
    (tendsto_stieltjesOfMeasurableRat_atBot hfm)
    (tendsto_stieltjesOfMeasurableRat_atTop hfm)

/-- Defining evaluation lemma for `kernelOfMeasurableRat`. -/
private theorem kernelOfMeasurableRat_apply (f : Unit × S → ℚ → ℝ) (hfm : Measurable f)
    (p : Unit × S) :
    kernelOfMeasurableRat f hfm p = (stieltjesOfMeasurableRat f hfm p).measure :=
  (rfl)

private instance isMarkovKernel_kernelOfMeasurableRat (f : Unit × S → ℚ → ℝ) (hfm : Measurable f) :
    IsMarkovKernel (kernelOfMeasurableRat f hfm) :=
  ⟨fun p ↦ (stieltjesOfMeasurableRat f hfm p).isProbabilityMeasure
    (tendsto_stieltjesOfMeasurableRat_atBot hfm p)
    (tendsto_stieltjesOfMeasurableRat_atTop hfm p)⟩

/-- Transporting an `IsRatCondKernelCDF` verification for `P.map (T, embeddingReal X)` to a
disintegration of `P.map (T, id)` via `Kernel.borelMarkovFromReal`. -/
private theorem map_prodMk_eq_compProd_of_isRatCondKernelCDF [StandardBorelSpace X] [Nonempty X]
    {P : Measure X} [IsProbabilityMeasure P] {T : X → S} (hT : Measurable T)
    {f : Unit × S → ℚ → ℝ} (hfm : Measurable f)
    (hRat : IsRatCondKernelCDF f
      (Kernel.const Unit (P.map (fun x ↦ (T x, embeddingReal X x))))
      (Kernel.const Unit (P.map (fun x ↦ (T x, embeddingReal X x))).fst)) :
    P.map (fun x ↦ (T x, x)) =
      P.map T ⊗ₘ (Kernel.borelMarkovFromReal X (kernelOfMeasurableRat f hfm)).comap
        (fun s ↦ ((), s)) (measurable_const.prodMk measurable_id) := by
  let e : X → ℝ := embeddingReal X
  have he : MeasurableEmbedding e := measurableEmbedding_embeddingReal X
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  let η : Kernel (Unit × S) ℝ := kernelOfMeasurableRat f hfm
  let Kunit : Kernel (Unit × S) X := Kernel.borelMarkovFromReal X η
  let κ : Kernel Unit (S × X) := Kernel.const Unit (P.map (fun x ↦ (T x, x)))
  let ρ : Measure (S × ℝ) := P.map (fun x ↦ (T x, e x))
  have hκ' : Kernel.map κ (Prod.map (id : S → S) e) = Kernel.const Unit ρ := by
    ext u A _
    rw [Kernel.map_apply _ (measurable_id.prodMap he.measurable), Kernel.const_apply,
      Kernel.const_apply, Measure.map_map (measurable_id.prodMap he.measurable) hpair]
    dsimp only [ρ]
    simp only [Function.comp_def, Prod.map_apply, id_eq]
  have hCond : IsCondKernelCDF (stieltjesOfMeasurableRat f hfm)
      (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) :=
    isCondKernelCDF_stieltjesOfMeasurableRat hRat
  have htoK : hCond.toKernel (stieltjesOfMeasurableRat f hfm) = η := by
    ext p
    rw [IsCondKernelCDF.toKernel_apply, kernelOfMeasurableRat_apply]
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
  have hfst : Measure.map Prod.fst (P.map (fun x ↦ (T x, x))) = P.map T := by
    rw [Measure.map_map measurable_fst hpair]
    simp only [Function.comp_def]
  rw [hfst]
  refine lintegral_congr fun s ↦ ?_
  rw [Kernel.comap_apply]

/-- On a nonempty standard Borel space `X`, if every bounded measurable `φ : X → ℝ` has a
parameter-free measurable version `ψ ∘ T` of the conditional expectation `(P θ)[φ | σ(T)]`,
then `T` is sufficient for the family of probability laws `P`.

Adapts Mathlib's `condKernelReal` construction (`stieltjesOfMeasurableRat`,
`isRatCondKernelCDF_preCDF`, `isCondKernelCDF_stieltjesOfMeasurableRat`, `compProd_toKernel`,
and `Kernel.borelMarkovFromReal`), replacing `preCDF` with the parameter-free conditional
expectations of the rational half-line indicators `1_{embeddingReal X ≤ q}`. -/
theorem isSufficientStatistic_of_exists_condExp_ae_eq [StandardBorelSpace X] [Nonempty X]
    {P : Θ → Measure X} [∀ θ, IsProbabilityMeasure (P θ)] {T : X → S} (hT : Measurable T)
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
  -- `stieltjesOfMeasurableRat` and `Kernel.borelMarkovFromReal`.
  let f : Unit × S → ℚ → ℝ := fun p q ↦ ψ q p.2
  have hfm : Measurable f := measurable_pi_iff.mpr fun q ↦ (hψm q).comp measurable_snd
  let K : Kernel S X :=
    (Kernel.borelMarkovFromReal X (kernelOfMeasurableRat f hfm)).comap
      (fun s ↦ ((), s)) (measurable_const.prodMk measurable_id)
  -- Phase 3: for each `θ`, verify `IsRatCondKernelCDF` via the set-integral identity and
  -- transport the resulting real disintegration back to `X`.
  refine ⟨hT, K, inferInstance, fun θ ↦ ?_⟩
  let ρ : Measure (S × ℝ) := (P θ).map (fun x ↦ (T x, e x))
  have hρfst : ρ.fst = (P θ).map T := by
    rw [Measure.fst, Measure.map_map measurable_fst (hT.prodMk he.measurable)]
    simp only [Function.comp_def]
  have hint : ∀ q : ℚ, Integrable (ψ q) ρ.fst := fun q ↦ by
    rw [hρfst, integrable_map_measure (hψm q).aestronglyMeasurable hT.aemeasurable]
    exact integrable_condExp.congr (hψce q θ)
  have hRat : IsRatCondKernelCDF f (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) :=
    isRatCondKernelCDF_of_forall_setIntegral_eq ρ hψm hint fun q _ hA ↦
      setIntegral_eq_measureReal_prod_Iic_of_condExp_ae_eq hT he.measurable (hψm q) (hψce q θ) hA
  exact map_prodMk_eq_compProd_of_isRatCondKernelCDF hT hfm hRat

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
