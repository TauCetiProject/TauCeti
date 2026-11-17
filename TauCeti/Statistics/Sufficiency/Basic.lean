/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Kernel.CondDistrib
public import TauCeti.Statistics.Mixture
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# Sufficient and minimal sufficient statistics

A statistic `T : X → S` is sufficient for a family of measures `P : Θ → Measure X` if a single
Markov kernel `K : Kernel S X`, independent of the parameter `θ`, disintegrates every joint law
`(P θ).map (fun x ↦ (T x, x))` as `(P θ).map T ⊗ₘ K`. It is minimal sufficient if it is sufficient
and factors almost everywhere through every other sufficient statistic via a measurable map
independent of `θ`.

This file establishes the characteristic API of `TauCeti.IsSufficientStatistic` and
`TauCeti.IsMinimalSufficientStatistic`, the disintegration integration identity (including for
mixtures `P ∘ₘ Λ` and countable mixtures), the parameter-free conditional-expectation formula for
disintegrating kernels, and the conditional-expectation characterization of sufficiency on standard
Borel spaces (Pfanzagl, Corollary 1.3.11).

## Main definitions

* `TauCeti.IsSufficientStatistic P T`: `T` is measurable and one Markov kernel disintegrates
  `(P θ).map (fun x ↦ (T x, x))` for every `θ`.
* `TauCeti.IsMinimalSufficientStatistic P T`: `T` is sufficient and factors almost everywhere
  through every sufficient statistic via a measurable map.

## Main results

* `TauCeti.comp_map_eq_of_map_prod_eq_compProd`: a disintegrating kernel averages to the original
  measure (`K ∘ₘ μ.map T = μ`).
* `TauCeti.integral_smul_eq_of_map_prod_eq_compProd`: the disintegration integration identity
  `∫ x, g (T x) • φ x ∂μ = ∫ x, g (T x) • ∫ y, φ y ∂K (T x) ∂μ`.
* `TauCeti.comp_map_prod_eq_compProd_of_forall` and `TauCeti.countableMixture_map_prod_eq_compProd`:
  a common disintegrating kernel also disintegrates any kernel mixture `P ∘ₘ Λ` and any countable
  mixture.
* `TauCeti.condExp_ae_eq_integral_of_map_prod_eq_compProd`: without assuming `StandardBorelSpace`,
  an s-finite kernel disintegrating `μ` along `T` computes conditional expectations given `σ(T)`.
* `TauCeti.isSufficientStatistic_iff_forall_exists_condExp_ae_eq`: on a nonempty standard Borel
  space, `T` is sufficient iff every bounded measurable function admits a parameter-free version of
  its conditional expectation given `σ(T)`.

## References

* J. Pfanzagl, *Parametric Statistical Theory*, de Gruyter, 1994, Definition 1.1.1,
  Corollary 1.3.11, and Definition 1.4.1.
* M. J. Schervish, *Theory of Statistics*, Springer, 1995, Definitions 2.8 and 2.28.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace TauCeti

section Disintegration

variable {Θ X S : Type*} [MeasurableSpace X] [mS : MeasurableSpace S]
  {μ : Measure X} {T : X → S} {K : Kernel S X}

/-- A kernel disintegrating `μ` along `T` reconstructs `μ` by averaging against `μ.map T`. -/
theorem comp_map_eq_of_map_prod_eq_compProd [SFinite μ] [IsSFiniteKernel K]
    (hT : Measurable T) (hK : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K) :
    K ∘ₘ μ.map T = μ := by
  have hprod : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  rw [← Measure.snd_compProd, ← hK, Measure.snd, Measure.map_map measurable_snd hprod]
  exact Measure.map_id'

/-- General disintegration integration identity for a function of `(T x, x)`. -/
theorem integral_eq_integral_integral_of_map_prod_eq_compProd [SFinite μ] [IsSFiniteKernel K]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hT : Measurable T) (hK : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K)
    {f : S × X → F} (hf : Integrable f (μ.map (fun x ↦ (T x, x)))) :
    ∫ x, f (T x, x) ∂μ = ∫ x, ∫ y, f (T x, y) ∂K (T x) ∂μ := by
  have hprod : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  have hKint : Integrable f (μ.map T ⊗ₘ K) := hK ▸ hf
  have hinner : AEStronglyMeasurable (fun s ↦ ∫ y, f (s, y) ∂K s) (μ.map T) := by
    simpa only [Measure.compProd, Kernel.prodMkLeft_apply, Kernel.const_apply] using
      hKint.aestronglyMeasurable.integral_kernel_compProd
  rw [← integral_map hprod.aemeasurable hf.aestronglyMeasurable,
    hK, Measure.integral_compProd hKint, ← integral_map hT.aemeasurable hinner]

/-- Disintegration integration identity for a product `g (T x) • φ x`. -/
theorem integral_smul_eq_of_map_prod_eq_compProd [SFinite μ] [IsSFiniteKernel K]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hT : Measurable T) (hK : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K)
    {g : S → ℝ} {φ : X → F} (hg : StronglyMeasurable g) (hφ : StronglyMeasurable φ)
    (hint : Integrable (fun x ↦ g (T x) • φ x) μ) :
    ∫ x, g (T x) • φ x ∂μ = ∫ x, g (T x) • ∫ y, φ y ∂K (T x) ∂μ := by
  have hprod : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  have hprod_meas : StronglyMeasurable fun p : S × X ↦ g p.1 • φ p.2 :=
    (hg.comp_measurable measurable_fst).smul (hφ.comp_measurable measurable_snd)
  have hprod_int : Integrable (fun p : S × X ↦ g p.1 • φ p.2) (μ.map (fun x ↦ (T x, x))) := by
    rwa [integrable_map_measure hprod_meas.aestronglyMeasurable hprod.aemeasurable]
  rw [integral_eq_integral_integral_of_map_prod_eq_compProd hT hK hprod_int]
  simp_rw [integral_smul]

/-- Disintegration integration identity for bounded measurable real functions `g` and `φ` under a
finite measure `μ`. -/
theorem integral_mul_eq_of_map_prod_eq_compProd_of_bdd [IsFiniteMeasure μ] [IsSFiniteKernel K]
    (hT : Measurable T) (hK : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K)
    {g : S → ℝ} {φ : X → ℝ} (hg : Measurable g) (hφ : Measurable φ)
    {Cg Cφ : ℝ} (hg_bdd : ∀ s, |g s| ≤ Cg) (hφ_bdd : ∀ x, |φ x| ≤ Cφ) :
    ∫ x, g (T x) * φ x ∂μ = ∫ x, g (T x) * ∫ y, φ y ∂K (T x) ∂μ := by
  have hφ_int : Integrable φ μ :=
    Integrable.of_bound hφ.aestronglyMeasurable Cφ (ae_of_all _ fun x ↦ by simpa using hφ_bdd x)
  have hmul_int : Integrable (fun x ↦ g (T x) * φ x) μ :=
    hφ_int.bdd_mul (hg.comp hT).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa using hg_bdd (T x))
  simpa only [smul_eq_mul] using
    integral_smul_eq_of_map_prod_eq_compProd hT hK hg.stronglyMeasurable hφ.stronglyMeasurable
      hmul_int

/-- A kernel that disintegrates every fiber of a kernel `P : Kernel Θ X` along `T` also
disintegrates any mixture `P ∘ₘ Λ`. -/
theorem comp_map_prod_eq_compProd_of_forall [MeasurableSpace Θ]
    (P : Kernel Θ X) [IsSFiniteKernel P] (Λ : Measure Θ) [SFinite Λ] [IsSFiniteKernel K]
    (hT : Measurable T) (hK : ∀ θ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K) :
    (P ∘ₘ Λ).map (fun x ↦ (T x, x)) = (P ∘ₘ Λ).map T ⊗ₘ K := by
  have hprod : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  ext A hA
  have hK_meas : Measurable fun s ↦ K s (Prod.mk s ⁻¹' A) :=
    Kernel.measurable_kernel_prodMk_left hA
  have hKT_meas : Measurable fun x ↦ K (T x) (Prod.mk (T x) ⁻¹' A) := hK_meas.comp hT
  rw [Measure.map_apply hprod hA, Measure.bind_apply (hprod hA) P.aemeasurable,
    Measure.compProd_apply hA, lintegral_map hK_meas hT,
    Measure.lintegral_bind P.aemeasurable hKT_meas.aemeasurable]
  refine lintegral_congr fun θ ↦ ?_
  rw [← Measure.map_apply hprod hA, hK θ, Measure.compProd_apply hA, lintegral_map hK_meas hT]

/-- A kernel that disintegrates every member of a family `P` along `T` also disintegrates every
countable mixture of `P`. -/
theorem countableMixture_map_prod_eq_compProd (P : Θ → Measure X) [∀ θ, SFinite (P θ)]
    [IsSFiniteKernel K] (hT : Measurable T)
    (hK : ∀ θ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K) (θs : ℕ → Θ) :
    (countableMixture P θs).map (fun x ↦ (T x, x)) =
      (countableMixture P θs).map T ⊗ₘ K := by
  have hprod : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  rw [map_countableMixture P θs hprod, map_countableMixture P θs hT,
    countableMixture_def, countableMixture_def, Measure.compProd_sum_left]
  congr 1
  ext n : 1
  rw [Measure.compProd_smul_left, hK (θs n)]

/-- An s-finite kernel disintegrating a finite measure `μ` along `T` computes conditional
expectations with respect to `mS.comap T`, without any `StandardBorelSpace` hypothesis on `X`. -/
theorem condExp_ae_eq_integral_of_map_prod_eq_compProd [IsFiniteMeasure μ] [IsSFiniteKernel K]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hT : Measurable T) (hK : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K)
    {φ : X → F} (hφ : Integrable φ μ) :
    μ[φ | mS.comap T] =ᵐ[μ] fun x ↦ ∫ y, φ y ∂K (T x) := by
  have hprod : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  have hprod_int : Integrable (fun p : S × X ↦ φ p.2) (μ.map T ⊗ₘ K) := by
    rw [← hK]
    exact hφ.comp_snd_map_prodMk hT.aemeasurable
  have hψ_asm : AEStronglyMeasurable (fun s ↦ ∫ y, φ y ∂K s) (μ.map T) := by
    simpa only [Measure.compProd, Kernel.prodMkLeft_apply, Kernel.const_apply] using
      hprod_int.aestronglyMeasurable.integral_kernel_compProd
  have hψ_int : Integrable (fun s ↦ ∫ y, φ y ∂K s) (μ.map T) := by
    simpa only [Measure.compProd, Kernel.prodMkLeft_apply, Kernel.const_apply] using
      hprod_int.integral_compProd
  refine (ae_eq_condExp_of_forall_setIntegral_eq hT.comap_le hφ
    (fun s _ _ ↦ (hψ_int.comp_aemeasurable hT.aemeasurable).integrableOn) ?_
    (hψ_asm.comp_ae_measurable' hT.aemeasurable)).symm
  rintro _ ⟨B, hB, rfl⟩ _
  have hpre : (fun x ↦ (T x, x)) ⁻¹' (B ×ˢ Set.univ) = T ⁻¹' B := by
    ext x
    simp
  calc ∫ x in T ⁻¹' B, ∫ y, φ y ∂K (T x) ∂μ
      = ∫ s in B, ∫ y, φ y ∂K s ∂(μ.map T) :=
        (setIntegral_map hB hψ_asm hT.aemeasurable).symm
    _ = ∫ p in B ×ˢ Set.univ, φ p.2 ∂(μ.map T ⊗ₘ K) := by
        rw [Measure.setIntegral_compProd hB MeasurableSet.univ hprod_int.integrableOn]
        simp_rw [Measure.restrict_univ]
    _ = ∫ p in B ×ˢ Set.univ, φ p.2 ∂(μ.map (fun x ↦ (T x, x))) := by rw [← hK]
    _ = ∫ x in T ⁻¹' B, φ x ∂μ := by
        rw [setIntegral_map (hB.prod MeasurableSet.univ)
          (hK ▸ hprod_int).aestronglyMeasurable hprod.aemeasurable, hpre]

end Disintegration

section Sufficiency

variable {Θ X S S' : Type*} [MeasurableSpace X] [mS : MeasurableSpace S]
  [MeasurableSpace S'] {P : Θ → Measure X} {T : X → S}

/-- `IsSufficientStatistic P T` says that `T` is measurable and a single Markov kernel
`K : Kernel S X`, independent of `θ`, disintegrates every joint law
`(P θ).map (fun x ↦ (T x, x))` as `(P θ).map T ⊗ₘ K`. -/
def IsSufficientStatistic (P : Θ → Measure X) (T : X → S) : Prop :=
  Measurable T ∧ ∃ K : Kernel S X, IsMarkovKernel K ∧
    ∀ θ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K

/-- Unfolding characterization of `IsSufficientStatistic`. -/
theorem isSufficientStatistic_iff :
    IsSufficientStatistic P T ↔
      Measurable T ∧ ∃ K : Kernel S X, IsMarkovKernel K ∧
        ∀ θ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K :=
  (Iff.rfl)

namespace IsSufficientStatistic

/-- A sufficient statistic is measurable. -/
theorem measurable (h : IsSufficientStatistic P T) : Measurable T :=
  h.1

/-- A sufficient statistic admits a parameter-free Markov disintegrating kernel. -/
theorem exists_kernel (h : IsSufficientStatistic P T) :
    ∃ K : Kernel S X, IsMarkovKernel K ∧
      ∀ θ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K :=
  h.2

/-- Post-composing a sufficient statistic with a measurable equivalence preserves sufficiency. -/
theorem comp_measurableEquiv [∀ θ, SFinite (P θ)] (h : IsSufficientStatistic P T) (e : S ≃ᵐ S') :
    IsSufficientStatistic P (e ∘ T) := by
  obtain ⟨hT, K, hKm, hK⟩ := h
  refine ⟨e.measurable.comp hT, K.comap e.symm e.symm.measurable, inferInstance, fun θ ↦ ?_⟩
  have hcomp : (K.comap e.symm e.symm.measurable).comap e e.measurable = K := by
    ext s A _
    simp [Kernel.comap_apply]
  have hprod : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  have hmap := Measure.map_prodMap_compProd_comap ((P θ).map T)
    (K.comap e.symm e.symm.measurable) e.measurable
  rw [hcomp, ← hK θ, Measure.map_map (e.measurable.prodMap measurable_id) hprod,
    Measure.map_map e.measurable hT] at hmap
  simpa only [Function.comp_def, Prod.map_apply, id_eq] using hmap

/-- Forward direction of the conditional-expectation characterization of sufficiency: a sufficient
statistic admits a parameter-free strongly measurable version of `(P θ)[φ | mS.comap T]` for every
strongly measurable `φ` integrable under each `P θ`, without assuming `StandardBorelSpace X`. -/
theorem exists_condExp_ae_eq [∀ θ, IsFiniteMeasure (P θ)] (h : IsSufficientStatistic P T)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {φ : X → F} (hφ : StronglyMeasurable φ) (hφ_int : ∀ θ, Integrable φ (P θ)) :
    ∃ ψ : S → F, StronglyMeasurable ψ ∧ ∀ θ, (P θ)[φ | mS.comap T] =ᵐ[P θ] ψ ∘ T := by
  obtain ⟨hT, K, hKm, hK⟩ := h
  refine ⟨fun s ↦ ∫ y, φ y ∂K s, hφ.integral_kernel, fun θ ↦ ?_⟩
  exact condExp_ae_eq_integral_of_map_prod_eq_compProd hT (hK θ) (hφ_int θ)

end IsSufficientStatistic

/-- Post-composing with a measurable equivalence preserves and reflects sufficiency. -/
@[simp]
theorem isSufficientStatistic_comp_measurableEquiv_iff [∀ θ, SFinite (P θ)] (e : S ≃ᵐ S') :
    IsSufficientStatistic P (e ∘ T) ↔ IsSufficientStatistic P T :=
  ⟨fun h ↦ by
    have he : e.symm ∘ (e ∘ T) = T := by ext x; simp
    exact he ▸ h.comp_measurableEquiv e.symm,
    fun h ↦ h.comp_measurableEquiv e⟩

/-- The identity map is sufficient for every family of s-finite measures. -/
theorem isSufficientStatistic_id (P : Θ → Measure X) [∀ θ, SFinite (P θ)] :
    IsSufficientStatistic P (id : X → X) := by
  refine ⟨measurable_id, Kernel.id, inferInstance, fun θ ↦ ?_⟩
  rw [Measure.map_id, Measure.compProd_id]
  rfl

/-- For a nonempty family of probability measures, a constant statistic is sufficient iff the family
consists of a single law. -/
theorem isSufficientStatistic_const_iff [Nonempty Θ] (P : Θ → Measure X)
    [∀ θ, IsProbabilityMeasure (P θ)] (s₀ : S) :
    IsSufficientStatistic P (fun _ : X ↦ s₀) ↔ ∀ θ₁ θ₂, P θ₁ = P θ₂ := by
  constructor
  · rintro ⟨-, K, hKm, hK⟩ θ₁ θ₂
    have hP : ∀ θ, P θ = K s₀ := fun θ ↦ by
      have h := comp_map_eq_of_map_prod_eq_compProd measurable_const (hK θ)
      rw [Measure.map_const, measure_univ, one_smul, Measure.dirac_bind K.measurable] at h
      exact h.symm
    rw [hP θ₁, hP θ₂]
  · intro hconst
    obtain ⟨θ₀⟩ := ‹Nonempty Θ›
    refine ⟨measurable_const, Kernel.const S (P θ₀), inferInstance, fun θ ↦ ?_⟩
    have hθ : P θ = P θ₀ := hconst θ θ₀
    have hprod : Measurable fun x : X ↦ (s₀, x) := measurable_const.prodMk measurable_id
    rw [hθ, Measure.map_const, measure_univ, one_smul]
    ext A hA
    rw [Measure.map_apply hprod hA, Measure.compProd_apply hA,
      lintegral_dirac' s₀ (Kernel.measurable_kernel_prodMk_left hA)]
    simp only [Kernel.const_apply]

/-- If a measurable family of rational functions `F : S → ℚ → ℝ` agrees at a point `s` with the
cumulative distribution function of a probability measure `ν` on `ℝ` at every rational number, then
the Stieltjes measure constructed by `stieltjesOfMeasurableRat F hF s` equals `ν`. -/
theorem measure_stieltjesOfMeasurableRat_eq_of_forall_eq_cdf
    {F : S → ℚ → ℝ} (hF : Measurable F) {s : S}
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hs : ∀ q : ℚ, F s q = cdf ν (q : ℝ)) :
    (stieltjesOfMeasurableRat F hF s).measure = ν := by
  have hpt : IsRatStieltjesPoint F s := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro q₁ q₂ hq
      rw [hs q₁, hs q₂]
      exact monotone_cdf ν (by exact_mod_cast hq)
    · have heq : F s = fun q : ℚ ↦ cdf ν (q : ℝ) := funext hs
      rw [heq]
      exact (tendsto_cdf_atTop ν).comp (tendsto_ratCast_atTop_iff.mpr tendsto_id)
    · have heq : F s = fun q : ℚ ↦ cdf ν (q : ℝ) := funext hs
      rw [heq]
      exact (tendsto_cdf_atBot ν).comp (tendsto_ratCast_atBot_iff.mpr tendsto_id)
    · intro t
      rw [hs t, ← StieltjesFunction.iInf_rat_gt_eq (cdf ν) (t : ℝ)]
      refine Equiv.iInf_congr
        { toFun := fun r : Ioi t ↦ ⟨r.1, by exact_mod_cast r.2⟩
          invFun := fun r : {r' : ℚ // (t : ℝ) < r'} ↦ ⟨r.1, by exact_mod_cast r.2⟩ } ?_
      intro r
      exact (hs r.1).symm
  have hst : stieltjesOfMeasurableRat F hF s = cdf ν := by
    ext x
    rw [← StieltjesFunction.iInf_rat_gt_eq (stieltjesOfMeasurableRat F hF s) x,
      ← StieltjesFunction.iInf_rat_gt_eq (cdf ν) x]
    congr 1 with r
    rw [stieltjesOfMeasurableRat_eq hF s r.1, toRatCDF_of_isRatStieltjesPoint hpt r.1, hs r.1]
  rw [hst, measure_cdf]

/-- Backward direction of the conditional-expectation characterization of sufficiency (indicator
form): on a nonempty standard Borel space, if every measurable set admits a parameter-free version
of its conditional probability given `mS.comap T`, then `T` is sufficient. -/
theorem isSufficientStatistic_of_forall_exists_condExp_indicator_ae_eq
    [StandardBorelSpace X] [Nonempty X]
    (P : Θ → Measure X) [∀ θ, IsFiniteMeasure (P θ)] {T : X → S} (hT : Measurable T)
    (hcond : ∀ A : Set X, MeasurableSet A →
      ∃ ψ : S → ℝ, Measurable ψ ∧ ∀ θ, (P θ)[A.indicator (1 : X → ℝ) | mS.comap T] =ᵐ[P θ] ψ ∘ T) :
    IsSufficientStatistic P T := by
  let e : X → ℝ := embeddingReal X
  have he : MeasurableEmbedding e := measurableEmbedding_embeddingReal X
  have hex : ∀ q : ℚ, ∃ ψ : S → ℝ, Measurable ψ ∧
      ∀ θ, (P θ)[(e ⁻¹' Iic (q : ℝ)).indicator (1 : X → ℝ) | mS.comap T] =ᵐ[P θ] ψ ∘ T :=
    fun q ↦ hcond (e ⁻¹' Iic (q : ℝ)) (he.measurable measurableSet_Iic)
  choose ψ hψ_meas hψ_eq using hex
  let F : S → ℚ → ℝ := fun s q ↦ ψ q s
  have hF_meas : Measurable F := measurable_pi_iff.mpr hψ_meas
  let η : Kernel S ℝ :=
    Kernel.mk (fun s ↦ (stieltjesOfMeasurableRat F hF_meas s).measure)
      (measurable_measure_stieltjesOfMeasurableRat hF_meas)
  have : IsMarkovKernel η := ⟨fun s ↦ instIsProbabilityMeasure_stieltjesOfMeasurableRat hF_meas s⟩
  let K : Kernel S X := Kernel.borelMarkovFromReal X η
  refine ⟨hT, K, inferInstance, fun θ ↦ ?_⟩
  let κ : Kernel S ℝ := condDistrib e T (P θ)
  let μK : Kernel S X := condDistrib id T (P θ)
  have hagree_q : ∀ q : ℚ, ∀ᵐ s ∂(P θ).map T, F s q = cdf (κ s) (q : ℝ) := by
    intro q
    have hce : (fun x ↦ (κ (T x)).real (Iic (q : ℝ))) =ᵐ[P θ]
        (P θ)[(e ⁻¹' Iic (q : ℝ)).indicator (1 : X → ℝ) | mS.comap T] :=
      condDistrib_ae_eq_condExp hT he.measurable measurableSet_Iic
    have hae_x : ∀ᵐ x ∂P θ, F (T x) q = cdf (κ (T x)) (q : ℝ) := by
      filter_upwards [hce, hψ_eq q θ] with x hx1 hx2
      rw [cdf_eq_real]
      exact (hx1.trans hx2).symm
    have hcdf_meas : Measurable fun s ↦ cdf (κ s) (q : ℝ) := by
      have : (fun s ↦ cdf (κ s) (q : ℝ)) = fun s ↦ (κ s).real (Iic (q : ℝ)) :=
        funext fun s ↦ cdf_eq_real (κ s) (q : ℝ)
      rw [this]
      exact (Kernel.measurable_coe κ measurableSet_Iic).ennreal_toReal
    exact (ae_map_iff hT.aemeasurable (measurableSet_eq_fun (hψ_meas q) hcdf_meas)).mpr hae_x
  have hη_eq : η =ᵐ[(P θ).map T] κ := by
    filter_upwards [ae_all_iff.mpr hagree_q] with s hs
    exact measure_stieltjesOfMeasurableRat_eq_of_forall_eq_cdf hF_meas hs
  have hcomp : κ =ᵐ[(P θ).map T] μK.map e :=
    condDistrib_comp hT.aemeasurable aemeasurable_id he.measurable
  have hK_eq : μK =ᵐ[(P θ).map T] K := by
    filter_upwards [hη_eq, hcomp] with s hsη hsc
    rw [Kernel.map_apply _ he.measurable] at hsc
    have hs_map : η s = (μK s).map e := hsη.trans hsc
    have hcompl : η s (range e)ᶜ = 0 := by
      rw [hs_map, Measure.map_apply he.measurable he.measurableSet_range.compl]
      simp
    have hKs : K s = (η s).comap e := by
      rw [Kernel.borelMarkovFromReal_apply, ite_eq_left hcompl]
    rw [hKs, hs_map, he.comap_map]
  exact (condDistrib_ae_eq_iff_measure_eq_compProd hT.aemeasurable aemeasurable_id K).mp hK_eq

/-- **Conditional-expectation characterization of sufficiency** (Pfanzagl, Corollary 1.3.11):
on a nonempty standard Borel space, a measurable statistic `T` is sufficient for a family of
finite measures `P` iff every bounded measurable real function admits a parameter-free measurable
version of its conditional expectation given `mS.comap T`. -/
theorem isSufficientStatistic_iff_forall_exists_condExp_ae_eq
    [StandardBorelSpace X] [Nonempty X]
    (P : Θ → Measure X) [∀ θ, IsFiniteMeasure (P θ)] {T : X → S} (hT : Measurable T) :
    IsSufficientStatistic P T ↔
      ∀ φ : X → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
        ∃ ψ : S → ℝ, Measurable ψ ∧ ∀ θ, (P θ)[φ | mS.comap T] =ᵐ[P θ] ψ ∘ T := by
  constructor
  · rintro hTsuff φ hφ ⟨C, hC⟩
    obtain ⟨ψ, hψ, hψ_eq⟩ := hTsuff.exists_condExp_ae_eq hφ.stronglyMeasurable fun θ ↦
      Integrable.of_bound hφ.aestronglyMeasurable C (ae_of_all _ fun x ↦ by simpa using hC x)
    exact ⟨ψ, hψ.measurable, hψ_eq⟩
  · intro hcond
    refine isSufficientStatistic_of_forall_exists_condExp_indicator_ae_eq P hT fun A hA ↦
      hcond (A.indicator 1) (measurable_const.indicator hA) ⟨1, fun x ↦ ?_⟩
    by_cases hx : x ∈ A <;> simp [hx]

end Sufficiency

section MinimalSufficiency

universe uX

variable {Θ S S₁ : Type*} {X : Type uX} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace S₁] {P : Θ → Measure X} {T : X → S}

/-- `IsMinimalSufficientStatistic P T` says that `T` is sufficient for `P` and factors almost
everywhere through every other sufficient statistic `U : X → S'` (with `S'` in the universe of `X`)
via a measurable map `φ` independent of the parameter. -/
def IsMinimalSufficientStatistic (P : Θ → Measure X) (T : X → S) : Prop :=
  IsSufficientStatistic P T ∧ ∀ (S' : Type uX) [MeasurableSpace S'] (U : X → S'),
    IsSufficientStatistic P U → ∃ φ : S' → S, Measurable φ ∧ ∀ θ, T =ᵐ[P θ] φ ∘ U

/-- Unfolding characterization of `IsMinimalSufficientStatistic`. -/
theorem isMinimalSufficientStatistic_iff :
    IsMinimalSufficientStatistic P T ↔
      IsSufficientStatistic P T ∧ ∀ (S' : Type uX) [MeasurableSpace S'] (U : X → S'),
        IsSufficientStatistic P U → ∃ φ : S' → S, Measurable φ ∧ ∀ θ, T =ᵐ[P θ] φ ∘ U :=
  (Iff.rfl)

namespace IsMinimalSufficientStatistic

/-- Every minimal sufficient statistic is sufficient. -/
theorem isSufficientStatistic (h : IsMinimalSufficientStatistic P T) :
    IsSufficientStatistic P T :=
  h.1

/-- Every minimal sufficient statistic is measurable. -/
theorem measurable (h : IsMinimalSufficientStatistic P T) : Measurable T :=
  h.1.measurable

/-- A minimal sufficient statistic factors almost everywhere through every sufficient statistic
whose codomain lives in the universe of `X`. -/
theorem exists_measurable_ae_eq (h : IsMinimalSufficientStatistic P T)
    {S' : Type uX} [MeasurableSpace S'] {U : X → S'} (hU : IsSufficientStatistic P U) :
    ∃ φ : S' → S, Measurable φ ∧ ∀ θ, T =ᵐ[P θ] φ ∘ U :=
  h.2 S' U hU

/-- A minimal sufficient statistic factors almost everywhere through any sufficient statistic whose
codomain is `Small` relative to `X` (in particular any `S' : Type`). -/
theorem exists_measurable_ae_eq_of_small [∀ θ, SFinite (P θ)]
    (h : IsMinimalSufficientStatistic P T) {S' : Type*} [MeasurableSpace S'] [Small.{uX} S']
    {U : X → S'} (hU : IsSufficientStatistic P U) :
    ∃ φ : S' → S, Measurable φ ∧ ∀ θ, T =ᵐ[P θ] φ ∘ U := by
  let _ : MeasurableSpace (Shrink.{uX} S') := MeasurableSpace.map (equivShrink S') ‹_›
  let e : S' ≃ᵐ Shrink.{uX} S' :=
    { toEquiv := equivShrink S'
      measurable_toFun := fun _ hs ↦ hs
      measurable_invFun := fun _ ht ↦ by
        rwa [MeasurableSpace.map_def, ← Set.preimage_comp,
          Equiv.symm_comp_self, Set.preimage_id] }
  obtain ⟨φ, hφ, hφ_eq⟩ := h.exists_measurable_ae_eq (hU.comp_measurableEquiv e)
  exact ⟨φ ∘ e, hφ.comp e.measurable, hφ_eq⟩

/-- Post-composing a minimal sufficient statistic with a measurable equivalence preserves minimal
sufficiency. -/
theorem comp_measurableEquiv [∀ θ, SFinite (P θ)] (h : IsMinimalSufficientStatistic P T)
    (e : S ≃ᵐ S₁) : IsMinimalSufficientStatistic P (e ∘ T) := by
  refine ⟨h.1.comp_measurableEquiv e, fun S' _ U hU ↦ ?_⟩
  obtain ⟨φ, hφ, hφ_eq⟩ := h.exists_measurable_ae_eq hU
  refine ⟨e ∘ φ, e.measurable.comp hφ, fun θ ↦ ?_⟩
  filter_upwards [hφ_eq θ] with x hx
  simp [hx]

end IsMinimalSufficientStatistic

/-- Post-composing with a measurable equivalence preserves and reflects minimal sufficiency. -/
@[simp]
theorem isMinimalSufficientStatistic_comp_measurableEquiv_iff [∀ θ, SFinite (P θ)]
    (e : S ≃ᵐ S₁) :
    IsMinimalSufficientStatistic P (e ∘ T) ↔ IsMinimalSufficientStatistic P T :=
  ⟨fun h ↦ by
    have he : e.symm ∘ (e ∘ T) = T := by ext x; simp
    exact he ▸ h.comp_measurableEquiv e.symm,
    fun h ↦ h.comp_measurableEquiv e⟩

/-- For a nonempty family consisting of a single probability law, any constant statistic is minimal
sufficient. -/
theorem isMinimalSufficientStatistic_const_of_forall_eq [Nonempty Θ] (P : Θ → Measure X)
    [∀ θ, IsProbabilityMeasure (P θ)] (hconst : ∀ θ₁ θ₂, P θ₁ = P θ₂) (s₀ : S) :
    IsMinimalSufficientStatistic P (fun _ : X ↦ s₀) := by
  refine ⟨(isSufficientStatistic_const_iff P s₀).mpr hconst, fun S' _ U _ ↦ ?_⟩
  exact ⟨fun _ ↦ s₀, measurable_const, fun _ ↦ EventuallyEq.rfl⟩

end MinimalSufficiency

end TauCeti
