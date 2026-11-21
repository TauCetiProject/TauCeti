/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.LogGauge.Diffeomorph
public import TauCeti.Algebra.Module.ZLattice.Family.LogGauge.Twist

/-!
# Representative-change comparison for the logarithmic gauge

Replacing the lattice representative `l : Λ` by `l + m • μ` (`μ : Λ`) leaves the normalized pure
translation action `TauCeti.logTranslationMulAction` and the cyclic quotient `Q = X / C_m`
unchanged (`TauCeti.logTranslationMulAction_add_nsmul`,
`TauCeti.logTranslationQuotientAddNsmulEquiv`,
`TauCeti.logTranslationQuotientAddNsmulDiffeomorph`), and changes the logarithmic gauge by
postcomposing with the logarithmic twist for `-μ` (`TauCeti.torusFamilyLogTwistMap` with
coordinate `φ = Subtype.val` on `Metric.ball 0 (r ^ m)`).

## Main results

* `TauCeti.torusFamilyLogGauge_add_nsmul`: upstairs comparison for `torusFamilyLogGauge` over
  `z ≠ 0`.
* `TauCeti.torusFamilyLogGaugeEquiv_add_nsmul`: comparison for the punctured equivalence
  `torusFamilyLogGaugeEquiv`.
* `TauCeti.torusFamilyLogGaugeDiffeomorph_add_nsmul`: comparison for the downstairs `C^n` (and
  holomorphic) diffeomorphism `torusFamilyLogGaugeDiffeomorph`.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, and A. Van de Ven, *Compact Complex Surfaces*, 2nd ed.,
  Springer, 2004, Ch. V, §13 (logarithmic transformations of torus families).
* K. Kodaira, *On compact analytic surfaces III*, Ann. of Math. **78** (1963), 1–40, §11.
-/

public section

open Complex Real MulAction TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

section EquivalenceComparison

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E] [Module ℂ E]
  (P : Metric.ball (0 : ℂ) (r ^ m) → Λ →ₗ[ℤ] E)

/-- Upstairs, replacing the period representative `l` by `l + m • μ` postcomposes the logarithmic
gauge with the logarithmic twist for `-μ` over `z ≠ 0`. -/
theorem torusFamilyLogGauge_add_nsmul (l μ : Λ)
    {x : letI := periodAddAction (powPullbackPeriod m r P)
      AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)}
    (hx : ((torusFamilyProjection (powPullbackPeriod m r P) x : rootsOfUnityBall m r) : ℂ) ≠ 0) :
    torusFamilyLogGauge P (l + m • μ) x =
      torusFamilyLogTwistMap Subtype.val P (-μ) (torusFamilyLogGauge P l x) := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  obtain ⟨⟨z, e⟩, rfl⟩ := Quotient.exists_rep x
  have hz : (z : ℂ) ≠ 0 := by rwa [torusFamilyProjection_mk] at hx
  have hexp : exp ((m : ℂ) * log (z : ℂ)) = (rootsOfUnityBall.powMap m r z : ℂ) := by
    rw [Complex.exp_natCast_mul, Complex.exp_log hz, rootsOfUnityBall.coe_powMap]
  rw [torusFamilyLogGauge_mk, torusFamilyLogGauge_mk,
    torusFamilyLogTwistMap_mk_of_exp_eq Subtype.val P (-μ) hexp]
  congr 2
  rw [map_add, map_nsmul, map_neg, smul_add, smul_neg, div_two_pi_I_smul_nsmul]
  abel

/-- Downstairs, replacing `l` by `l + m • μ` changes the logarithmic gauge equivalence `Q* ≃ Y*` by
postcomposing with the logarithmic twist for `-μ`. -/
theorem torusFamilyLogGaugeEquiv_add_nsmul (l μ : Λ) (hr : 0 ≤ r) :
    letI := periodAddAction (powPullbackPeriod m r P)
    torusFamilyLogGaugeEquiv P (l + m • μ) hr =
      ((logTranslationQuotientAddNsmulEquiv P l μ).subtypeEquiv fun q ↦ by
          rw [torusFamilyCyclicQuotientProjection_logTranslationQuotientAddNsmulEquiv]).trans
        ((torusFamilyLogGaugeEquiv P l hr).trans
          (torusFamilyLogTwistEquiv Subtype.val P (-μ))) := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  ext ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hx : ((torusFamilyProjection (powPullbackPeriod m r P) x :
      rootsOfUnityBall m r) : ℂ) ≠ 0 := fun h ↦
    hq (by rw [torusFamilyCyclicQuotientProjection_mk, h, zero_pow (NeZero.ne m)])
  simp only [Equiv.trans_apply, Equiv.subtypeEquiv_apply, coe_torusFamilyLogTwistEquiv,
    logTranslationQuotientAddNsmulEquiv_mk]
  rw [torusFamilyLogGaugeEquiv_mk P (l + m • μ) hr x, torusFamilyLogGaugeEquiv_mk P l hr x]
  exact torusFamilyLogGauge_add_nsmul P l μ hx

end EquivalenceComparison

section DiffeomorphComparison

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (P : Metric.ball (0 : ℂ) (r ^ m) → Λ →ₗ[ℤ] E)
  [∀ t, DiscreteTopology (LinearMap.range (P t))]
  [∀ t, IsZLattice ℝ (LinearMap.range (P t))]
  (hinj : ∀ t, Function.Injective (P t)) {n : ℕ∞ω}
  (hP : ∀ l, ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n fun t ↦ P t l)

/-- **Representative-change comparison for the downstairs logarithmic gauge.** Replacing `l` by
`l + m • μ` changes the downstairs `C^n` (or holomorphic) logarithmic gauge diffeomorphism
`Q* ≃ₘ^n Y*` by postcomposing with the logarithmic twist diffeomorphism for `-μ` (up to the
canonical identification of the two quotient manifolds). -/
theorem torusFamilyLogGaugeDiffeomorph_add_nsmul (l μ : Λ) (hr : 0 ≤ r)
    (hfree : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      IsCancelSMul (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
    letI := Opens.instChartedSpace (H := ModelProd ℂ E) (torusFamilyBallNonzeroOpens P)
    letI := periodAddAction (powPullbackPeriod m r P)
    letI : ChartedSpace (ModelProd ℂ E)
        (letI := logTranslationMulAction P (l + m • μ);
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) (l + m • μ)
        (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree)
    letI : ChartedSpace (ModelProd ℂ E)
        (letI := logTranslationMulAction P l;
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (logTranslationQuotientNonzeroOpens P (l + m • μ))
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (logTranslationQuotientNonzeroOpens P l)
    torusFamilyLogGaugeDiffeomorph P hP hinj (l + m • μ) hr
        (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree) =
      ((logTranslationQuotientAddNsmulDiffeomorph P hP hinj l μ hfree).subtype
          (U := logTranslationQuotientNonzeroOpens P (l + m • μ))
          (V := logTranslationQuotientNonzeroOpens P l) fun q ↦ by
            simp only [Opens.mem_mk, Set.mem_ofPred_eq, ← Diffeomorph.coe_toEquiv,
              logTranslationQuotientAddNsmulDiffeomorph_toEquiv,
              torusFamilyCyclicQuotientProjection_logTranslationQuotientAddNsmulEquiv]).trans
        ((torusFamilyLogGaugeDiffeomorph P hP hinj l hr hfree).trans
          (torusFamilyLogTwistDiffeomorph Subtype.val P hinj
            contMDiff_subtypeVal_ball hP (-μ))) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
  let _ := Opens.instChartedSpace (H := ModelProd ℂ E) (torusFamilyBallNonzeroOpens P)
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ : ChartedSpace (ModelProd ℂ E)
      (letI := logTranslationMulAction P (l + m • μ);
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
    logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) (l + m • μ)
      (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree)
  let _ : ChartedSpace (ModelProd ℂ E)
      (letI := logTranslationMulAction P l;
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
    logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  let _ := Opens.instChartedSpace (H := ModelProd ℂ E)
    (logTranslationQuotientNonzeroOpens P (l + m • μ))
  let _ := Opens.instChartedSpace (H := ModelProd ℂ E)
    (logTranslationQuotientNonzeroOpens P l)
  apply Diffeomorph.toEquiv_injective
  rw [torusFamilyLogGaugeDiffeomorph_toEquiv]
  refine (torusFamilyLogGaugeEquiv_add_nsmul P l μ hr).trans ?_
  exact (congrArg₂ Equiv.trans
    (by simp only [Diffeomorph.subtype_toEquiv, logTranslationQuotientAddNsmulDiffeomorph_toEquiv])
    (congrArg₂ Equiv.trans
      (torusFamilyLogGaugeDiffeomorph_toEquiv P hP hinj l hr hfree)
      (torusFamilyLogTwistDiffeomorph_toEquiv Subtype.val P hinj
        contMDiff_subtypeVal_ball hP (-μ)))).symm

end DiffeomorphComparison

end TauCeti
