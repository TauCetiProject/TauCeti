/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.LogGauge.Basic
public import TauCeti.Analysis.Complex.RootsOfUnity.Manifold
public import TauCeti.Topology.MetricSpace.Pseudo.Lemmas
import TauCeti.Algebra.Module.ZLattice.Family.BaseChange.ContMDiff
import TauCeti.Algebra.Module.ZLattice.Family.LogGauge.Twist

/-!
# Regularity of the upstairs logarithmic gauge

`contMDiff_powPullbackPeriod` preserves `C^n` regularity over `𝓘(ℂ)` under pullback along the
power map, and the translation sections of the normalized pure translation action are `C^n`
(`contMDiff_logTranslationSection`). For a `C^n` varying period family,
`contMDiffAt_torusFamilyLogGauge` proves `C^n`
regularity of the upstairs map `TauCeti.torusFamilyLogGauge` from
`(rootsOfUnityBall m r × E)/Λ` to `(Metric.ball 0 (r ^ m) × E)/Λ` off the central fibre
(`z ≠ 0`), hence holomorphy there when `n ≠ 0`. Although its formula uses the principal
logarithm, near any nonzero point it agrees modulo periods with a formula using a holomorphic
branch. No constancy of the period family is needed.

Both discs carry their inherited open-subset complex atlases. This is the upstairs regularity
step for descent to the punctured cyclic quotient; the downstairs biholomorphism
`TauCeti.torusFamilyLogGaugeDiffeomorph` is built from it in
`TauCeti.Algebra.Module.ZLattice.Family.LogGauge.Diffeomorph`.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*,
  second edition, Chapter V, section on logarithmic transformations.
-/

public section

open Complex Filter Topology
open scoped Manifold ContDiff Real

namespace TauCeti

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (P : Metric.ball (0 : ℂ) (r ^ m) → Λ →ₗ[ℤ] E) {n : ℕ∞ω}

/-- Pullback along `rootsOfUnityBall.powMap` preserves `C^n` regularity of each period. -/
theorem contMDiff_powPullbackPeriod {l : Λ}
    (hP : ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n fun t ↦ P t l) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n fun z ↦ powPullbackPeriod m r P z l := by
  simpa only [powPullbackPeriod_apply, Function.comp_def] using
    hP.comp rootsOfUnityBall.contMDiff_powMap

variable (hP : ∀ l, ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n fun t ↦ P t l)
  [FiniteDimensional ℂ E]
  [∀ t, DiscreteTopology (LinearMap.range (P t))]
  [∀ t, IsZLattice ℝ (LinearMap.range (P t))]
  (hinj : ∀ t, Function.Injective (P t))

/-- The translation sections `z ↦ [ζ z, (log ζ / 2πi) • P (z ^ m) l]` of the normalized pure
translation action `TauCeti.logTranslationMulAction` are `C^n` maps from the disc to the pulled-back
family, hence holomorphic when `n ≠ 0`. -/
theorem contMDiff_logTranslationSection (l : Λ) (ζ : rootsOfUnity m ℂ) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, E)) n (logTranslationSection P l ζ) := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  rw [funext (logTranslationSection_eq_mk_of_exp_eq P l (exp_log (ζ : ℂˣ).ne_zero))]
  exact (isLocalDiffeomorph_torusFamily_mk (powPullbackPeriod m r P)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    (fun l ↦ contMDiff_powPullbackPeriod P (hP l))).contMDiff.comp
    ((contMDiff_const_smul ζ).prodMk
      ((contMDiff_const (I' := 𝓘(ℂ)) (c := log ((ζ : ℂˣ) : ℂ) / (2 * π * I))).smul
        (contMDiff_powPullbackPeriod P (hP l))))

/-- The upstairs map `torusFamilyLogGauge` from `(rootsOfUnityBall m r × E)/Λ` to
`(Metric.ball 0 (r ^ m) × E)/Λ` is `C^n` off the central fibre (`z ≠ 0`), hence holomorphic
there when `n ≠ 0`, including on the branch cut of the principal logarithm. -/
theorem contMDiffAt_torusFamilyLogGauge (l : Λ)
    {x : letI := periodAddAction (powPullbackPeriod m r P)
      AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)}
    (hx : ((torusFamilyProjection (powPullbackPeriod m r P) x : rootsOfUnityBall m r) : ℂ) ≠ 0) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n
      (torusFamilyLogGauge P l) x := by
  have haux : ∀ (Q : rootsOfUnityBall m r → Λ →ₗ[ℤ] E)
      (_ : Q = P ∘ rootsOfUnityBall.powMap m r)
      [∀ z, DiscreteTopology (LinearMap.range (Q z))]
      [∀ z, IsZLattice ℝ (LinearMap.range (Q z))]
      (hQinj : ∀ z, Function.Injective (Q z))
      (hQP : ∀ l', ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n fun z ↦ Q z l')
      (G : letI := periodAddAction Q; letI := periodAddAction P;
        AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E) →
          AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E))
      (_ : ∀ z e, (letI := periodAddAction Q; letI := periodAddAction P;
        G (Quotient.mk _ (z, e))) =
        (letI := periodAddAction P;
          Quotient.mk _ (rootsOfUnityBall.powMap m r z,
            e - (log (z : ℂ) / (2 * π * I)) • Q z l)))
      {y : letI := periodAddAction Q; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)},
      ((torusFamilyProjection Q y : rootsOfUnityBall m r) : ℂ) ≠ 0 →
        letI := periodAddAction P
        letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
        letI := periodAddAction Q
        letI := torusFamilyChartedSpace (H := ℂ) Q (fun l ↦ (hQP l).continuous) hQinj
        ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n G y := by
    intro Q hQ _ _ hQinj hQP G hG y hy
    subst hQ
    let _ := periodAddAction P
    let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    let _ := periodAddAction (P ∘ rootsOfUnityBall.powMap m r)
    let _ := torusFamilyChartedSpace (H := ℂ) (P ∘ rootsOfUnityBall.powMap m r)
      (fun l ↦ ((hP l).comp rootsOfUnityBall.contMDiff_powMap).continuous)
      (fun z ↦ hinj (rootsOfUnityBall.powMap m r z))
    have heq : G = torusFamilyBaseChangeMap P (rootsOfUnityBall.powMap m r) ∘
        ⇑(torusFamilyLogTwistMap Subtype.val (P ∘ rootsOfUnityBall.powMap m r) (-l)) := by
      funext w
      induction w using Quotient.inductionOn with
      | h p =>
        obtain ⟨z, e⟩ := p
        dsimp only [Function.comp_apply]
        rw [hG, torusFamilyLogTwistMap_mk, torusFamilyBaseChangeMap_mk]
        simp [sub_eq_add_neg]
    rw [heq]
    have hbc := contMDiff_torusFamilyBaseChangeMap P hinj hP (rootsOfUnityBall.powMap m r)
      rootsOfUnityBall.contMDiff_powMap
    have htw := contMDiffAt_torusFamilyLogTwistMap Subtype.val (P ∘ rootsOfUnityBall.powMap m r)
      (fun z ↦ hinj (rootsOfUnityBall.powMap m r z)) rootsOfUnityBall.contMDiff_val
      (fun l' ↦ (hP l').comp rootsOfUnityBall.contMDiff_powMap) (-l) hy
    exact (hbc _).comp y htw
  exact haux (powPullbackPeriod m r P) (powPullbackPeriod_eq_comp P)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    (fun l' ↦ contMDiff_powPullbackPeriod P (hP l'))
    (torusFamilyLogGauge P l)
    (fun z e ↦ by
      rw [torusFamilyLogGauge_mk, powPullbackPeriod_apply])
    hx

end TauCeti
