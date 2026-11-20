/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.LogGauge.Basic
public import TauCeti.Analysis.Complex.RootsOfUnity.Manifold
public import TauCeti.Topology.MetricSpace.Pseudo.Lemmas
import TauCeti.Analysis.SpecialFunctions.Pow.LocalRoot
import Mathlib.Geometry.Manifold.Algebra.Structures

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

When the normalized pure translation action is free, the cyclic quotient `Q = X / C_m` carries the
quotient atlas `TauCeti.logTranslationQuotientChartedSpace`, for which it is a `C^n` manifold
(`TauCeti.isManifold_logTranslationQuotient`).

Both discs carry their inherited open-subset complex atlases. This is the upstairs regularity
step for descent to the punctured cyclic quotient; the downstairs diffeomorphism
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
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  obtain ⟨⟨z₀, e₀⟩, rfl⟩ := Quotient.exists_rep x
  have hz₀ : (z₀ : ℂ) ≠ 0 := by rwa [torusFamilyProjection_mk] at hx
  rw [← (isLocalDiffeomorph_torusFamily_mk (powPullbackPeriod m r P)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    (fun l ↦ contMDiff_powPullbackPeriod P (hP l)) (z₀, e₀)).contMDiffAt_comp_iff le_rfl]
  -- A logarithm `L` centred at `z₀` is holomorphic even if `z₀` lies on the principal branch cut.
  obtain ⟨L, hL, hLex⟩ := exists_contDiffAt_exp_eq (n := n) hz₀
  have hLc : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ) n
      (fun p : rootsOfUnityBall m r × E ↦ L p.1) (z₀, e₀) :=
    hL.contMDiffAt.comp_of_eq
      (rootsOfUnityBall.contMDiff_val.comp contMDiff_fst).contMDiffAt rfl
  have hpow : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (rootsOfUnityBall.powMap m r) :=
    rootsOfUnityBall.contMDiff_powMap
  have hq := (isLocalDiffeomorph_torusFamily_mk P hinj hP).contMDiff
  have hs := hq.contMDiffAt.comp (z₀, e₀)
    ((hpow.comp contMDiff_fst).contMDiffAt.prodMk
      (contMDiffAt_snd.sub ((hLc.div_const (2 * π * I)).smul
        ((contMDiff_powPullbackPeriod P (hP l)).comp contMDiff_fst).contMDiffAt)))
  apply hs.congr_of_eventuallyEq
  filter_upwards [(continuous_subtypeVal.comp continuous_fst).continuousAt.eventually_ne hz₀]
    with p hp
  simpa [Function.comp_def, powPullbackPeriod_apply] using
    (torusFamilyLogGauge_mk_of_exp_eq P l (hLex _ hp) p.2)

/-! ### The atlas of the cyclic quotient -/

section CyclicQuotient

variable (l : Λ)
  (hfree : letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    IsCancelSMul (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))

/-- **The atlas of the cyclic quotient.** For continuous periods and a free normalized pure
translation action `TauCeti.logTranslationMulAction`, this is the quotient atlas
`TauCeti.torusFamilyAffineQuotientChartedSpace` on the cyclic quotient `Q = X / C_m`. -/
noncomputable abbrev logTranslationQuotientChartedSpace
    (hcont : ∀ l, Continuous fun t ↦ P t l) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    ChartedSpace (ModelProd ℂ E) (MulAction.orbitRel.Quotient (rootsOfUnity m ℂ)
      (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
  letI := periodAddAction (powPullbackPeriod m r P)
  letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l ↦ continuous_powPullbackPeriod P (hcont l))
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
    (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
    (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
    (fun l ↦ continuous_powPullbackPeriod P (hcont l)) (fun _ ↦ continuous_snd)
    (continuous_logTranslationSection P l (hcont l)) hfree

/-- For `C^n` periods and a free normalized pure translation action, the cyclic quotient
is a `C^n` manifold for `logTranslationQuotientChartedSpace`. -/
theorem isManifold_logTranslationQuotient :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj l hfree (fun l ↦ (hP l).continuous)
    IsManifold (𝓘(ℂ).prod 𝓘(ℂ, E)) n (MulAction.orbitRel.Quotient (rootsOfUnity m ℂ)
      (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
  isManifold_torusFamilyAffineQuotient (powPullbackPeriod m r P)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    (fun l ↦ contMDiff_powPullbackPeriod P (hP l)) (fun _ _ ↦ AddMonoidHom.id E)
    (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
    (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
    (fun _ ↦ contMDiff_snd) (contMDiff_logTranslationSection P hP hinj l) hfree

/-- The orbit map `X → Q` is a `C^n` local diffeomorphism for the quotient atlas. -/
theorem isLocalDiffeomorph_logTranslationQuotient_mk :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj l hfree (fun l ↦ (hP l).continuous)
    IsLocalDiffeomorph (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n
      (Quotient.mk (MulAction.orbitRel (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))) :=
  isLocalDiffeomorph_torusFamilyAffineQuotient_mk (powPullbackPeriod m r P)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    (fun l ↦ contMDiff_powPullbackPeriod P (hP l)) (fun _ _ ↦ AddMonoidHom.id E)
    (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
    (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
    (fun _ ↦ contMDiff_snd) (contMDiff_logTranslationSection P hP hinj l) hfree

end CyclicQuotient

end TauCeti
