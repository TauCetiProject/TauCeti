/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.LogGauge.Basic
public import TauCeti.Analysis.Complex.RootsOfUnity.Manifold
public import TauCeti.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Regularity of the upstairs logarithmic gauge

`contMDiff_powPullbackPeriod` preserves `C^n` regularity over `𝓘(ℂ)` under pullback along the
power map. For a `C^n` varying period family, `contMDiffAt_torusFamilyLogGauge` proves `C^n`
regularity of the upstairs map `TauCeti.torusFamilyLogGauge` from
`(rootsOfUnityBall m r × E)/Λ` to `(Metric.ball 0 (r ^ m) × E)/Λ` off the central fibre
(`z ≠ 0`), hence holomorphy there when `n ≠ 0`. Although its formula uses the principal
logarithm, near any nonzero point it agrees modulo periods with a formula using a holomorphic
branch. No constancy of the period family is needed.

Both discs carry their inherited open-subset complex atlases. This is the upstairs regularity
step for descent to the punctured cyclic quotient, not a downstairs biholomorphism theorem for
`TauCeti.torusFamilyLogGaugeEquiv`.

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
  -- A branch centred at `z₀` is holomorphic even if `z₀` lies on the principal branch cut.
  let L : ℂ → ℂ := fun z ↦ log z₀ + log (z / z₀)
  have hL {z : ℂ} (hz : z ≠ 0) : exp (L z) = z := by
    simp only [L]
    rw [Complex.exp_add, exp_log hz₀, exp_log (div_ne_zero hz hz₀), mul_div_cancel₀ _ hz₀]
  have hLc : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ) n
      (fun p : rootsOfUnityBall m r × E ↦ L p.1) (z₀, e₀) := by
    apply contMDiffAt_const.add
    exact (Complex.contDiffAt_log (x := 1) one_mem_slitPlane).contMDiffAt.comp_of_eq
      ((contDiff_id.div_const (z₀ : ℂ)).contMDiff.comp
        (rootsOfUnityBall.contMDiff_val.comp contMDiff_fst)).contMDiffAt
      (by simp [hz₀])
  have hpow : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (rootsOfUnityBall.powMap m r) :=
    rootsOfUnityBall.contMDiff_powMap
  have hq := (isLocalDiffeomorph_torusFamily_mk P hinj hP).contMDiff
  have hs := hq.contMDiffAt.comp (z₀, e₀)
    ((hpow.comp contMDiff_fst).contMDiffAt.prodMk
      (contMDiffAt_snd.sub ((hLc.div_const (2 * π * I)).smul
        ((contMDiff_powPullbackPeriod P (hP l)).comp contMDiff_fst).contMDiffAt)))
  apply hs.congr_of_eventuallyEq
  have hopen : IsOpen {p : rootsOfUnityBall m r × E | (p.1 : ℂ) ≠ 0} :=
    isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const
  filter_upwards [hopen.mem_nhds hz₀] with p hp
  simpa [Function.comp_def, powPullbackPeriod_apply] using
    (torusFamilyLogGauge_mk_of_exp_eq P l (hL hp) p.2)

end TauCeti
