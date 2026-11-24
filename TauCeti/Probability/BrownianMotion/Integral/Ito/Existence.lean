/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Localization
import all TauCeti.Probability.BrownianMotion.Integral.Ito.Localization
import TauCeti.Probability.Martingale.Local.Version
import TauCeti.Probability.Process.TimeAverage

/-!
# Existence of the continuous-time Brownian Itô integral

For a filtration-relative Brownian motion `W` with almost surely continuous paths and a locally
square-integrable predictable integrand `H` (`TauCeti.LocallyBrownianIntegrable ℱ P H`), this file
proves existence and local-martingale regularity for `TauCeti.Probability.IsItoIntegral` on the
original raw filtration. Basic algebraic closure properties and uniqueness belong to
`TauCeti.Probability.BrownianMotion.Integral.Ito.Basic`, global `BrownianIntegrable`
comparisons, Itô isometries, and true martingale properties belong to
`TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry`, shared localized stage construction
belongs to `TauCeti.Probability.BrownianMotion.Integral.Ito.Localization`, optional stopping and
local congruence belong to `TauCeti.Probability.BrownianMotion.Integral.Ito.Stopping`, and
deterministic-time measurable multiplier laws belong to
`TauCeti.Probability.BrownianMotion.Integral.Ito.Locality`.

Existence (`exists_isItoIntegral`) localizes `H` along closed-level hits of
`TauCeti.nnvolume.energyLocalizer`, patches continuous martingale stages without enlarging the
filtration, then upgrades the patched local martingale to an indistinguishable strongly predictable
version. For strongly progressive integrands with finite
pathwise square energy on every finite horizon, `exists_isItoIntegral_of_isStronglyProgressive`
extracts a predictable representative agreeing `(timeMeasure T).prod P`-almost everywhere and an
Itô integral unique up to indistinguishability among all predictable representatives. Every strongly
progressive `IsItoIntegral` is a native local martingale (`locally_martingale_of_isItoIntegral`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D, §3.3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W H I : ℝ≥0 → Ω → ℝ}

/-- **Existence of the continuous-time Brownian Itô integral.** For a filtration-relative Brownian
motion `W` with almost surely continuous paths and a `LocallyBrownianIntegrable` integrand `H`,
there exists a strongly predictable native local martingale `I` on the original raw filtration
satisfying `IsItoIntegral ℱ P W H I`. -/
theorem exists_isItoIntegral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ I ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ I P ∧
      IsItoIntegral ℱ P W H I := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨X, _, _, hX_cont, hX_loc, hX_ito, _⟩ :=
    hW.exists_patched_energyLocalizer_process hcont hH
  obtain ⟨I, hI_pred, hIX, hI_loc⟩ :=
    hX_loc.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hX_cont.mono fun _ hc _ ↦ hc.continuousWithinAt)
  exact ⟨I, hI_pred, hI_loc, hX_ito.congr hIX.symm⟩

/-- **Existence of the continuous-time Brownian Itô integral for strongly progressive
integrands.** Against a filtration-relative Brownian motion `W` with almost surely continuous paths,
any strongly progressive integrand `H` with almost surely finite pathwise square energy on every
finite horizon admits a strongly predictable representative `G` agreeing with `H`
`(timeMeasure T).prod P`-almost everywhere on every horizon, together with a strongly predictable
native local martingale `I` satisfying `IsItoIntegral ℱ P W G I`. Any other predictable integrand
`G'` agreeing with `H` `(timeMeasure T).prod P`-almost everywhere on every horizon yields an Itô
integral indistinguishable from `I`. -/
theorem exists_isItoIntegral_of_isStronglyProgressive
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : IsStronglyProgressive ℱ H)
    (hH_mem : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, MemLp (fun t ↦ H t ω) 2
      ((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ))) :
    ∃ G I : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ G ∧
      (∀ T : ℝ≥0, Function.uncurry G =ᵐ[(timeMeasure T).prod P] Function.uncurry H) ∧
      IsStronglyPredictable ℱ I ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ I P ∧
      IsItoIntegral ℱ P W G I ∧
      ∀ ⦃G' I' : ℝ≥0 → Ω → ℝ⦄,
        (∀ T : ℝ≥0, Function.uncurry G' =ᵐ[(timeMeasure T).prod P] Function.uncurry H) →
        IsItoIntegral ℱ P W G' I' → I ≡ᵐ[P] I' := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨G, hG_pred, hGH_real⟩ := hH.exists_isStronglyPredictable_ae_prod P
  have hGH (T : ℝ≥0) : Function.uncurry G =ᵐ[(timeMeasure T).prod P] Function.uncurry H := by
    have hcomp := ((measurePreserving_coe_timeMeasure T).prod
      (MeasurePreserving.id P)).quasiMeasurePreserving.ae_eq_comp (hGH_real T)
    simpa only [Function.comp_def, Prod.map, id_eq, Real.toNNReal_coe,
      Function.uncurry_def] using hcomp
  have hG_loc : LocallyBrownianIntegrable ℱ P G := by
    refine locallyBrownianIntegrable_iff_nat.mpr ⟨hG_pred, fun n ↦ ?_⟩
    have heq' : ∀ᵐ ω ∂P, (fun t ↦ G t ω) =ᵐ[timeMeasure n] (fun t ↦ H t ω) :=
      Measure.ae_ae_of_ae_prod
        ((Measure.measurePreserving_swap (μ := P)
          (ν := timeMeasure n)).quasiMeasurePreserving.ae_eq_comp (hGH n))
    filter_upwards [hH_mem, heq'] with ω hω heqω
    have hω' := hω n
    rw [NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def] at hω'
    rw [← NNReal.coe_natCast n, NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def]
    exact hω'.ae_eq heqω.symm
  obtain ⟨I, hI_pred, hI_loc, hI_ito⟩ := hW.exists_isItoIntegral hcont hG_loc
  refine ⟨G, I, hG_pred, hGH, hI_pred, hI_loc, hI_ito, fun G' I' hG'H hI' ↦ ?_⟩
  exact isItoIntegral_indist_of_ae_eq hW hI_ito hI' fun T ↦ (hGH T).trans (hG'H T).symm

/-- **Local-martingale property of the Brownian Itô integral.** Any strongly progressive process
satisfying `IsItoIntegral` is a native local martingale on the original raw filtration. -/
theorem locally_martingale_of_isItoIntegral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI_prog : IsStronglyProgressive ℱ I) (hI : IsItoIntegral ℱ P W H I) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ I P := by
  obtain ⟨J, _, hJ_loc, hJ_ito⟩ := hW.exists_isItoIntegral hcont hI.locallyBrownianIntegrable
  exact hI_prog.locally_martingale_of_indist hJ_loc (isItoIntegral_unique hW hJ_ito hI)

end TauCeti.Probability.IsFilteredPreBrownianReal
