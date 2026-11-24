/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Localization
import all TauCeti.Probability.BrownianMotion.Integral.Ito.Localization
import TauCeti.Probability.BrownianMotion.Integral.Stopping.Integral
import TauCeti.Probability.Process.Indistinguishable

/-!
# Optional stopping and localization for the Brownian Itô integral

For a filtration-relative Brownian motion `W` with almost surely continuous paths, stopping a
Brownian Itô integral `I` at any raw stopping time `σ` yields an Itô integral of `H` cut off to
the closed stochastic interval `⟦0, σ⟧` (`isItoIntegral_stoppedProcess`). Consequently:

* Restricting an integrand to `(σ, τ]` yields `stoppedProcess I τ - stoppedProcess I (σ ⊓ τ)`
  (`isItoIntegral_ite_Ioc`, `indist_stoppedProcess_sub_of_isItoIntegral_ite_Ioc`), simplifying to
  `stoppedProcess I τ - stoppedProcess I σ` when `σ ≤ τ`
  (`isItoIntegral_ite_Ioc_of_le`, `indist_stoppedProcess_sub_of_isItoIntegral_ite_Ioc_of_le`).
* Integrands agreeing product-almost-everywhere on `⟦0, σ⟧` over every finite horizon have
  indistinguishable stopped Itô integrals (`stoppedProcess_indist_of_isItoIntegral`).
* Stopping an Itô integral at `TauCeti.nnvolume.energyLocalizer H C` recovers the completed `L²`
  integral of the stopped finite-energy cutoff at every time `t`
  (`stoppedProcess_energyLocalizer_ae_eq_l2Integral`).

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
  {ℱ : Filtration ℝ≥0 mΩ} {W H K I J : ℝ≥0 → Ω → ℝ}

/-- **Optional stopping of the Brownian Itô integral.** Stopping an Itô integral at any raw
stopping time `σ` yields an Itô integral of `H` cut off to `⟦0, σ⟧`. -/
theorem isItoIntegral_stoppedProcess
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) :
    IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (stoppedProcess I σ) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hH : LocallyBrownianIntegrable ℱ P H := hI.locallyBrownianIntegrable
  obtain ⟨X, U, _, hX_cont, _, hX_ito, hUp, hUcont, hUae, hX_stop⟩ :=
    hW.exists_patched_energyLocalizer_process hcont hH
  let τ (k : ℕ) := TauCeti.nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)
  let hHstage (k : ℕ) :=
    (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P)
      ((k : ℝ≥0) + 1)).ite_le hσ
  have hUσ_ae (k : ℕ) (t : ℝ≥0) :
      stoppedProcess (U k) σ t =ᵐ[P] hW.l2Integral t ((hHstage k).toPredictableLp t) :=
    hW.stoppedProcess_ae_eq_l2Integral _ (hUp k).stronglyAdapted
      ((hUcont k).mono fun _ hc _ ↦ hc.continuousWithinAt) (hUae k) hσ t
  have hXσ_stop (k : ℕ) :
      stoppedProcess (stoppedProcess X σ) (τ k) ≡ᵐ[P] stoppedProcess (U k) σ := by
    rw [stoppedProcess_stoppedProcess, inf_comm, ← stoppedProcess_stoppedProcess]
    exact (hX_stop k).stoppedProcess σ
  have hXσ_ito : IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (stoppedProcess X σ) := by
    refine hW.isItoIntegral_of_localized_stages (hH.isStronglyPredictable.ite_le hσ)
      (hX_cont.mono fun _ hc ↦ hc.stoppedProcess)
      hH.isLocalizingSequence_energyLocalizer
      hHstage hUσ_ae hXσ_stop fun t ↦ ?_
    filter_upwards [hH.ae_accumulatedEnergy_lt_top] with ω hfin k hlt s hs
    have hle : (s : WithTop ℝ≥0) ≤ τ k ω := (WithTop.coe_le_coe.mpr (mem_Iic.mp hs)).trans hlt.le
    have hcut : TauCeti.nnvolume.finiteEnergyCutoff H s ω = H s ω :=
      TauCeti.nnvolume.finiteEnergyCutoff_eqOn (hfin t) hs
    dsimp only [τ] at hle ⊢
    rw [ite_eq_left hle, hcut]
  exact hXσ_ito.congr ((isItoIntegral_unique hW hX_ito hI).stoppedProcess σ)

/-- **Difference law on `(σ, τ]` for the Brownian Itô integral.** Restricting an integrand
to the half-open stochastic interval `(σ, τ]` corresponds to
`stoppedProcess I τ - stoppedProcess I (σ ⊓ τ)`, without requiring `σ ≤ τ`. -/
theorem isItoIntegral_ite_Ioc
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (fun t ω ↦ stoppedProcess I τ t ω - stoppedProcess I (σ ⊓ τ) t ω) := by
  convert (hW.isItoIntegral_stoppedProcess hcont hI hτ).sub
    (hW.isItoIntegral_stoppedProcess hcont hI (hσ.min hτ)) using 1
  ext t ω
  by_cases h1 : (t : WithTop ℝ≥0) ≤ σ ω <;> by_cases h2 : (t : WithTop ℝ≥0) ≤ τ ω
  · have hlt : ¬ (σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω) := fun h ↦ not_le_of_gt h.1 h1
    have hm : (t : WithTop ℝ≥0) ≤ min (σ ω) (τ ω) := le_min h1 h2
    rw [ite_eq_right hlt, ite_eq_left h2, ite_eq_left hm, sub_self]
  · have hlt : ¬ (σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω) := fun h ↦ h2 h.2
    have hm : ¬ (t : WithTop ℝ≥0) ≤ min (σ ω) (τ ω) := fun h ↦ h2 (h.trans (min_le_right _ _))
    rw [ite_eq_right hlt, ite_eq_right h2, ite_eq_right hm, sub_zero]
  · have hlt : σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω := ⟨not_le.mp h1, h2⟩
    have hm : ¬ (t : WithTop ℝ≥0) ≤ min (σ ω) (τ ω) := fun h ↦ h1 (h.trans (min_le_left _ _))
    rw [ite_eq_left hlt, ite_eq_left h2, ite_eq_right hm, sub_zero]
  · have hlt : ¬ (σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω) := fun h ↦ h2 h.2
    have hm : ¬ (t : WithTop ℝ≥0) ≤ min (σ ω) (τ ω) := fun h ↦ h2 (h.trans (min_le_right _ _))
    rw [ite_eq_right hlt, ite_eq_right h2, ite_eq_right hm, sub_zero]

/-- **Ordered difference law on `(σ, τ]` for the Brownian Itô integral.** When `σ ≤ τ`,
restricting an integrand to `(σ, τ]` corresponds to `stoppedProcess I τ - stoppedProcess I σ`. -/
theorem isItoIntegral_ite_Ioc_of_le
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) :
    IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (fun t ω ↦ stoppedProcess I τ t ω - stoppedProcess I σ t ω) := by
  simpa only [inf_of_le_left hστ] using hW.isItoIntegral_ite_Ioc hcont hI hσ hτ

/-- Indistinguishability form of `isItoIntegral_ite_Ioc`. -/
theorem indist_stoppedProcess_sub_of_isItoIntegral_ite_Ioc
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hJ : IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) J) :
    J ≡ᵐ[P] fun t ω ↦ stoppedProcess I τ t ω - stoppedProcess I (σ ⊓ τ) t ω :=
  isItoIntegral_unique hW hJ (hW.isItoIntegral_ite_Ioc hcont hI hσ hτ)

/-- Indistinguishability form of `isItoIntegral_ite_Ioc_of_le`. -/
theorem indist_stoppedProcess_sub_of_isItoIntegral_ite_Ioc_of_le
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ)
    (hJ : IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) J) :
    J ≡ᵐ[P] fun t ω ↦ stoppedProcess I τ t ω - stoppedProcess I σ t ω :=
  isItoIntegral_unique hW hJ (hW.isItoIntegral_ite_Ioc_of_le hcont hI hσ hτ hστ)

/-- **Local congruence of the Brownian Itô integral.** If two integrands agree
product-almost-everywhere on `⟦0, σ⟧` over every finite horizon for a raw stopping time `σ`,
their Itô integrals agree up to indistinguishability when stopped at `σ`. -/
theorem stoppedProcess_indist_of_isItoIntegral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ)
    (hHK : ∀ t : ℝ≥0,
      Function.uncurry (fun s : ℝ≥0 ↦ fun ω ↦ if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0) =ᵐ[
        (timeMeasure t).prod P]
      Function.uncurry (fun s : ℝ≥0 ↦ fun ω ↦ if (s : WithTop ℝ≥0) ≤ σ ω then K s ω else 0)) :
    stoppedProcess I σ ≡ᵐ[P] stoppedProcess J σ := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hIσ := (hW.isItoIntegral_stoppedProcess hcont hI hσ).congr_integrand
    (hJ.isStronglyPredictable.ite_le hσ) hHK
  exact isItoIntegral_unique hW hIσ (hW.isItoIntegral_stoppedProcess hcont hJ hσ)

/-- **Closed-level energy-stage identification for any Brownian Itô integral.** Stopping an Itô
integral at `TauCeti.nnvolume.energyLocalizer H C` identifies at each time `t` almost everywhere
with the completed `L²` integral of its stopped finite-energy cutoff. -/
theorem stoppedProcess_energyLocalizer_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I) (C t : ℝ≥0) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    stoppedProcess I (TauCeti.nnvolume.energyLocalizer H C) t =ᵐ[P]
      hW.l2Integral t ((hI.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer
        (P := P) C).toPredictableLp t) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hH : LocallyBrownianIntegrable ℱ P H := hI.locallyBrownianIntegrable
  let τ := TauCeti.nnvolume.energyLocalizer H C
  have hτ : IsStoppingTime ℱ τ :=
    hI.isStronglyPredictable.isStoppingTime_energyLocalizer TauCeti.nnvolume C
  let hHcut := hI.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P) C
  have hstop : IsItoIntegral ℱ P W
      (fun s ω ↦ if (s : WithTop ℝ≥0) ≤ τ ω then TauCeti.nnvolume.finiteEnergyCutoff H s ω else 0)
      (stoppedProcess I τ) := by
    refine (hW.isItoIntegral_stoppedProcess hcont hI hτ).congr_integrand
      hHcut.isStronglyPredictable fun u ↦ ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure u) (ν := P)).ae
        (ae_mem_Ioc_timeMeasure u),
      (Measure.quasiMeasurePreserving_snd (μ := timeMeasure u) (ν := P)).ae
        hH.ae_accumulatedEnergy_lt_top] with ⟨s, ω⟩ hs hfin
    by_cases hle : (s : WithTop ℝ≥0) ≤ τ ω
    · simp only [Function.uncurry_apply_pair, ite_eq_left hle]
      exact (TauCeti.nnvolume.finiteEnergyCutoff_eqOn (hfin u) hs.2).symm
    · simp only [Function.uncurry_apply_pair, ite_eq_right hle]
  exact hW.ae_eq_l2Integral_of_isItoIntegral hHcut hstop t

end TauCeti.Probability.IsFilteredPreBrownianReal
