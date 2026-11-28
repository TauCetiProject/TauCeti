/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Stopping
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Probability.BrownianMotion.Integral.Progressive
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Process.Stopping
import TauCeti.Topology.Instances.ENNReal

/-!
# Local-martingale property and localized Brownian Itô integration

`TauCeti.LocallyBrownianIntegrable ℱ P H` relaxes `TauCeti.BrownianIntegrable ℱ P H` to predictable
integrands with a.s. finite pathwise square energy on every finite horizon. Building on optional
stopping (`TauCeti.Probability.IsItoIntegral.stoppedProcess`, `stoppedProcess_indist`) and the
`L²` theory (`TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry`), this module establishes
the local-martingale property on a raw filtration
(`TauCeti.Probability.IsItoIntegral.locally_martingale`) for any filtered pre-Brownian motion
`W`, and `TauCeti.LocallyBrownianIntegrable.exists_isItoIntegral` constructs a strongly
progressive continuous local-martingale Itô integral whenever `W` has a.s. continuous paths.

## Main results

* `TauCeti.Probability.IsItoIntegral.locally_martingale`: strongly progressive continuous Itô
  integrals are native local martingales on the raw filtration.
* `TauCeti.LocallyBrownianIntegrable.exists_isItoIntegral`: existence of a strongly progressive
  continuous local-martingale Itô integral for `LocallyBrownianIntegrable` integrands.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H I J : ℝ≥0 → Ω → ℝ}

/-! ### Local-martingale property -/

namespace Probability.IsItoIntegral

private def energyStage (H : ℝ≥0 → Ω → ℝ) (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : WithTop ℝ≥0) ≤ nnvolume.energyLocalizer H ((k : ℝ≥0) + 1) ω then
    nnvolume.finiteEnergyCutoff H t ω else 0

/-- Every strongly progressive continuous Itô integral against a filtered pre-Brownian motion `W`
is a native local martingale on the raw filtration, without path continuity of `W` or moment
bounds. -/
theorem locally_martingale
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hprog : IsStronglyProgressive ℱ I) :
    Locally (fun X ↦ Martingale X ℱ P) ℱ I P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ (k : ℕ) := nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)
  have hτ_loc : IsLocalizingSequence ℱ τ P :=
    hI.locallyBrownianIntegrable.isLocalizingSequence_energyLocalizer
  have hHs (k : ℕ) : BrownianIntegrable ℱ P (energyStage H k) :=
    hI.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((k : ℝ≥0) + 1)
  have hmart (k : ℕ) : Martingale (MeasureTheory.stoppedProcess I (τ k)) ℱ P :=
    ((hI.stoppedProcess hW (hτ_loc.isStoppingTime k)).congr_integrand
      (hHs k).isStronglyPredictable fun T ↦ by
        filter_upwards [ae_mem_Ioc_timeMeasure_prod P T,
          (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T)
            (ν := P)).ae hI.locallyBrownianIntegrable.ae_accumulatedEnergy_lt_top] with p hpT hfin
        dsimp only [Function.uncurry, energyStage, τ]
        have hcut : nnvolume.finiteEnergyCutoff H p.1 p.2 = H p.1 p.2 :=
          nnvolume.finiteEnergyCutoff_eqOn (hfin T) hpT.2
        rw [hcut]).martingale hW (hHs k)
      (hprog.stoppedProcess (hτ_loc.isStoppingTime k)).stronglyAdapted
  refine hprog.locally_martingale_of_ae_stopped_eq hτ_loc hmart fun k _ ↦ .of_forall fun ω ↦ by
    rw [MeasureTheory.stoppedProcess_indicator_comm, indicator_of_mem]
    simpa only [Set.mem_ofPred_eq, ← WithTop.coe_bot, NNReal.bot_eq_zero, WithTop.coe_zero] using
      nnvolume.energyLocalizer_pos H (by positivity) ω

end Probability.IsItoIntegral

/-! ### Localized existence -/

private theorem tendsto_measure_lintegral_of_ae_eventually_eqOn [IsFiniteMeasure P]
    {L H_stage : ℕ → ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hL : ∀ k, IsStronglyPredictable ℱ (L k))
    (hHs : ∀ k, IsStronglyPredictable ℱ (H_stage k))
    (hH : IsStronglyPredictable ℱ H)
    (hstage : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖L k s ω - H_stage k s ω‖ₑ ^ 2 ∂Probability.timeMeasure T}) atTop (𝓝 0))
    (heq : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, EqOn (H_stage k · ω) (H · ω) (Iic T))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖L k s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure T}) atTop (𝓝 0) := by
  refine MeasureTheory.tendsto_measure_ge_of_ae_eventually_le
    (fun k ↦ IsStronglyPredictable.measurable_lintegral_enorm_sq
      (H := fun s ω ↦ L k s ω - H s ω) ((hL k).sub hH))
    (fun k ↦ IsStronglyPredictable.measurable_lintegral_enorm_sq
      (H := fun s ω ↦ L k s ω - H_stage k s ω) ((hL k).sub (hHs k)))
    (hstage ε hε) ?_
  filter_upwards [heq] with ω hω
  filter_upwards [hω] with k hk
  exact (lintegral_congr_ae ((Probability.ae_mem_Ioc_timeMeasure T).mono fun s hs ↦ by
    have hEq : H s ω = H_stage k s ω := (hk hs.2).symm; rw [hEq])).le

private theorem isItoIntegral_of_stopped_stages
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : IsStronglyPredictable ℱ H) (hI_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    {τ : ℕ → Ω → WithTop ℝ≥0} {H_stage U : ℕ → ℝ≥0 → Ω → ℝ}
    (hτ_top : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤))
    (hHs : ∀ k, BrownianIntegrable ℱ P (H_stage k))
    (hU : ∀ k, Probability.IsItoIntegral ℱ P W (H_stage k) (U k))
    (hI_stop : ∀ k T, MeasureTheory.stoppedProcess I (τ k) T =ᵐ[P] U k T)
    (heq : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ k in atTop, EqOn (H_stage k · ω) (H · ω) (Iic T)) :
    Probability.IsItoIntegral ℱ P W H I where
  isStronglyPredictable := hH
  ae_continuous := hI_cont
  exists_approx T := by
    let := (hW.hasLaw_eval 0).isProbabilityMeasure
    choose n γ a C _ hγ ha hb herr using fun k : ℕ ↦
      ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P T (hHs k).isStronglyPredictable
        ((hHs k).memLp_timeMeasure T) (ENNReal.inv_pos.mpr (by simp [ENNReal.natCast_ne_top] :
          ((k : ℝ≥0∞) + 1) ≠ ∞))
    have hl2_hold : Tendsto (fun k ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (γ k) (n k) (a k) p.1 p.2 - H_stage k p.1 p.2) 2
          ((Probability.timeMeasure T).prod P)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (ENNReal.tendsto_inv_natCast_add_nhds_zero 1)
        (fun _ ↦ zero_le) fun k ↦ (herr k).le
    have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
      MemLp.of_bound ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable (C k) (.of_forall (hb k j hj))
    have hl2_gain : Tendsto (fun k ↦ eLpNorm
        ((Finance.simpleGains (γ k) (n k) (a k) W T - U k T) - 0) 2 P) atTop (𝓝 0) :=
      hl2_hold.congr fun k ↦ by
        rw [sub_zero, ← (hU k).eLpNorm_simpleGains_sub_eq hW (hHs k)
          (hγ k).monotoneOn (ha k) (ha₂ k) T]
    refine ⟨n, γ, a, fun k ↦ (hγ k).monotoneOn, ha,
      tendsto_measure_lintegral_of_ae_eventually_eqOn
        (fun k ↦ Finance.isStronglyPredictable_simpleHolding (ha k))
        (fun k ↦ (hHs k).isStronglyPredictable) hH (fun _ hε ↦
          IsStronglyPredictable.tendsto_measure_lintegral_enorm_sub_sq_of_tendsto_eLpNorm
            (fun k ↦ Finance.isStronglyPredictable_simpleHolding (ha k))
            (fun k ↦ (hHs k).isStronglyPredictable) hl2_hold hε)
        (heq.mono fun _ hω ↦ hω T),
      ((tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hl2_gain).add
        (MeasureTheory.tendstoInMeasure_of_stoppedProcess_ae_eq hτ_top
          (fun k ↦ ((hU k).memLp hW (hHs k) T).aestronglyMeasurable) (fun k ↦ hI_stop k T))).congr
        (fun _ ↦ .of_forall fun _ ↦ sub_add_cancel _ _) (.of_forall fun _ ↦ zero_add _)⟩

/-- **Existence of the localized continuous Brownian Itô integral**: every
`LocallyBrownianIntegrable` integrand against an a.s. continuous filtered pre-Brownian motion `W`
admits a strongly progressive continuous local-martingale Itô integral on the raw filtration. -/
theorem LocallyBrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, Probability.IsItoIntegral ℱ P W H I ∧ IsStronglyProgressive ℱ I ∧
      Locally (fun X ↦ Martingale X ℱ P) ℱ I P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ (k : ℕ) := nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)
  have hτ_loc : IsLocalizingSequence ℱ τ P := hH.isLocalizingSequence_energyLocalizer
  have hHs (k : ℕ) : BrownianIntegrable ℱ P (Probability.IsItoIntegral.energyStage H k) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((k : ℝ≥0) + 1)
  choose U hU_ito hU_pred _ using fun k ↦ (hHs k).exists_isItoIntegral hW hcont
  have hcompat (k m : ℕ) (hkm : k ≤ m) : MeasureTheory.stoppedProcess (U m) (τ k) ≡ᵐ[P] U k := by
    have hcut : (fun (t : ℝ≥0) ω ↦ if (t : WithTop ℝ≥0) ≤ τ k ω then
        Probability.IsItoIntegral.energyStage H m t ω else 0) =
        Probability.IsItoIntegral.energyStage H k := by
      ext t ω; dsimp only [Probability.IsItoIntegral.energyStage, τ]
      have hmono := nnvolume.monotone_energyLocalizer H ω
        (add_le_add (Nat.cast_le.mpr hkm) (le_rfl : (1 : ℝ≥0) ≤ 1))
      split_ifs with h1 h2
      · rfl
      · exact (h2 (h1.trans hmono)).elim
      · rfl
    exact (hU_ito m).stoppedProcess_indist hW (hτ_loc.isStoppingTime k) (hcut ▸ hU_ito k)
  obtain ⟨I, hI_prog, hI_cont, hI_stop⟩ := exists_isStronglyProgressive_patch_stoppedProcess
    hτ_loc.tendsto_top (fun k ↦ (hU_pred k).isStronglyProgressive)
    (fun k ↦ (hU_ito k).ae_continuous) hcompat
  have hI_ito := isItoIntegral_of_stopped_stages hW hH.isStronglyPredictable hI_cont
    hτ_loc.tendsto_top hHs hU_ito (fun k T ↦ (hI_stop k).mono fun _ hω ↦ hω T)
    hH.ae_eventually_ite_le_energyLocalizer_eqOn
  exact ⟨I, hI_ito, hI_prog, hI_ito.locally_martingale hW hI_prog⟩

/-- **Existence of the continuous Brownian Itô integral for strongly progressive integrands**:
against an a.s. continuous filtered pre-Brownian motion `W`, any strongly progressive integrand `H`
with a.s. finite pathwise square energy on every integer horizon admits a predictable representative
`G` agreeing product-a.e. with `H` on every horizon and a strongly progressive continuous
local-martingale Itô integral `I`, unique up to indistinguishability among all predictable
representatives. -/
theorem _root_.MeasureTheory.IsStronglyProgressive.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : IsStronglyProgressive ℱ H)
    (henergy : ∀ n : ℕ, ∀ᵐ ω ∂P,
      (∫⁻ t, ‖H t ω‖ₑ ^ 2 ∂Probability.timeMeasure n) < ∞) :
    ∃ G I : ℝ≥0 → Ω → ℝ, LocallyBrownianIntegrable ℱ P G ∧
      (∀ T : ℝ≥0, Function.uncurry G =ᵐ[(Probability.timeMeasure T).prod P]
        Function.uncurry H) ∧
      Probability.IsItoIntegral ℱ P W G I ∧ IsStronglyProgressive ℱ I ∧
      Locally (fun X ↦ Martingale X ℱ P) ℱ I P ∧
      ∀ ⦃G' I' : ℝ≥0 → Ω → ℝ⦄,
        (∀ T : ℝ≥0, Function.uncurry G' =ᵐ[(Probability.timeMeasure T).prod P]
          Function.uncurry H) →
        Probability.IsItoIntegral ℱ P W G' I' → I ≡ᵐ[P] I' := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have henergy' (n : ℕ) : ∀ᵐ ω ∂P,
      (∫⁻ t, ‖H t ω‖ₑ ^ 2 ∂((volume.restrict (Ioc 0 (n : ℝ))).comap
        ((↑) : ℝ≥0 → ℝ))) < ∞ := by
    simpa only [← NNReal.coe_natCast n, NNReal.comap_volume_restrict_Ioc,
      ← Probability.timeMeasure_def] using henergy n
  obtain ⟨G, hG, hGH⟩ := hH.exists_locallyBrownianIntegrable_ae_prod henergy'
  have hGH' (T : ℝ≥0) : Function.uncurry G =ᵐ[(Probability.timeMeasure T).prod P]
      Function.uncurry H := by
    simpa only [NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def] using hGH T
  obtain ⟨I, hI_ito, hI_prog, hI_loc⟩ := hG.exists_isItoIntegral hW hcont
  refine ⟨G, I, hG, hGH', hI_ito, hI_prog, hI_loc, fun G' I' hG'H hI' ↦ ?_⟩
  exact hI_ito.indist_of_ae_eq hW (fun T ↦ (hGH' T).trans (hG'H T).symm) hI'

end TauCeti
