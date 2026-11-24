/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry
import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
import TauCeti.Probability.BrownianMotion.Integral.Stopping.Integral
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.LocalProperty
import TauCeti.Probability.Process.Patching

/-!
# Localized stage construction for the Brownian Itô integral

This file provides the shared localization machinery underlying existence, optional stopping, and
event locality of the continuous-time Brownian Itô integral on the original raw filtration:

* `TauCeti.Probability.IsFilteredPreBrownianReal.isItoIntegral_of_localized_stages`: if an almost
  surely continuous process stopped along a localizing sequence matches `L²`-integral stages that
  agree with `H` before the stopping times, then it satisfies `IsItoIntegral`.

It also houses the internal `TauCeti.nnvolume.energyLocalizer` stage-patching construction shared
across the `Ito` submodules via `import all`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D, §3.3.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W H I : ℝ≥0 → Ω → ℝ}

/-- **Itô integral criterion from localized `L²` stages.** If an almost surely continuous process
`X` stopped along a localizing sequence `τ` is indistinguishable at each stage `k` from a process
`U k` representing `hW.l2Integral t ((hHstage k).toPredictableLp t)`, and each `Hstage k` agrees
with `H` on `[0, t]` whenever `t < τ k ω`, then `IsItoIntegral ℱ P W H X`. Combining this
criterion with `isItoIntegral_unique` establishes independence of the chosen localizer. -/
public theorem isItoIntegral_of_localized_stages
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : IsStronglyPredictable ℱ H)
    {X : ℝ≥0 → Ω → ℝ} (hX_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω))
    {τ : ℕ → Ω → WithTop ℝ≥0} (hloc : IsLocalizingSequence ℱ τ P)
    {Hstage : ℕ → ℝ≥0 → Ω → ℝ} (hHstage : ∀ k, BrownianIntegrable ℱ P (Hstage k))
    {U : ℕ → ℝ≥0 → Ω → ℝ}
    (hUae : ∀ k t, U k t =ᵐ[P] hW.l2Integral t ((hHstage k).toPredictableLp t))
    (hstop : ∀ k, stoppedProcess X (τ k) ≡ᵐ[P] U k)
    (hstage_eq : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ∀ k, (t : WithTop ℝ≥0) < τ k ω →
      EqOn (fun s ↦ Hstage k s ω) (fun s ↦ H s ω) (Iic t)) :
    IsItoIntegral ℱ P W H X where
  isStronglyPredictable := hH
  ae_continuous := hX_cont
  exists_approx t := by
    let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    choose n grid a _ _ hgrid ha _ ha₂ herr using fun k : ℕ ↦
      ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t (hHstage k).isStronglyPredictable
        ((hHstage k).memLp_timeMeasure t) (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (k + 1)))
    have herr_lim : Tendsto (fun k ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (grid k) (n k) (a k) p.1 p.2 - Hstage k p.1 p.2) 2
          ((timeMeasure t).prod P)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
        (fun _ ↦ bot_le) fun k ↦ (herr k).le
    refine ⟨n, grid, a, fun k ↦ (hgrid k).monotoneOn, ha, fun _ hε ↦
      hloc.tendsto_measure_of_ae_imp_of_lt t
        (MeasureTheory.tendsto_measure_le_lintegral_enorm_pow_of_tendsto_eLpNorm (n := 2)
          two_ne_zero
          (g := fun k p ↦ Finance.simpleHolding (grid k) (n k) (a k) p.1 p.2 - Hstage k p.1 p.2)
          (fun k ↦ (((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
            (hHstage k).isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
          (by simpa only [Nat.cast_ofNat] using herr_lim) hε)
        fun k ↦ (hstage_eq t).mono fun ω hgood hlt hω ↦ ?_,
      tendstoInMeasure_iff_norm.mpr fun ε hε ↦ ?_⟩
    · have heq_int : (∫⁻ s, ‖Finance.simpleHolding (grid k) (n k) (a k) s ω - Hstage k s ω‖ₑ ^ 2
          ∂timeMeasure t) =
        ∫⁻ s, ‖Finance.simpleHolding (grid k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t := by
        rw [timeMeasure_def]
        exact setLIntegral_congr_fun measurableSet_Ioc fun s hs ↦ by
          have hs_eq : Hstage k s ω = H s ω := hgood k hlt hs.2; rw [hs_eq]
      simpa only [mem_ofPred_eq, Pi.sub_apply, Function.uncurry_apply_pair, heq_int] using hω
    · have hG_stage : TendstoInMeasure P
          (fun k ω ↦ Finance.simpleGains (grid k) (n k) (a k) W t ω - U k t ω) atTop 0 := by
        refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
        simpa only [Pi.sub_def, sub_zero] using
          hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
            hHstage (fun k ↦ hUae k t) (fun k ↦ (hgrid k).monotoneOn) ha ha₂ herr_lim
      have hG_ε := (tendstoInMeasure_iff_norm.mp hG_stage) ε hε
      simp only [Pi.zero_apply, sub_zero] at hG_ε
      exact hloc.tendsto_measure_of_ae_imp_of_lt t hG_ε fun k ↦
        ((hstop k).ae_eq_eval t).mono fun ω heq_u hlt hω ↦ by
          simpa only [mem_ofPred_eq, ← heq_u, stoppedProcess_eq_of_le (u := X) hlt.le] using hω

/-- **Patched energy-localizer construction for the Brownian Itô integral.** Given an almost
surely continuous filtration-relative Brownian motion `W` and a `LocallyBrownianIntegrable`
integrand `H`, constructs a strongly progressive, almost surely continuous local martingale
`X` satisfying `IsItoIntegral ℱ P W H X`, together with the continuous predictable stage integrals
`U m` along the closed-level energy localizers `TauCeti.nnvolume.energyLocalizer H (m + 1)`. -/
theorem exists_patched_energyLocalizer_process
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    letI := (hW.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
    ∃ (X : ℝ≥0 → Ω → ℝ) (U : ℕ → ℝ≥0 → Ω → ℝ),
      IsStronglyProgressive ℱ X ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω)) ∧
      Locally (fun Z ↦ Martingale Z ℱ P) ℱ X P ∧
      IsItoIntegral ℱ P W H X ∧
      (∀ m, IsStronglyPredictable ℱ (U m)) ∧
      (∀ m, ∀ᵐ ω ∂P, Continuous (fun t ↦ U m t ω)) ∧
      (∀ m t, U m t =ᵐ[P] hW.l2Integral t
        ((hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer
          (P := P) ((m : ℝ≥0) + 1)).toPredictableLp t)) ∧
      ∀ m : ℕ, stoppedProcess X (TauCeti.nnvolume.energyLocalizer H ((m : ℝ≥0) + 1)) ≡ᵐ[P] U m := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let τ (m : ℕ) := TauCeti.nnvolume.energyLocalizer H ((m : ℝ≥0) + 1)
  have hloc := hH.isLocalizingSequence_energyLocalizer
  let hHstage (m : ℕ) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P) ((m : ℝ≥0) + 1)
  choose U hUp hUm hUcont hUae using fun m ↦ hW.exists_continuous_l2Integral hcont (hHstage m)
  have hcompat (n m : ℕ) (hnm : n ≤ m) : stoppedProcess (U m) (τ n) ≡ᵐ[P] U n := by
    refine TauCeti.indist_of_ae_continuous
      ((hUcont m).mono fun _ hc ↦ hc.stoppedProcess) (hUcont n) fun t ↦ ?_
    have hstop_ae := hW.stoppedProcess_ae_eq_l2Integral (hHstage m) (hUp m).stronglyAdapted
      ((hUcont m).mono fun _ hc _ ↦ hc.continuousWithinAt) (hUae m) (hloc.isStoppingTime n) t
    have hlp_eq : ((hHstage m).ite_le (hloc.isStoppingTime n)).toPredictableLp t =
        (hHstage n).toPredictableLp t := by
      refine (BrownianIntegrable.toPredictableLp_eq_iff _ _).mpr (.of_forall fun ⟨s, ω⟩ ↦ ?_)
      have hτ_le : τ n ω ≤ τ m ω := TauCeti.nnvolume.monotone_energyLocalizer H ω
        (add_le_add (Nat.cast_le.mpr hnm) le_rfl)
      dsimp only [Function.uncurry_apply_pair, τ] at *
      by_cases hs : (s : WithTop ℝ≥0) ≤ TauCeti.nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω
      · rw [ite_eq_left hs, ite_eq_left (hs.trans hτ_le), ite_eq_left hs]
      · rw [ite_eq_right hs, ite_eq_right hs]
    exact hstop_ae.trans (hlp_eq ▸ (hUae n t).symm)
  obtain ⟨X, hX_prog, hX_cont, hX_stop⟩ :=
    TauCeti.exists_isStronglyProgressive_patch_stoppedProcess hloc.tendsto_top
      (fun m ↦ (hUp m).isStronglyProgressive) hUcont hcompat
  have hX_loc : Locally (fun Z ↦ Martingale Z ℱ P) ℱ X P := by
    refine hX_prog.locally_martingale_of_ae_stopped_eq hloc hUm fun n t ↦ ?_
    have hX_ind : (fun s ↦ {ω | (⊥ : WithTop ℝ≥0) < τ n ω}.indicator (X s)) = X := by
      ext s ω
      have hpos : (⊥ : WithTop ℝ≥0) < τ n ω :=
        TauCeti.nnvolume.energyLocalizer_pos H (C := (n : ℝ≥0) + 1) (by positivity) ω
      exact indicator_of_mem hpos _
    rw [hX_ind]
    exact (hX_stop n).symm.ae_eq_eval t
  have hX_ito : IsItoIntegral ℱ P W H X :=
    hW.isItoIntegral_of_localized_stages hH.isStronglyPredictable hX_cont hloc
      hHstage hUae hX_stop fun t ↦ hH.ae_accumulatedEnergy_lt_top.mono fun ω hfin k hlt s hs ↦ by
        have hle : (s : WithTop ℝ≥0) ≤ τ k ω :=
          (WithTop.coe_le_coe.mpr (mem_Iic.mp hs)).trans hlt.le
        dsimp only [τ] at hle
        simpa only [ite_eq_left hle] using TauCeti.nnvolume.finiteEnergyCutoff_eqOn (hfin t) hs
  exact ⟨X, U, hX_prog, hX_cont, hX_loc, hX_ito, hUp, hUcont, hUae, hX_stop⟩

end TauCeti.Probability.IsFilteredPreBrownianReal
