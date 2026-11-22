/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.Stopping.Integral
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
import TauCeti.Probability.BrownianMotion.Integral.Locality
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Martingale.Local.Version
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.Patching

/-!
# Existence and properties of the continuous-time Brownian Itô integral

For a filtration-relative Brownian motion `W` with almost surely continuous paths and a locally
square-integrable predictable integrand `H` (`TauCeti.LocallyBrownianIntegrable ℱ P H`), this file
proves existence, local-martingale regularity, optional stopping, stochastic-interval differences,
deterministic-time measurable multipliers, and local pathwise congruence for
`TauCeti.Probability.IsItoIntegral` on the original raw filtration. Basic algebraic closure
properties and uniqueness belong to `TauCeti.Probability.BrownianMotion.Integral.Ito.Basic`.

Existence (`exists_isItoIntegral`) localizes `H` by closed-level hits of its repaired energy clock
(`TauCeti.nnvolume.energyLocalizer`), constructs continuous martingale stages via
`exists_continuous_l2Integral`, verifies stage compatibility via `stoppedProcess_ae_eq_l2Integral`,
patches the stages without enlarging the filtration, and upgrades the patched local martingale to
an indistinguishable strongly predictable version. Stopping an Itô integral at any raw stopping
time `σ` represents `H` cut off to `⟦0, σ⟧` (`itoIntegral_stoppedProcess`), yielding stopped
energy-stage identification (`stoppedProcess_energyLocalizer_ae_eq_l2Integral`), difference laws
on `(σ, τ]` (`itoIntegral_ite_Ioc`), future multiplier laws after deterministic `s`
(`itoIntegral_ite_lt_mul`), local congruence (`itoIntegral_local_congr`), and the global `L²`
isometry and martingale properties when `H` is `BrownianIntegrable` (without path continuity of
`W`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D, §3.3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

namespace IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W H K I J : ℝ≥0 → Ω → ℝ}

/-- Any almost surely continuous modification of `t ↦ hW.l2Integral t (hH.toPredictableLp t)`
satisfies the elementary-approximation specification `IsItoIntegral`. -/
theorem isItoIntegral_of_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) :
    IsItoIntegral ℱ P W H I where
  isStronglyPredictable := hH.isStronglyPredictable
  ae_continuous := hI_cont
  exists_approx t := by
    let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
    have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
      MemLp.of_bound ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable (C k)
        (Eventually.of_forall (hb k j hj))
    refine ⟨n, τ, a, fun k ↦ (hτ k).monotoneOn, ha, fun _ hε ↦
      MeasureTheory.tendsto_measure_le_lintegral_enorm_pow_of_tendsto_eLpNorm (n := 2) two_ne_zero
        (g := fun k p ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2)
        (fun k ↦ (((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
          hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
        (by simpa only [Nat.cast_ofNat] using herr t) hε,
      tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_⟩
    exact hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
      (fun _ ↦ hH) (fun _ ↦ hI t) (fun k ↦ (hτ k).monotoneOn) ha ha₂ (herr t)

private theorem isItoIntegral_of_localized_stages
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
    choose n grid a C _ hgrid ha hb herr using fun k : ℕ ↦
      ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t (hHstage k).isStronglyPredictable
        ((hHstage k).memLp_timeMeasure t) (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (k + 1)))
    have herr_lim : Tendsto (fun k ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (grid k) (n k) (a k) p.1 p.2 - Hstage k p.1 p.2) 2
          ((timeMeasure t).prod P)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
        (fun _ ↦ bot_le) fun k ↦ (herr k).le
    have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
      MemLp.of_bound ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable (C k)
        (Eventually.of_forall (hb k j hj))
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

private theorem exists_patched_energyLocalizer_process
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

/-- **Local-martingale property of the Brownian Itô integral.** Any strongly progressive process
satisfying `IsItoIntegral` for a `LocallyBrownianIntegrable` integrand is a native local
martingale on the original raw filtration. -/
theorem itoIntegral_localMartingale
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI_prog : IsStronglyProgressive ℱ I) (hI : IsItoIntegral ℱ P W H I) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ I P := by
  obtain ⟨J, _, hJ_loc, hJ_ito⟩ := hW.exists_isItoIntegral hcont hH
  exact hI_prog.locally_martingale_of_indist hJ_loc (isItoIntegral_unique hW hJ_ito hI)

/-- **Optional stopping of the Brownian Itô integral.** Stopping an Itô integral of a
`LocallyBrownianIntegrable` integrand `H` at any raw stopping time `σ` yields an Itô integral of
`H` cut off to `⟦0, σ⟧`. -/
theorem itoIntegral_stoppedProcess
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) :
    IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (stoppedProcess I σ) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
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

/-- **Difference law on `(σ, τ]` for the Brownian Itô integral.** Restricting a
`LocallyBrownianIntegrable` integrand to the half-open stochastic interval `(σ, τ]` corresponds to
`stoppedProcess I τ - stoppedProcess I (σ ⊓ τ)`, without requiring `σ ≤ τ`. -/
theorem itoIntegral_ite_Ioc
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (fun t ω ↦ stoppedProcess I τ t ω - stoppedProcess I (σ ⊓ τ) t ω) := by
  convert (hW.itoIntegral_stoppedProcess hcont hH hI hτ).sub
    (hW.itoIntegral_stoppedProcess hcont hH hI (hσ.min hτ)) using 1
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
restricting a `LocallyBrownianIntegrable` integrand to `(σ, τ]` corresponds to
`stoppedProcess I τ - stoppedProcess I σ`. -/
theorem itoIntegral_ite_Ioc_of_le
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) :
    IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (fun t ω ↦ stoppedProcess I τ t ω - stoppedProcess I σ t ω) := by
  simpa only [inf_of_le_left hστ] using hW.itoIntegral_ite_Ioc hcont hH hI hσ hτ

/-- Indistinguishability form of `itoIntegral_ite_Ioc`. -/
theorem itoIntegral_ite_Ioc_indist
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hJ : IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) J) :
    J ≡ᵐ[P] fun t ω ↦ stoppedProcess I τ t ω - stoppedProcess I (σ ⊓ τ) t ω :=
  isItoIntegral_unique hW hJ (hW.itoIntegral_ite_Ioc hcont hH hI hσ hτ)

/-- Indistinguishability form of `itoIntegral_ite_Ioc_of_le`. -/
theorem itoIntegral_ite_Ioc_indist_of_le
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ)
    (hJ : IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) J) :
    J ≡ᵐ[P] fun t ω ↦ stoppedProcess I τ t ω - stoppedProcess I σ t ω :=
  isItoIntegral_unique hW hJ (hW.itoIntegral_ite_Ioc_of_le hcont hH hI hσ hτ hστ)

/-- **Deterministic-time measurable multiplier law for the Brownian Itô integral.** Multiplying
a `LocallyBrownianIntegrable` integrand after a deterministic time `s` by an `ℱ s`-measurable
random variable `ξ` scales the post-`s` increment `I t - I (min s t)` by `ξ`. No boundedness or
moment assumption on `ξ` is required. -/
theorem itoIntegral_ite_lt_mul
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I)
    (s : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if s < t then ξ ω * H t ω else 0)
      (fun t ω ↦ ξ ω * (I t ω - I (min s t) ω)) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨X, U, _, hX_cont, _, hX_ito, _, hUcont, hUae, hX_stop⟩ :=
    hW.exists_patched_energyLocalizer_process hcont hH
  let τ₁ (m : ℕ) := TauCeti.nnvolume.energyLocalizer H ((m : ℝ≥0) + 1)
  let τ₂ (m : ℕ) (ω : Ω) : WithTop ℝ≥0 := if ‖ξ ω‖ ≤ (m : ℝ) then ⊤ else s
  have hτ₂_meas (m : ℕ) : MeasurableSet[ℱ s] {ω | ‖ξ ω‖ ≤ (m : ℝ)} := by
    let : MeasurableSpace Ω := ℱ s
    exact hξ.measurable.norm measurableSet_Iic
  have hτ₂_st (m : ℕ) : IsStoppingTime ℱ (τ₂ m) := by
    intro t
    by_cases hst : s ≤ t
    · have heq : {ω | τ₂ m ω ≤ (t : WithTop ℝ≥0)} = {ω | ‖ξ ω‖ ≤ (m : ℝ)}ᶜ := by
        ext ω
        change (if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s) ≤ t ↔ ¬ ‖ξ ω‖ ≤ (m : ℝ)
        by_cases h : ‖ξ ω‖ ≤ (m : ℝ)
        · rw [ite_eq_left h]
          exact iff_of_false (WithTop.not_top_le_coe t) (not_not.mpr h)
        · rw [ite_eq_right h]
          exact iff_of_true (WithTop.coe_le_coe.mpr hst) h
      rw [heq]
      exact ℱ.mono hst _ (hτ₂_meas m).compl
    · have heq : {ω | τ₂ m ω ≤ (t : WithTop ℝ≥0)} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun ω ↦ ?_
        change ¬ (if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s) ≤ t
        by_cases h : ‖ξ ω‖ ≤ (m : ℝ)
        · rw [ite_eq_left h]
          exact not_le.mpr (WithTop.coe_lt_top t)
        · rw [ite_eq_right h]
          exact not_le.mpr (WithTop.coe_lt_coe.mpr (not_le.mp hst))
      rw [heq]
      exact @MeasurableSet.empty Ω (ℱ t)
  have hτ₂_mono (ω : Ω) : Monotone (fun m ↦ τ₂ m ω) := fun m n hmn ↦ by
    by_cases hm : ‖ξ ω‖ ≤ (m : ℝ)
    · have hn : ‖ξ ω‖ ≤ (n : ℝ) := hm.trans (by exact_mod_cast hmn)
      dsimp only [τ₂]
      rw [ite_eq_left hm, ite_eq_left hn]
    · simp only [τ₂, ite_eq_right hm]
      split_ifs
      · exact le_top
      · exact le_rfl
  have hτ₂_top (ω : Ω) : Tendsto (fun m ↦ τ₂ m ω) atTop (𝓝 ⊤) := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖ξ ω‖
    exact tendsto_const_nhds.congr' ((eventually_ge_atTop N).mono fun m hm ↦ by
      have hle : ‖ξ ω‖ ≤ (m : ℝ) := hN.trans (by exact_mod_cast hm)
      dsimp only [τ₂]
      exact (ite_eq_left hle).symm)
  let τ (m : ℕ) (ω : Ω) : WithTop ℝ≥0 := min (τ₁ m ω) (τ₂ m ω)
  have hloc₁ := hH.isLocalizingSequence_energyLocalizer
  have hloc : IsLocalizingSequence ℱ τ P := by
    refine ⟨⟨fun m ↦ (hloc₁.isStoppingTime m).min (hτ₂_st m), ?_⟩, ?_⟩
    · filter_upwards [hloc₁.tendsto_top] with ω hω
      refine (WithTop.tendsto_nhds_top_iff _).mpr fun t ↦ ?_
      filter_upwards [(WithTop.tendsto_nhds_top_iff _).mp hω t,
        (WithTop.tendsto_nhds_top_iff _).mp (hτ₂_top ω) t] with m hm₁ hm₂
      exact lt_min hm₁ hm₂
    · filter_upwards [hloc₁.mono] with ω hω m n hmn
      exact min_le_min (hω hmn) (hτ₂_mono ω hmn)
  let ξ_m (m : ℕ) (ω : Ω) : ℝ := if ‖ξ ω‖ ≤ (m : ℝ) then ξ ω else 0
  have hξ_m (m : ℕ) : StronglyMeasurable[ℱ s] (ξ_m m) := by
    let : MeasurableSpace Ω := ℱ s
    exact hξ.ite (hτ₂_meas m) stronglyMeasurable_const
  have hξ_m_bd (m : ℕ) : MemLp (ξ_m m) ∞ P :=
    memLp_top_of_bound ((hξ_m m).mono (ℱ.le s)).aestronglyMeasurable (m : ℝ)
      (Eventually.of_forall fun ω ↦ by
        by_cases h : ‖ξ ω‖ ≤ (m : ℝ)
        · dsimp only [ξ_m]; rwa [ite_eq_left h]
        · dsimp only [ξ_m]; rw [ite_eq_right h, norm_zero]; exact Nat.cast_nonneg m)
  let Hbase (m : ℕ) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P) ((m : ℝ≥0) + 1)
  let Hstage (m : ℕ) : ℝ≥0 → Ω → ℝ := fun t ω ↦
    if s < t then ξ_m m ω * (if (t : WithTop ℝ≥0) ≤ τ₁ m ω then
      TauCeti.nnvolume.finiteEnergyCutoff H t ω else 0) else 0
  have hHstage (m : ℕ) : BrownianIntegrable ℱ P (Hstage m) :=
    (Hbase m).ite_lt_mul s (hξ_m m) (hξ_m_bd m)
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ ξ ω * (X t ω - X (min s t) ω)
  let V (m : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ := ξ_m m ω * (U m t ω - U m (min s t) ω)
  have hY_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω) := hX_cont.mono fun _ hc ↦
    continuous_const.mul (hc.sub (hc.comp (continuous_const.min continuous_id)))
  have hUae' (m : ℕ) (t : ℝ≥0) : V m t =ᵐ[P] hW.l2Integral t ((hHstage m).toPredictableLp t) := by
    have hmul := hW.coeFn_l2Integral_ite_lt_mul_eq_mul_sub (Hbase m) s t (hξ_m m) (hξ_m_bd m)
    filter_upwards [hmul, hUae m t, hUae m (min s t)] with ω hω ht hmin
    exact (congrArg (fun x ↦ ξ_m m ω * x) (congrArg₂ Sub.sub ht hmin)).trans hω.symm
  have hstop (m : ℕ) : stoppedProcess Y (τ m) ≡ᵐ[P] V m := by
    refine TauCeti.indist_of_ae_continuous (hY_cont.mono fun _ hc ↦ hc.stoppedProcess)
      ((hUcont m).mono fun _ hc ↦
        continuous_const.mul (hc.sub (hc.comp (continuous_const.min continuous_id)))) fun t ↦ ?_
    filter_upwards [(hX_stop m).ae_eq_eval t, (hX_stop m).ae_eq_eval (min s t)] with ω ht hmin
    by_cases hm : ‖ξ ω‖ ≤ (m : ℝ)
    · have hτ_eq : τ m ω = τ₁ m ω :=
        min_eq_left (by dsimp only [τ₂]; rw [ite_eq_left hm]; exact le_top)
      have hξ_eq : ξ_m m ω = ξ ω := ite_eq_left hm
      have hmin_eq : min s (min (t : WithTop ℝ≥0) (τ₁ m ω)).untopA =
          (min ((min s t : ℝ≥0) : WithTop ℝ≥0) (τ₁ m ω)).untopA := by
        cases τ₁ m ω with
        | top =>
          rw [min_top_right, min_top_right]
          simp only [WithTop.untopA, WithTop.untopD_coe]
        | coe r =>
          rw [← WithTop.coe_min, ← WithTop.coe_min]
          simp only [WithTop.untopA, WithTop.untopD_coe, min_assoc]
      dsimp only [stoppedProcess, Y, V]
      rw [hτ_eq, hξ_eq, hmin_eq]
      dsimp only [τ₁]
      rw [← ht, ← hmin]
      rfl
    · have hτ_le : τ m ω ≤ (s : WithTop ℝ≥0) := by
        refine (min_le_right _ _).trans_eq ?_
        dsimp only [τ₂]
        exact ite_eq_right hm
      have hu_lt : min (t : WithTop ℝ≥0) (τ m ω) ≠ ⊤ :=
        ne_of_lt ((min_le_left _ _).trans_lt (WithTop.coe_lt_top t))
      have hu_le : (min (t : WithTop ℝ≥0) (τ m ω)).untopA ≤ s := by
        lift min (t : WithTop ℝ≥0) (τ m ω) to ℝ≥0 using hu_lt with u hu
        exact WithTop.coe_le_coe.mp (hu ▸ (min_le_right _ _).trans hτ_le)
      have hmin_eq : min s (min (t : WithTop ℝ≥0) (τ m ω)).untopA =
          (min (t : WithTop ℝ≥0) (τ m ω)).untopA := min_eq_right hu_le
      have hξ0 : ξ_m m ω = 0 := ite_eq_right hm
      dsimp only [stoppedProcess, Y, V]
      rw [hmin_eq, sub_self, mul_zero, hξ0, zero_mul]
  have hY_ito : IsItoIntegral ℱ P W (fun t ω ↦ if s < t then ξ ω * H t ω else 0) Y := by
    refine hW.isItoIntegral_of_localized_stages
      (hH.ite_lt_mul s hξ).isStronglyPredictable hY_cont hloc hHstage hUae' hstop fun t ↦ ?_
    filter_upwards [hH.ae_accumulatedEnergy_lt_top] with ω hfin m hlt u hu
    by_cases hsu : s < u
    · have hs_lt_t : s < t := hsu.trans_le hu
      have hτ_gt_s : (s : WithTop ℝ≥0) < τ₂ m ω :=
        (WithTop.coe_lt_coe.mpr hs_lt_t).trans (hlt.trans_le (min_le_right _ _))
      have hm : ‖ξ ω‖ ≤ (m : ℝ) := by
        by_contra hnot
        have : τ₂ m ω = (s : WithTop ℝ≥0) := ite_eq_right hnot
        exact absurd (this ▸ hτ_gt_s) (lt_irrefl _)
      have hle₁ : (u : WithTop ℝ≥0) ≤ τ₁ m ω :=
        (WithTop.coe_le_coe.mpr (mem_Iic.mp hu)).trans (hlt.trans_le (min_le_left _ _)).le
      have hcut : TauCeti.nnvolume.finiteEnergyCutoff H u ω = H u ω :=
        TauCeti.nnvolume.finiteEnergyCutoff_eqOn (hfin t) hu
      simp only [Hstage, ite_eq_left hsu, ξ_m, ite_eq_left hm, ite_eq_left hle₁, hcut]
    · simp [Hstage, hsu]
  refine hY_ito.congr ?_
  filter_upwards [isItoIntegral_unique hW hX_ito hI] with ω hω
  intro t
  simp [Y, hω t, hω (min s t)]

/-- Indistinguishability form of `itoIntegral_ite_lt_mul`. -/
theorem itoIntegral_ite_lt_mul_indist
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I)
    (s : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ)
    (hJ : IsItoIntegral ℱ P W (fun t : ℝ≥0 ↦ fun ω ↦ if s < t then ξ ω * H t ω else 0) J) :
    J ≡ᵐ[P] fun t ω ↦ ξ ω * (I t ω - I (min s t) ω) :=
  isItoIntegral_unique hW hJ (hW.itoIntegral_ite_lt_mul hcont hH hI s hξ)

/-- **Local congruence of the Brownian Itô integral.** If two `LocallyBrownianIntegrable`
integrands agree product-almost-everywhere on `⟦0, σ⟧` over every finite horizon for a raw stopping
time `σ`, their Itô integrals agree up to indistinguishability when stopped at `σ`. -/
theorem itoIntegral_local_congr
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) (hK : LocallyBrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ)
    (hHK : ∀ t : ℝ≥0,
      Function.uncurry (fun s : ℝ≥0 ↦ fun ω ↦ if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0) =ᵐ[
        (timeMeasure t).prod P]
      Function.uncurry (fun s : ℝ≥0 ↦ fun ω ↦ if (s : WithTop ℝ≥0) ≤ σ ω then K s ω else 0)) :
    stoppedProcess I σ ≡ᵐ[P] stoppedProcess J σ := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hIσ := (hW.itoIntegral_stoppedProcess hcont hH hI hσ).congr_integrand
    (hK.isStronglyPredictable.ite_le hσ) hHK
  exact isItoIntegral_unique hW hIσ (hW.itoIntegral_stoppedProcess hcont hK hJ hσ)

/-- When `H` has finite expected square energy on every finite horizon (`BrownianIntegrable`), any
process `I` satisfying `IsItoIntegral ℱ P W H I` agrees almost everywhere at each time `t` with
`hW.l2Integral t (hH.toPredictableLp t)`. Neither path continuity of `W` nor usual conditions on
the filtration are needed. -/
theorem itoIntegral_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨n, τ, a, hτ, ha, hKH, hKI⟩ := hI.exists_approx t
  obtain ⟨m, σ, b, C, _, hσ, hb, hbd, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have hbd₂ (k j : ℕ) (hj : j < m k) : MemLp (b k j) 2 P :=
    MemLp.of_bound ((hb k j hj).mono (ℱ.le _)).aestronglyMeasurable (C k)
      (Eventually.of_forall (hbd k j hj))
  have hLH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (σ k) (m k) (b k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t})
        atTop (𝓝 0) := fun _ hε ↦
    MeasureTheory.tendsto_measure_le_lintegral_enorm_pow_of_tendsto_eLpNorm (n := 2) two_ne_zero
      (g := fun k p ↦ Finance.simpleHolding (σ k) (m k) (b k) p.1 p.2 - H p.1 p.2)
      (fun k ↦ (((Finance.isStronglyPredictable_simpleHolding (hb k)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
      (by simpa only [Nat.cast_ofNat] using herr t) hε
  have hLJ : TendstoInMeasure P (fun k ↦ Finance.simpleGains (σ k) (m k) (b k) W t)
      atTop (hW.l2Integral t (hH.toPredictableLp t)) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) <| by
      simpa only [Pi.sub_def] using
        hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
          (fun _ ↦ hH) (fun _ ↦ .rfl) (fun k ↦ (hσ k).monotoneOn) hb hbd₂ (herr t)
  choose N ρ c _ hρ hc hhold hgain using fun k ↦
    Finance.exists_simpleHolding_simpleGains_eq_sub ℱ (hτ k) (hσ k).monotoneOn (ha k) (hb k)
  have hdiff : TendstoInMeasure P (fun k ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω -
      Finance.simpleGains (σ k) (m k) (b k) W t ω) atTop (fun _ ↦ 0) := by
    have henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
        ∫⁻ s, ‖Finance.simpleHolding (ρ k) (N k) (c k) s ω‖ₑ ^ 2 ∂timeMeasure t})
          atTop (𝓝 0) := fun ε hε ↦ by
      refine TauCeti.tendsto_measure_le_lintegral_of_le_two_mul_add
        (f₁ := fun k s ω ↦ ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2)
        (f₂ := fun k s ω ↦ ‖Finance.simpleHolding (σ k) (m k) (b k) s ω - H s ω‖ₑ ^ 2)
        (fun k ω ↦ (((((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
          hH.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const
            2).comp (measurable_id.prodMk measurable_const)).aemeasurable)
        (fun k s ω ↦ ?_) hKH hLH hε
      rw [hhold k s ω, ← mul_add]
      exact TauCeti.eNorm_sub_sq_le_two_mul _ _ (H s ω)
    exact (hW.tendstoInMeasure_simpleGains_of_energy (fun k ↦ (hρ k).monotoneOn) hc t
      henergy).congr_left fun k ↦ ae_of_all _ fun ω ↦ hgain k W t ω
  obtain ⟨ns, hns, hK⟩ := hKI.exists_seq_tendsto_ae
  obtain ⟨ns', hns', hL⟩ := (hLJ.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ns'', hns'', hD⟩ :=
    ((hdiff.comp hns.tendsto_atTop).comp hns'.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hK, hL, hD] with ω hKω hLω hDω
  have hsub := (hKω.comp (hns'.tendsto_atTop.comp hns''.tendsto_atTop)).sub
    (hLω.comp hns''.tendsto_atTop)
  exact sub_eq_zero.mp (tendsto_nhds_unique hsub hDω)

/-- **Closed-level energy-stage identification for any Brownian Itô integral.** Stopping an Itô
integral of a `LocallyBrownianIntegrable` integrand at `TauCeti.nnvolume.energyLocalizer H C`
identifies at each time `t` almost everywhere with the completed `L²` integral of its stopped
finite-energy cutoff. -/
theorem stoppedProcess_energyLocalizer_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (C t : ℝ≥0) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    stoppedProcess I (TauCeti.nnvolume.energyLocalizer H C) t =ᵐ[P]
      hW.l2Integral t ((hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer
        (P := P) C).toPredictableLp t) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let τ := TauCeti.nnvolume.energyLocalizer H C
  have hτ : IsStoppingTime ℱ τ :=
    hH.isStronglyPredictable.isStoppingTime_energyLocalizer TauCeti.nnvolume C
  let hHcut := hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P) C
  have hstop : IsItoIntegral ℱ P W
      (fun s ω ↦ if (s : WithTop ℝ≥0) ≤ τ ω then TauCeti.nnvolume.finiteEnergyCutoff H s ω else 0)
      (stoppedProcess I τ) := by
    refine (hW.itoIntegral_stoppedProcess hcont hH hI hτ).congr_integrand
      hHcut.isStronglyPredictable fun u ↦ ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure u) (ν := P)).ae
        (ae_mem_Ioc_timeMeasure u),
      (Measure.quasiMeasurePreserving_snd (μ := timeMeasure u) (ν := P)).ae
        hH.ae_accumulatedEnergy_lt_top] with ⟨s, ω⟩ hs hfin
    by_cases hle : (s : WithTop ℝ≥0) ≤ τ ω
    · simp only [Function.uncurry_apply_pair, ite_eq_left hle]
      exact (TauCeti.nnvolume.finiteEnergyCutoff_eqOn (hfin u) hs.2).symm
    · simp only [Function.uncurry_apply_pair, ite_eq_right hle]
  exact hW.itoIntegral_ae_eq_l2Integral hHcut hstop t

/-- **Cross-isometry of the Brownian Itô integral** on `BrownianIntegrable` integrands. -/
theorem itoIntegral_mul_isometry
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (T : ℝ≥0) :
    ∫ ω, I T ω * J T ω ∂P = ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure T).prod P :=
  hW.integral_mul_of_ae_eq_l2Integral hH hK
    (hW.itoIntegral_ae_eq_l2Integral hH hI)
    (hW.itoIntegral_ae_eq_l2Integral hK hJ) T

/-- Any strongly adapted Itô integral of a `BrownianIntegrable` integrand is a true martingale on
the original raw filtration, with square-compensation martingale `I_t² - ∫_{(0, t]} H_s² ds`. -/
theorem itoIntegral_martingale
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H)
    (hI_adapt : StronglyAdapted ℱ I) (hI : IsItoIntegral ℱ P W H I) :
    Martingale I ℱ P ∧
      Martingale (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P :=
  ⟨hW.martingale_of_ae_eq_l2Integral hH hI_adapt (hW.itoIntegral_ae_eq_l2Integral hH hI),
    hW.martingale_sq_sub_integral_of_ae_eq_l2Integral hH hI_adapt
      (hW.itoIntegral_ae_eq_l2Integral hH hI)⟩

end IsFilteredPreBrownianReal

end TauCeti.Probability
