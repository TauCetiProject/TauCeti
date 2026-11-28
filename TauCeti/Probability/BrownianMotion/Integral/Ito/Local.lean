/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
public import TauCeti.Probability.BrownianMotion.Integral.Ito.L2
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Stopping
import Mathlib.MeasureTheory.Integral.Indicator
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Integral.Lebesgue.Norm
import TauCeti.MeasureTheory.Measure.Prod
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Process.AccumulatedEnergy
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Process.StochasticInterval
import TauCeti.Probability.Process.Stopping
import TauCeti.Probability.Process.TimeAverage
import TauCeti.Probability.Process.TimeMeasure
import TauCeti.Topology.Instances.ENNReal

/-!
# Local-martingale property, localization stability, and localized Brownian Itô integration

`TauCeti.LocallyBrownianIntegrable ℱ P H` relaxes `TauCeti.BrownianIntegrable ℱ P H` to predictable
integrands with a.s. finite pathwise square energy on every finite horizon. Building on optional
stopping (`TauCeti.Probability.IsItoIntegral.stoppedProcess`, `stoppedProcess_indist`, `ite_Ioc`)
and the `L²` theory (`TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry`,
`TauCeti.Probability.BrownianMotion.Integral.Ito.L2`), this module establishes:

* `TauCeti.Probability.IsItoIntegral.of_stoppedProcess`: stability of `IsItoIntegral` under
  localization by measurable random times tending almost surely to `⊤`;
* `TauCeti.Probability.IsItoIntegral.ite_Ioc_add` and
  `TauCeti.Probability.IsFilteredPreBrownianReal.indist_ite_Ioc_add_stoppedProcess_sub`:
  adjacent stochastic-interval concatenation for Itô integrals and stopped integrals;
* `TauCeti.Probability.IsItoIntegral.locally_martingale` and
  `TauCeti.Probability.IsItoIntegral.locally_martingale_sq_sub`: strongly progressive continuous Itô
  integrals `I` and their square-compensated brackets `I t ^ 2 - ∫ s, H s ^ 2 ∂timeMeasure t` are
  native local martingales on the raw filtration;
* `TauCeti.LocallyBrownianIntegrable.exists_isItoIntegral` and
  `TauCeti.Probability.IsFilteredPreBrownianReal.exists_isItoIntegral_of_isStronglyProgressive`:
  existence of a strongly progressive continuous local-martingale Itô integral for
  `LocallyBrownianIntegrable` integrands (and predictable representative for strongly progressive
  inputs) whenever `W` has a.s. continuous paths.

No completeness or right continuity of the filtration is assumed anywhere.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, §2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H I J : ℝ≥0 → Ω → ℝ}

namespace Probability

/-! ### Localization stability and stochastic-interval concatenation -/

private theorem tendsto_measure_compl_goodEvent [IsFiniteMeasure P]
    {τ : ℕ → Ω → WithTop ℝ≥0} {Hseq : ℕ → ℝ≥0 → Ω → ℝ} {H : ℝ≥0 → Ω → ℝ}
    (hτ_meas : ∀ n, Measurable (τ n))
    (hHseq_meas : ∀ n, Measurable (fun p : ℝ≥0 × Ω ↦ Hseq n p.1 p.2 - H p.1 p.2))
    (hτ : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤))
    (hHeq : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n in atTop, EqOn (Hseq n · ω) (H · ω) (Iic T))
    (t : ℝ≥0) :
    let G (m : ℕ) : Set Ω := {ω | (t : WithTop ℝ≥0) < τ m ω} ∩
      {ω | ∫⁻ s, ‖Hseq m s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t = 0}
    (∀ m, MeasurableSet (G m)) ∧ Tendsto (fun m ↦ P (G m)ᶜ) atTop (𝓝 0) := by
  intro G
  have hE_meas (m : ℕ) : Measurable (fun ω ↦ ∫⁻ s, ‖Hseq m s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t) :=
    ((hHseq_meas m).eNorm.pow_const 2).lintegral_prod_left'
  have hG_meas (m : ℕ) : MeasurableSet (G m) :=
    (measurableSet_lt measurable_const (hτ_meas m)).inter (hE_meas m (measurableSet_singleton 0))
  refine ⟨hG_meas, ?_⟩
  simpa using tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    MeasurableSet.empty (fun m ↦ (hG_meas m).compl) <| by
      filter_upwards [hτ, hHeq] with ω hτω hHω
      obtain ⟨m, hm⟩ := eventually_atTop.mp
        ((hτω.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))).and (hHω t))
      refine eventually_atTop.mpr ⟨m, fun j hj ↦ ?_⟩
      simp only [mem_compl_iff, mem_empty_iff_false, iff_false, not_not, G, mem_inter_iff,
        Set.mem_ofPred_eq]
      exact ⟨(hm j hj).1, (TauCeti.ae_eq_iff_lintegral_enorm_sub_sq_eq_zero
        (((hHseq_meas j).comp measurable_prodMk_right).eNorm.pow_const 2).aemeasurable).mp
        ((ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ (hm j hj).2 hs.2)⟩

private theorem exists_simpleHolding_stage_approx
    {Hseq U : ℕ → ℝ≥0 → Ω → ℝ}
    (hU : ∀ n, IsItoIntegral ℱ P W (Hseq n) (U n)) {t : ℝ≥0}
    {G : ℕ → Set Ω} (hG_lim : Tendsto (fun m ↦ P (G m)ᶜ) atTop (𝓝 0)) (k : ℕ) :
    ∃ m n σ a,
      MonotoneOn σ (Iic n) ∧ (∀ j < n, StronglyMeasurable[ℱ (σ j)] (a j)) ∧
      P (G m)ᶜ < ((k : ℝ≥0∞) + 1)⁻¹ / 2 ∧
      P {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤ ∫⁻ s, ‖Finance.simpleHolding σ n a s ω - Hseq m s ω‖ₑ ^ 2
          ∂timeMeasure t} < ((k : ℝ≥0∞) + 1)⁻¹ / 2 ∧
      P {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤ edist (Finance.simpleGains σ n a W t ω) (U m t ω)} <
        ((k : ℝ≥0∞) + 1)⁻¹ / 2 := by
  have hδ : 0 < ((k : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.mpr (by simp)
  have hhalf : 0 < ((k : ℝ≥0∞) + 1)⁻¹ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨m, hm⟩ := (hG_lim.eventually (gt_mem_nhds hhalf)).exists
  obtain ⟨n', σ', a', hσ', ha', hE', hM'⟩ := (hU m).exists_approx t
  obtain ⟨j, hj1, hj2⟩ :=
    (((hE' _ hδ).eventually (gt_mem_nhds hhalf)).and
      ((hM' _ hδ).eventually (gt_mem_nhds hhalf))).exists
  exact ⟨m, n' j, σ' j, a' j, hσ' j, ha' j, hm, hj1, hj2⟩

/-- If `I` is almost surely continuous and, along measurable random times `τ n → ⊤` almost surely,
each stopped process `stoppedProcess I (τ n)` is indistinguishable from an Itô integral of a
process `Hseq n` that eventually agrees with `H` on every compact horizon `[0, T]` outside a common
null set, then `I` is an Itô integral of `H`. Neither monotonicity nor the stopping-time property
of `τ n` is required. -/
theorem IsItoIntegral.of_stoppedProcess [IsFiniteMeasure P]
    {τ : ℕ → Ω → WithTop ℝ≥0} {Hseq U : ℕ → ℝ≥0 → Ω → ℝ}
    (hH : IsStronglyPredictable ℱ H)
    (hIcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    (hτ_meas : ∀ n, Measurable (τ n))
    (hτ : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤))
    (hU : ∀ n, IsItoIntegral ℱ P W (Hseq n) (U n))
    (hstop : ∀ n, MeasureTheory.stoppedProcess I (τ n) ≡ᵐ[P] U n)
    (hHeq : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n in atTop, EqOn (Hseq n · ω) (H · ω) (Iic T)) :
    IsItoIntegral ℱ P W H I := by
  refine ⟨hH, hIcont, fun t ↦ ?_⟩
  have hdiff_meas (m : ℕ) : Measurable (fun p : ℝ≥0 × Ω ↦ Hseq m p.1 p.2 - H p.1 p.2) :=
    (((hU m).isStronglyPredictable.sub hH).mono ℱ.predictable_le_prod).measurable
  let G (m : ℕ) : Set Ω := {ω | (t : WithTop ℝ≥0) < τ m ω} ∩
    {ω | ∫⁻ s, ‖Hseq m s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t = 0}
  obtain ⟨-, hG_lim⟩ := tendsto_measure_compl_goodEvent hτ_meas hdiff_meas hτ hHeq t
  choose m n σ a hσ ha hGm hEk hMk using exists_simpleHolding_stage_approx hU hG_lim
  have hinv : Tendsto (fun k : ℕ ↦ ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_natCast_add_nhds_zero 1
  refine ⟨n, σ, a, hσ, ha, fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
  · refine TauCeti.tendsto_measure_of_subset_union hinv measure_empty
      (Eventually.of_forall fun k ↦ (hGm k).le) (Eventually.of_forall fun k ↦ (hEk k).le) ?_
    filter_upwards [hinv.eventually (gt_mem_nhds hε)] with k hk ω hω
    refine if hGω : ω ∈ G (m k) then Or.inr (Or.inr ?_) else Or.inr (Or.inl hGω)
    have hHeq_ae : (fun s ↦ Hseq (m k) s ω) =ᵐ[timeMeasure t] fun s ↦ H s ω :=
      (TauCeti.ae_eq_iff_lintegral_enorm_sub_sq_eq_zero
        (((hdiff_meas (m k)).comp measurable_prodMk_right).eNorm.pow_const 2).aemeasurable).mpr
        hGω.2
    have hlint : (∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure t) =
        ∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - Hseq (m k) s ω‖ₑ ^ 2
          ∂timeMeasure t :=
      lintegral_congr_ae (hHeq_ae.mono fun _ hs ↦ by dsimp only at hs ⊢; rw [hs])
    dsimp only [Set.mem_ofPred_eq] at hω ⊢
    exact hk.le.trans (hlint ▸ hω)
  · let N : Set Ω := {ω | ¬ ∀ j, MeasureTheory.stoppedProcess I (τ j) t ω = U j t ω}
    have hN : P N = 0 := ae_iff.mp ((ae_all_iff.mpr hstop).mono fun ω hω j ↦ hω j t)
    refine TauCeti.tendsto_measure_of_subset_union hinv hN
      (Eventually.of_forall fun k ↦ (hGm k).le) (Eventually.of_forall fun k ↦ (hMk k).le) ?_
    filter_upwards [hinv.eventually (gt_mem_nhds hε)] with k hk ω hω
    by_cases hNω : ω ∈ N
    · exact Or.inl hNω
    · by_cases hGω : ω ∈ G (m k)
      · refine Or.inr (Or.inr ?_)
        have hIU : I t ω = U (m k) t ω := by
          have h1 := (not_not.mp hNω) (m k)
          rwa [MeasureTheory.stoppedProcess_eq_of_le hGω.1.le] at h1
        dsimp only [Set.mem_ofPred_eq] at hω ⊢
        exact hk.le.trans (hIU ▸ hω)
      · exact Or.inr (Or.inl hGω)

/-- **Adjacent stochastic-interval concatenation for Itô integrals.** For ordered random times
`σ ≤ τ ≤ ρ`, summing Itô integrals of the restrictions `1_{(σ, τ]} H` and `1_{(τ, ρ]} H` yields
an Itô integral of `1_{(σ, ρ]} H`. Neither stopping-time properties nor path continuity of `W` is
needed. -/
theorem IsItoIntegral.ite_Ioc_add {σ τ ρ : Ω → WithTop ℝ≥0} (hστ : σ ≤ τ) (hτρ : τ ≤ ρ)
    {J₁ J₂ : ℝ≥0 → Ω → ℝ}
    (hJ₁ : IsItoIntegral ℱ P W
      (fun t ω ↦ if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) J₁)
    (hJ₂ : IsItoIntegral ℱ P W
      (fun t ω ↦ if τ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ ρ ω then H t ω else 0) J₂) :
    IsItoIntegral ℱ P W
      (fun t ω ↦ if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ ρ ω then H t ω else 0)
      (fun t ω ↦ J₁ t ω + J₂ t ω) := by
  rw [TauCeti.ite_Ioc_fun_eq_add_ite_Ioc hστ hτρ]
  exact hJ₁.add hJ₂

/-- **Adjacent stochastic-interval concatenation for stopped Itô integrals.** For ordered random
times `σ ≤ τ ≤ ρ` where `σ` and `ρ` are stopping times, summing Itô integrals of `1_{(σ, τ]} H` and
`1_{(τ, ρ]} H` is indistinguishable from `stoppedProcess I ρ - stoppedProcess I σ`. -/
theorem IsFilteredPreBrownianReal.indist_ite_Ioc_add_stoppedProcess_sub
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {σ τ ρ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hρ : IsStoppingTime ℱ ρ)
    (hστ : σ ≤ τ) (hτρ : τ ≤ ρ) {J₁ J₂ : ℝ≥0 → Ω → ℝ}
    (hJ₁ : IsItoIntegral ℱ P W
      (fun t ω ↦ if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) J₁)
    (hJ₂ : IsItoIntegral ℱ P W
      (fun t ω ↦ if τ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ ρ ω then H t ω else 0) J₂) :
    (fun t ω ↦ J₁ t ω + J₂ t ω) ≡ᵐ[P]
      fun t ω ↦ MeasureTheory.stoppedProcess I ρ t ω - MeasureTheory.stoppedProcess I σ t ω :=
  isItoIntegral_unique hW (hJ₁.ite_Ioc_add hστ hτρ hJ₂)
    (hI.ite_Ioc hW hσ hρ (hστ.trans hτρ))

/-! ### Local-martingale property and square compensation -/

namespace IsItoIntegral

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

/-- **Local-martingale Itô square compensation (quadratic variation bracket).** For any strongly
progressive Itô integral `I` of `H` against a filtered pre-Brownian motion `W`, the process
`I t ^ 2 - ∫ s, H s ^ 2 ∂timeMeasure t` is a native local martingale on the raw filtration,
without path continuity of `W`. -/
theorem locally_martingale_sq_sub
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hprog : IsStronglyProgressive ℱ I) :
    Locally (fun X ↦ Martingale X ℱ P) ℱ
      (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ (k : ℕ) := nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)
  have hτ_loc : IsLocalizingSequence ℱ τ P :=
    hI.locallyBrownianIntegrable.isLocalizingSequence_energyLocalizer
  have hHs (k : ℕ) : BrownianIntegrable ℱ P (energyStage H k) :=
    hI.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((k : ℝ≥0) + 1)
  have hmart (k : ℕ) : Martingale
      (fun t ω ↦ MeasureTheory.stoppedProcess I (τ k) t ω ^ 2 -
        ∫ s, energyStage H k s ω ^ 2 ∂timeMeasure t) ℱ P :=
    ((hI.stoppedProcess hW (hτ_loc.isStoppingTime k)).congr_integrand
      (hHs k).isStronglyPredictable fun T ↦ by
        filter_upwards [ae_mem_Ioc_timeMeasure_prod P T,
          (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T)
            (ν := P)).ae hI.locallyBrownianIntegrable.ae_accumulatedEnergy_lt_top] with p hpT hfin
        dsimp only [Function.uncurry, energyStage, τ]
        have hcut : nnvolume.finiteEnergyCutoff H p.1 p.2 = H p.1 p.2 :=
          nnvolume.finiteEnergyCutoff_eqOn (hfin T) hpT.2
        rw [hcut]).martingale_sq_sub hW (hHs k)
      (hprog.stoppedProcess (hτ_loc.isStoppingTime k)).stronglyAdapted
  have hX_prog : IsStronglyProgressive ℱ (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) :=
    fun t ↦ ((hprog t).pow 2).sub
      (hI.isStronglyPredictable.isStronglyPredictable_integral_sq_timeMeasure
        |>.isStronglyProgressive t)
  refine hX_prog.locally_martingale_of_ae_stopped_eq hτ_loc hmart fun k t ↦ ?_
  rw [nnvolume.stoppedProcess_indicator_pos_energyLocalizer H _ (by positivity)]
  filter_upwards [hI.locallyBrownianIntegrable.ae_accumulatedEnergy_lt_top] with ω hfin
  have hE_eq := hI.isStronglyPredictable.stoppedProcess_integral_sq_timeMeasure_eq (τ k) t hfin
  have hstop_sub :
      MeasureTheory.stoppedProcess (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t)
          (τ k) t ω =
        MeasureTheory.stoppedProcess I (τ k) t ω ^ 2 -
          MeasureTheory.stoppedProcess (fun u ω' ↦ ∫ s, H s ω' ^ 2 ∂timeMeasure u)
            (τ k) t ω := by
    simp only [MeasureTheory.stoppedProcess_eq_stoppedValue_apply, stoppedValue]
  rw [hstop_sub, ← hE_eq]
  rfl

end IsItoIntegral

end Probability

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

/-- **Existence of the Itô integral for strongly progressive integrands.** Against an almost
surely continuous filtered pre-Brownian motion, every strongly progressive integrand with almost
surely finite pathwise square energy on every finite horizon admits a predictable representative `G`
agreeing with `H` almost everywhere with respect to `(timeMeasure T).prod P` on every finite
horizon `T`, together with a strongly progressive, almost surely continuous Itô integral `I` of `G`
that is a native local martingale on the raw filtration. By
`TauCeti.Probability.IsItoIntegral.indist_of_ae_eq`, any two such predictable representatives yield
indistinguishable Itô integrals. -/
theorem Probability.IsFilteredPreBrownianReal.exists_isItoIntegral_of_isStronglyProgressive
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : IsStronglyProgressive ℱ H)
    (hHmem : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, MemLp (fun t ↦ H t ω) 2 (Probability.timeMeasure T)) :
    ∃ G I : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable ℱ G ∧
      (∀ T : ℝ≥0, Function.uncurry G =ᵐ[(Probability.timeMeasure T).prod P] Function.uncurry H) ∧
      Probability.IsItoIntegral ℱ P W G I ∧ IsStronglyProgressive ℱ I ∧
        Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨G, hGpred, hGH_real⟩ := hH.exists_isStronglyPredictable_ae_prod P
  have hGH (T : ℝ≥0) :
      Function.uncurry G =ᵐ[(Probability.timeMeasure T).prod P] Function.uncurry H :=
    ((((measurePreserving_coe_timeMeasure T).prod (MeasurePreserving.id P)).quasiMeasurePreserving
      |>.ae_eq_comp (hGH_real T))).mono fun ⟨s, ω⟩ hp ↦ by
      simpa only [Function.uncurry_apply_pair, Function.comp_apply, Prod.map_apply, id_eq,
        Real.toNNReal_coe] using hp
  have hG_loc : LocallyBrownianIntegrable ℱ P G := by
    refine locallyBrownianIntegrable_iff_nat.2 ⟨hGpred, fun n ↦ ?_⟩
    have hsec : ∀ᵐ ω ∂P, (fun t ↦ H t ω) =ᵐ[Probability.timeMeasure n] fun t ↦ G t ω :=
      (Measure.ae_ae_eq_flip_of_ae_eq_uncurry (hGH n)).mono fun _ h ↦ h.symm
    filter_upwards [hHmem, hsec] with ω hω heq
    rw [← NNReal.coe_natCast n, NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def]
    exact (hω n).ae_eq heq
  obtain ⟨I, hI, hIprog, hIloc⟩ := hG_loc.exists_isItoIntegral hW hcont
  exact ⟨G, I, hGpred, hGH, hI, hIprog, hIloc⟩

end TauCeti
