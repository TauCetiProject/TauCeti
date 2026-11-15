/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Martingale
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
import Mathlib.MeasureTheory.Integral.Indicator
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Stopping
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Process.Stopping
import TauCeti.Probability.Process.StoppingApproximation

/-!
# Stopping and localizing the Brownian Itô integral process

This file proves stability of `TauCeti.IsItoIntegral` under stopping at raw-filtration stopping
times, deduces the native local-martingale property, and constructs predictable almost surely
continuous Itô integral processes across the full pathwise square-energy domain
`TauCeti.LocallyBrownianIntegrable`:

* `IsItoIntegral.stoppedProcess`: against a filtered pre-Brownian motion `W`, stopping an Itô
  integral `I` of `H` at a stopping time `τ` yields an Itô integral of the cutoff integrand
  `H · 1_{[0, τ]}`, without assuming path continuity of `W` or adaptation of `I`.
* `IsItoIntegral.stoppedProcess_indist_of_ae_eq`: local determination of `stoppedProcess I τ` by
  the restriction of the integrand to `[0, τ]`.
* `IsItoIntegral.locally_martingale`: any strongly progressive Itô integral against a filtered
  pre-Brownian motion is a native local martingale (`Locally (Martingale · ℱ P) ℱ I P`).
* `LocallyBrownianIntegrable.exists_isItoIntegral`: against a filtered pre-Brownian motion `W`
  with almost surely continuous paths, every `LocallyBrownianIntegrable` integrand admits a
  predictable almost surely continuous local-martingale Itô integral on the raw filtration.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open Set hiding mem_range
open Finset hiding Iic mem_Iic min_zero
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H K I J : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

private theorem tendstoInMeasure_simpleGains_of_le
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {v T : ℝ≥0} (hvT : v ≤ T)
    {n : ℕ → ℕ} {g : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hg : ∀ m, MonotoneOn (g m) (Iic (n m)))
    (ha : ∀ m j, j < n m → StronglyMeasurable[ℱ (g m j)] (a m j))
    (hE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (g m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure T}) atTop (𝓝 0)) :
    TendstoInMeasure P (fun m ↦ Finance.simpleGains (g m) (n m) (a m) W v) atTop (I v) := by
  have hle : Probability.timeMeasure v ≤ Probability.timeMeasure T := by
    rw [Probability.timeMeasure_def, Probability.timeMeasure_def]
    exact Measure.restrict_mono_set _ (Ioc_subset_Ioc_right hvT)
  refine hI.tendstoInMeasure_simpleGains hW hg ha fun δ hδ ↦ ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hE δ hδ)
    (fun _ ↦ zero_le) fun m ↦ measure_mono fun ω (hω : δ ≤ _) ↦ ?_
  exact hω.trans (lintegral_mono' hle le_rfl)

private theorem stoppedProcess_dyadicCeilTime
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hτ : IsStoppingTime ℱ τ) (d : ℕ) :
    IsItoIntegral ℱ P W
      (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then H t ω else 0)
      (stoppedProcess I (fun ω ↦ dyadicCeilTime d (τ ω))) := by
  let σ (ω : Ω) := dyadicCeilTime d (τ ω)
  refine ⟨hI.isStronglyPredictable.ite_le (hτ.dyadicCeilTime d),
    hI.ae_continuous.mono fun _ hc ↦ hc.stoppedProcess, fun T ↦ ?_⟩
  obtain ⟨n, g, a, hg, ha, hE, _⟩ := hI.exists_seq_approx T
  choose N r b hr hb hhold hgains using fun m ↦
    Finance.exists_simpleHolding_stopped_dyadicCeilTime hτ d T (hg m) (ha m) W
  refine ⟨N, r, b, hr, hb, fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
  · have hsub (m : ℕ) :
        {ω | ε ≤ ∫⁻ s, ‖Finance.simpleHolding (r m) (N m) (b m) s ω -
          (if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0)‖ₑ ^ 2 ∂Probability.timeMeasure T} ⊆
        {ω | ε ≤ ∫⁻ s, ‖Finance.simpleHolding (g m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure T} := fun ω hω ↦ by
      refine hω.trans (lintegral_mono_ae ?_)
      filter_upwards [Probability.ae_mem_Ioc_timeMeasure T] with s hs
      rw [hhold m s hs ω]
      by_cases hsσ : (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω)
      · rw [ite_eq_left hsσ, ite_eq_left hsσ]
      · rw [ite_eq_right hsσ, ite_eq_right hsσ, sub_self, eNorm_zero, zero_pow (by norm_num)]
        exact zero_le
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hE ε hε)
      (fun _ ↦ zero_le) fun m ↦ measure_mono (hsub m)
  · let S : Finset ℝ≥0 := (range (dyadicCount d T + 1)).image (dyadicGrid d T)
    have hv_lim (v : ℝ≥0) (hv : v ∈ S) : Tendsto
        (fun m ↦ P {ω | ε ≤ edist (Finance.simpleGains (g m) (n m) (a m) W v ω) (I v ω)})
        atTop (𝓝 0) := by
      obtain ⟨k, _, rfl⟩ := mem_image.1 hv
      exact tendstoInMeasure_simpleGains_of_le hW hI (dyadicGrid_le d T k) hg ha hE ε hε
    have hsum : Tendsto (fun m ↦ ∑ v ∈ S,
        P {ω | ε ≤ edist (Finance.simpleGains (g m) (n m) (a m) W v ω) (I v ω)})
        atTop (𝓝 0) := by
      simpa only [sum_const_zero] using tendsto_finsetSum S hv_lim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ ↦ zero_le) fun m ↦ ?_
    have hsub : {ω | ε ≤ edist (Finance.simpleGains (r m) (N m) (b m) W T ω)
        (stoppedProcess I σ T ω)} ⊆
        ⋃ v ∈ S,
          {ω | ε ≤ edist (Finance.simpleGains (g m) (n m) (a m) W v ω) (I v ω)} := by
      intro ω hω
      refine mem_biUnion (mem_image.2 ⟨dyadicStopIndex d T (τ ω),
        mem_range.2 (Nat.lt_succ_of_le (dyadicStopIndex_le d T (τ ω))),
        dyadicGrid_dyadicStopIndex d T (τ ω)⟩) ?_
      simpa only [mem_ofPred_eq, hgains m ω, stoppedProcess] using hω
    exact (measure_mono hsub).trans (measure_biUnion_finset_le S _)

private theorem tendsto_measure_lintegral_dyadicCeilTime [IsFiniteMeasure P]
    (hH : LocallyBrownianIntegrable ℱ P H) (hτ : IsStoppingTime ℱ τ)
    (T : ℝ≥0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun d ↦ P {ω | ε ≤ ∫⁻ s,
      ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then H s ω else 0) -
        (if (s : WithTop ℝ≥0) ≤ τ ω then H s ω else 0)‖ₑ ^ 2
      ∂Probability.timeMeasure T}) atTop (𝓝 0) := by
  let F (d : ℕ) (s : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
    ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then H s ω else 0) -
      (if (s : WithTop ℝ≥0) ≤ τ ω then H s ω else 0)‖ₑ ^ 2
  have hF_meas (d : ℕ) : Measurable (fun p : ℝ≥0 × Ω ↦ F d p.1 p.2) :=
    (((hH.isStronglyPredictable.ite_le (hτ.dyadicCeilTime d)).sub
      (hH.isStronglyPredictable.ite_le hτ)).mono ℱ.predictable_le_prod).measurable.eNorm
      |>.pow_const 2
  rw [← measure_empty (μ := P)]
  refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty
    (fun d ↦ (hF_meas d).lintegral_prod_left' measurableSet_Ici)
    (hH.ae_memLp.mono fun ω hω ↦ ?_)
  have hm := hω T
  rw [NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def] at hm
  have hlim := tendsto_lintegral_dyadicCeilTime (u := τ ω)
    (hm.aestronglyMeasurable.eNorm.pow_const 2)
    (hm.aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.1 hm).ne
  filter_upwards [hlim.eventually (eventually_lt_nhds hε)] with d hd
  simp only [Set.mem_empty_iff_false, iff_false, not_le]
  exact hd

namespace IsItoIntegral

/-- **Stopping an Itô integral.** Against a filtered pre-Brownian motion, stopping an Itô integral
at a stopping time `τ` on the raw filtration yields an Itô integral of the cutoff integrand
`H · 1_{[0, τ]}`. Neither path continuity of `W` nor adaptation of `I` is needed. -/
theorem stoppedProcess (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (MeasureTheory.stoppedProcess I τ) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hId (d : ℕ) := stoppedProcess_dyadicCeilTime hW hI hτ d
  have hWm (s : ℝ≥0) : AEStronglyMeasurable (W s) P :=
    ((hW.martingale.stronglyAdapted s).mono (ℱ.le s)).aestronglyMeasurable
  refine of_seq (hI.isStronglyPredictable.ite_le hτ)
    (hI.ae_continuous.mono fun _ hc ↦ hc.stoppedProcess) hId
    (fun T _ hε ↦ tendsto_measure_lintegral_dyadicCeilTime hI.locallyBrownianIntegrable hτ T hε)
    fun T ↦ tendstoInMeasure_of_tendsto_ae (fun d ↦ (hId d).aestronglyMeasurable hWm T) ?_
  filter_upwards [hI.ae_continuous] with ω hω
  exact tendsto_stoppedProcess_dyadicCeilTime I τ T ω hω.continuousAt.continuousWithinAt

/-- **Local congruence of Itô integrals.** Against a filtered pre-Brownian motion and at a stopping
time `τ`, two Itô integrals whose integrands agree `(timeMeasure T).prod P`-almost everywhere on
`[0, τ]` for every finite horizon `T` have indistinguishable stopped processes. -/
theorem stoppedProcess_indist_of_ae_eq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hτ : IsStoppingTime ℱ τ)
    (hHK : ∀ T : ℝ≥0, ∀ᵐ p ∂(Probability.timeMeasure T).prod P,
      (p.1 : WithTop ℝ≥0) ≤ τ p.2 → H p.1 p.2 = K p.1 p.2) :
    MeasureTheory.stoppedProcess I τ ≡ᵐ[P] MeasureTheory.stoppedProcess J τ := by
  refine (hI.stoppedProcess hW hτ).indist_of_ae_eq_prod hW (hJ.stoppedProcess hW hτ) fun T ↦ ?_
  filter_upwards [hHK T] with p hp
  dsimp only [Function.uncurry]
  split_ifs with h
  · exact hp h
  · rfl

/-- **Local martingale property of the Itô integral.** Every strongly progressive Itô integral
against a filtered pre-Brownian motion is a native local martingale on the raw filtration. -/
theorem locally_martingale (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hProg : IsStronglyProgressive ℱ I) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ I P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hH := hI.locallyBrownianIntegrable
  have hτ := hH.isLocalizingSequence_energyLocalizer
  have hMart (n : ℕ) : Martingale
      (MeasureTheory.stoppedProcess I (nnvolume.energyLocalizer H ((n : ℝ≥0) + 1))) ℱ P :=
    (hI.stoppedProcess hW (hτ.isStoppingTime n)).martingale hW
      (hH.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1))
      (hProg.stoppedProcess (hτ.isStoppingTime n)).stronglyAdapted
  refine hProg.locally_martingale_of_ae_stopped_eq hτ hMart fun n t ↦ .of_forall fun ω ↦ ?_
  have hpos : ω ∈ {ω | (⊥ : WithTop ℝ≥0) < nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω} :=
    nnvolume.energyLocalizer_pos H (by positivity : (0 : ℝ≥0) < n + 1) ω
  rw [stoppedProcess_indicator_comm']
  exact (Set.indicator_of_mem hpos _).symm

end IsItoIntegral

/-- **Existence of the localized Brownian Itô integral process.** Against a filtered pre-Brownian
motion `W` with almost surely continuous paths, every `LocallyBrownianIntegrable` integrand admits
a predictable almost surely continuous local-martingale Itô integral on the raw filtration. -/
theorem LocallyBrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ I P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τn (n : ℕ) := nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)
  have hτ := hH.isLocalizingSequence_energyLocalizer
  choose U hU_ito hU_pred _ using fun n : ℕ ↦
    (hH.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1)).exists_isItoIntegral hW hcont
  have hcompat (n m : ℕ) (hnm : n ≤ m) :
      MeasureTheory.stoppedProcess (U m) (τn n) ≡ᵐ[P] U n := by
    refine ((hU_ito m).stoppedProcess hW (hτ.isStoppingTime n)).indist_of_ae_eq hW (hU_ito n)
      fun _ ↦ .of_forall fun ω ↦ .of_forall fun t ↦ ?_
    have hmono : τn n ω ≤ τn m ω :=
      nnvolume.monotone_energyLocalizer H ω (by exact_mod_cast Nat.add_le_add_right hnm 1)
    dsimp only
    by_cases ht : (t : WithTop ℝ≥0) ≤ τn n ω
    · have htm : (t : WithTop ℝ≥0) ≤ τn m ω := ht.trans hmono
      dsimp only [τn] at ht htm
      rw [ite_eq_left ht, ite_eq_left htm, ite_eq_left ht]
    · dsimp only [τn] at ht
      rw [ite_eq_right ht, ite_eq_right ht]
  obtain ⟨X, hX_prog, hX_cont, hX_stop⟩ := exists_isStronglyProgressive_patch_stoppedProcess
    hτ.tendsto_top (fun n ↦ (hU_pred n).isStronglyProgressive)
    (fun n ↦ (hU_ito n).ae_continuous) hcompat
  obtain ⟨I, hI_pred, hIX⟩ :=
    hX_prog.stronglyAdapted.exists_isStronglyPredictable_indist_of_ae_isLeftContinuous
      (hX_cont.mono fun _ hc ↦ hc.isLeftContinuous)
  have hI_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω) := by
    filter_upwards [hX_cont, hIX] with ω hc hω using hc.congr (fun t ↦ (hω t).symm)
  have hI_ito : IsItoIntegral ℱ P W H I := by
    refine IsItoIntegral.of_seq hH.isStronglyPredictable hI_cont hU_ito
      (fun T _ hε ↦ hH.tendsto_measure_lintegral_energyLocalizer T hε) fun T ↦ ?_
    refine tendstoInMeasure_of_tendsto_ae
      (fun n ↦ ((hU_pred n).isStronglyProgressive.stronglyAdapted T
        |>.mono (ℱ.le T)).aestronglyMeasurable) ?_
    filter_upwards [hτ.tendsto_top, hIX, ae_all_iff.2 hX_stop] with ω hlim hIXω hstop
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(WithTop.tendsto_nhds_top_iff _).1 hlim T] with n hn
    rw [← hstop n T, stoppedProcess_eq_of_le hn.le, hIXω T]
  exact ⟨I, hI_ito, hI_pred, hI_ito.locally_martingale hW hI_pred.isStronglyProgressive⟩

end TauCeti
