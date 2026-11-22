/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.NNReal
public import TauCeti.Probability.Process.EnergyLocalizer
public import TauCeti.Probability.Process.TimeMeasure
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
public import Mathlib.Probability.Process.LocalProperty
import TauCeti.MeasureTheory.Integral.Lebesgue.Cutoff
import TauCeti.Probability.Process.LocalProperty

/-!
# Closed-level energy localization of Brownian integrands

Stop the finite-energy cutoff of a predictable integrand at the first closed-level hit of
its repaired energy clock. The resulting integrand is Brownian integrable under a finite
sample measure: its pathwise square energy is bounded by the level, hence its expected
square energy is finite. These stopping times belong to the original raw filtration.

For locally Brownian-integrable inputs, stopping the original integrand directly at any closed
energy level already yields a Brownian-integrable process, and the integer levels form a native
localizing sequence along which the pathwise square-energy error on each finite horizon tends to
zero in measure. On one common sample-full event the stopped cutoffs eventually agree with the
original integrand on every finite horizon. No stochastic integral or usual augmentation is
constructed.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}

/-- The finite-energy cutoff stopped at a closed-level energy hit is Brownian integrable,
even without any moment or local-integrability assumption on the original integrand. -/
theorem MeasureTheory.IsStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer
    [IsFiniteMeasure P] (hH : IsStronglyPredictable ℱ H) (C : ℝ≥0) :
    TauCeti.BrownianIntegrable ℱ P (fun t ω ↦
      if (t : WithTop ℝ≥0) ≤ TauCeti.nnvolume.energyLocalizer H C ω then
        TauCeti.nnvolume.finiteEnergyCutoff H t ω else 0) := by
  have hp := (hH.finiteEnergyCutoff TauCeti.nnvolume).ite_le
    (hH.isStoppingTime_energyLocalizer TauCeti.nnvolume C)
  refine ⟨hp, fun T ↦ ?_⟩
  rw [TauCeti.Probability.timeMeasure_def, ← TauCeti.nnvolume_def]
  have hm := (hp.mono ℱ.predictable_le_prod).aestronglyMeasurable
    (μ := (TauCeti.nnvolume.restrict (Ioc 0 T)).prod P)
  rw [hm.memLp_two_iff_lintegral_enorm_sq_lt_top]
  calc
    _ = ∫⁻ ω, ∫⁻ t in Ioc 0 T, ‖if (t : WithTop ℝ≥0) ≤
        TauCeti.nnvolume.energyLocalizer H C ω then
          TauCeti.nnvolume.finiteEnergyCutoff H t ω else 0‖ₑ ^ 2 ∂TauCeti.nnvolume ∂P :=
      lintegral_prod_symm _ (hm.eNorm.pow_const 2)
    _ ≤ ∫⁻ _ : Ω, (C : ℝ≥0∞) ∂P :=
      lintegral_mono (TauCeti.nnvolume.setLIntegral_enorm_sq_ite_le_energyLocalizer_le H C T)
    _ < ∞ := by simp [ENNReal.mul_lt_top, measure_lt_top]

namespace TauCeti.LocallyBrownianIntegrable

/-- The original accumulated energy is finite on all finite horizons on one common
sample-full event. This uses the lower square integral, not a Bochner fallback value. -/
theorem ae_accumulatedEnergy_lt_top (hH : LocallyBrownianIntegrable ℱ P H) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, nnvolume.accumulatedEnergy H T ω < ∞ := by
  filter_upwards [hH.ae_memLp] with ω hω T
  have hfinite := (hω T).aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.mp (hω T)
  rw [Probability.timeMeasure_def, ← nnvolume_def] at hfinite
  simpa only [nnvolume.accumulatedEnergy_eq_setLIntegral_Ioc] using hfinite

/-- Positive integer closed energy levels yield a native localizing sequence on the raw
filtration. The stopping times are increasing everywhere and tend to infinity almost surely. -/
theorem isLocalizingSequence_energyLocalizer (hH : LocallyBrownianIntegrable ℱ P H) :
    IsLocalizingSequence ℱ (fun n : ℕ ↦ nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)) P where
  isStoppingTime n := hH.isStronglyPredictable.isStoppingTime_energyLocalizer nnvolume _
  mono := Eventually.of_forall fun ω ↦ (nnvolume.monotone_energyLocalizer H ω).comp
    (fun _ _ hij ↦ add_le_add (Nat.cast_le.mpr hij) le_rfl)
  tendsto_top := by
    filter_upwards [hH.ae_accumulatedEnergy_lt_top] with ω hω
    apply (nnvolume.tendsto_energyLocalizer H ω hω).comp
    exact tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop

/-- On one sample-full event and each finite horizon, the closed-level stopped cutoffs
eventually recover the original integrand everywhere on that horizon. -/
theorem ae_eventually_ite_le_energyLocalizer_eqOn (hH : LocallyBrownianIntegrable ℱ P H) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n : ℕ in atTop,
      EqOn (fun t : ℝ≥0 ↦ if (t : WithTop ℝ≥0) ≤
        nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω then
        nnvolume.finiteEnergyCutoff H t ω else 0) (fun t ↦ H t ω) (Iic T) := by
  filter_upwards [hH.ae_accumulatedEnergy_lt_top,
    hH.isLocalizingSequence_energyLocalizer.tendsto_top] with ω hfinite hlim T
  filter_upwards [(WithTop.tendsto_nhds_top_iff _).mp hlim T] with n hn
  intro t ht
  have htime : t ≤ T := ht
  have hle : (t : WithTop ℝ≥0) ≤ nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω :=
    (WithTop.coe_le_coe.mpr htime).trans hn.le
  simpa only [ite_eq_left hle] using nnvolume.finiteEnergyCutoff_eqOn (hfinite T) ht

/-- Stopping a locally Brownian-integrable integrand directly at any closed energy level yields a
Brownian-integrable process under a finite sample measure, without needing `finiteEnergyCutoff`. -/
theorem brownianIntegrable_ite_le_energyLocalizer [IsFiniteMeasure P]
    (hH : LocallyBrownianIntegrable ℱ P H) (C : ℝ≥0) :
    BrownianIntegrable ℱ P
      (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ nnvolume.energyLocalizer H C ω then H t ω else 0) := by
  refine brownianIntegrable_iff_timeMeasure.2
    ⟨hH.isStronglyPredictable.ite_le
      (hH.isStronglyPredictable.isStoppingTime_energyLocalizer nnvolume C), fun T ↦
      (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer C).memLp T
        |>.ae_eq ?_⟩
  filter_upwards
    [Measure.quasiMeasurePreserving_fst.tendsto_ae (Probability.ae_mem_Ioc_timeMeasure T),
      Measure.quasiMeasurePreserving_snd.tendsto_ae hH.ae_accumulatedEnergy_lt_top] with p ht hfin
  dsimp only [Function.uncurry]
  split_ifs; exacts [nnvolume.finiteEnergyCutoff_eqOn (hfin T) ht.2, rfl]

/-- Along the integer closed-level energy localizers, the pathwise square-energy error on each
finite horizon tends to zero in measure under a finite sample measure. -/
theorem tendsto_measure_lintegral_energyLocalizer [IsFiniteMeasure P]
    (hH : LocallyBrownianIntegrable ℱ P H) (T : ℝ≥0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ P {ω | ε ≤ ∫⁻ s,
      ‖(if (s : WithTop ℝ≥0) ≤ nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω then
          H s ω else 0) - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure T}) atTop (𝓝 0) :=
  tendsto_measure_lintegral_ite_le_pow_of_tendsto_measure_le
    (hH.isLocalizingSequence_energyLocalizer.toIsPreLocalizingSequence.tendsto_measure_le T)
    H ((Probability.ae_mem_Ioc_timeMeasure T).mono fun _ hs ↦ hs.2) two_ne_zero hε

end TauCeti.LocallyBrownianIntegrable
