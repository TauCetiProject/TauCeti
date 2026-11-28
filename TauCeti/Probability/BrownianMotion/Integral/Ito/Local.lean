/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Stopping
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Process.Patching

/-!
# Localizing the Brownian Itô integral process

This file proves the native local-martingale property for strongly progressive Itô integrals
(`TauCeti.Probability.IsItoIntegral.locally_martingale`), constructs predictable almost surely
continuous local-martingale Itô integral processes across `TauCeti.LocallyBrownianIntegrable`
(`TauCeti.LocallyBrownianIntegrable.exists_isItoIntegral`), and characterizes existence of an
Itô integral as `LocallyBrownianIntegrable`
(`TauCeti.Probability.exists_isItoIntegral_iff`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., 1991, §3.2.D.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open Set hiding mem_range
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H I : ℝ≥0 → Ω → ℝ}

namespace Probability.IsItoIntegral

/-- **Local martingale property of the Itô integral.** Every strongly progressive Itô integral
against a filtered pre-Brownian motion is a native local martingale on the raw filtration. -/
theorem locally_martingale (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hProg : IsStronglyProgressive ℱ I) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ I P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hH := hI.locallyBrownianIntegrable; have hτ := hH.isLocalizingSequence_energyLocalizer
  refine hProg.locally_martingale_of_ae_stopped_eq hτ (fun n ↦
    (hI.stoppedProcess hW (hτ.isStoppingTime n)).martingale hW
      (hH.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1))
      (hProg.stoppedProcess (hτ.isStoppingTime n)).stronglyAdapted) fun n t ↦ .of_forall fun ω ↦ by
    rw [stoppedProcess_indicator_comm']
    exact (Set.indicator_of_mem (nnvolume.energyLocalizer_pos H (by positivity) ω) _).symm

end Probability.IsItoIntegral

/-- **Existence of the localized Brownian Itô integral process.** Against a filtered pre-Brownian
motion `W` with almost surely continuous paths, every `LocallyBrownianIntegrable` integrand admits
a predictable almost surely continuous local-martingale Itô integral on the raw filtration. -/
theorem LocallyBrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, Probability.IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ I P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure; have hτ := hH.isLocalizingSequence_energyLocalizer
  choose U hU_ito hU_pred _ using fun n : ℕ ↦
    (hH.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1)).exists_isItoIntegral hW hcont
  obtain ⟨X, hX_prog, hX_cont, hX_stop⟩ := exists_isStronglyProgressive_patch_stoppedProcess
    hτ.tendsto_top (fun n ↦ (hU_pred n).isStronglyProgressive) (fun n ↦ (hU_ito n).ae_continuous)
    fun n m hnm ↦ ((hU_ito m).stoppedProcess hW (hτ.isStoppingTime n)).indist_of_ae_eq hW
      (hU_ito n) fun _ ↦ .of_forall fun ω ↦ .of_forall fun t ↦ by
        have hmono := nnvolume.monotone_energyLocalizer H ω
          (by exact_mod_cast Nat.add_le_add_right hnm 1 : (n : ℝ≥0) + 1 ≤ (m : ℝ≥0) + 1)
        dsimp only; split_ifs with h1 h2 <;> [rfl; exact (h2 (h1.trans hmono)).elim; rfl]
  obtain ⟨I, hI_pred, hIX⟩ :=
    hX_prog.stronglyAdapted.exists_isStronglyPredictable_indist_of_ae_isLeftContinuous
      (hX_cont.mono fun _ hc ↦ hc.isLeftContinuous)
  have hI_ito : Probability.IsItoIntegral ℱ P W H I :=
    Probability.IsItoIntegral.of_seq hH.isStronglyPredictable
      (by filter_upwards [hX_cont, hIX] with _ hc hω using hc.congr fun t ↦ (hω t).symm) hU_ito
      (fun T _ hε ↦ hH.tendsto_measure_lintegral_energyLocalizer T hε) fun T ↦
      tendstoInMeasure_of_tendsto_ae (fun n ↦ ((hU_pred n).isStronglyProgressive.stronglyAdapted T
        |>.mono (ℱ.le T)).aestronglyMeasurable) (by
        filter_upwards [hτ.tendsto_top, hIX, ae_all_iff.2 hX_stop] with ω hlim hIXω hstop
        exact tendsto_const_nhds.congr' <|
          ((WithTop.tendsto_nhds_top_iff _).1 hlim T).mono fun n hn ↦ by
            dsimp only; rw [← hstop n T, stoppedProcess_eq_of_le hn.le, hIXω T])
  exact ⟨I, hI_ito, hI_pred, hI_ito.locally_martingale hW hI_pred.isStronglyProgressive⟩

/-- Against a filtered pre-Brownian motion `W` with almost surely continuous paths, `H` admits an
Itô integral if and only if `H` is `LocallyBrownianIntegrable`. -/
theorem Probability.exists_isItoIntegral_iff
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) :
    (∃ I, Probability.IsItoIntegral ℱ P W H I) ↔ LocallyBrownianIntegrable ℱ P H :=
  ⟨fun ⟨_, hI⟩ ↦ hI.locallyBrownianIntegrable,
    fun hH ↦ let ⟨I, hI, _⟩ := hH.exists_isItoIntegral hW hcont; ⟨I, hI⟩⟩

end TauCeti
