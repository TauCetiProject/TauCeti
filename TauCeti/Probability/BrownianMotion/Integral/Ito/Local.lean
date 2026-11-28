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
import TauCeti.MeasureTheory.Measure.Prod
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Process.AccumulatedEnergy
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Process.Stopping
import TauCeti.Probability.Process.TimeAverage
import TauCeti.Probability.Process.TimeMeasure

/-!
# Local-martingale property and localized Brownian Itô integration

`TauCeti.LocallyBrownianIntegrable ℱ P H` relaxes `TauCeti.BrownianIntegrable ℱ P H` to predictable
integrands with a.s. finite pathwise square energy on every finite horizon. Building on optional
stopping and localization stability (`TauCeti.Probability.IsItoIntegral.stoppedProcess`,
`stoppedProcess_indist`, `ite_Ioc`, `of_stoppedProcess`) and the `L²` theory
(`TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry`,
`TauCeti.Probability.BrownianMotion.Integral.Ito.L2`), this module establishes:

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

/-! ### Local-martingale property and square compensation -/

namespace IsItoIntegral

private def energyStage (H : ℝ≥0 → Ω → ℝ) (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : WithTop ℝ≥0) ≤ nnvolume.energyLocalizer H ((k : ℝ≥0) + 1) ω then
    nnvolume.finiteEnergyCutoff H t ω else 0

private theorem stoppedProcess_energyStage
    (hW : IsFilteredPreBrownianReal ℱ W P) (hI : IsItoIntegral ℱ P W H I) {k : ℕ}
    (hτ : IsStoppingTime ℱ (nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)))
    (hHs : BrownianIntegrable ℱ P (energyStage H k)) :
    IsItoIntegral ℱ P W (energyStage H k)
      (MeasureTheory.stoppedProcess I (nnvolume.energyLocalizer H ((k : ℝ≥0) + 1))) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine (hI.stoppedProcess hW hτ).congr_integrand hHs.isStronglyPredictable fun T ↦ ?_
  filter_upwards [ae_mem_Ioc_timeMeasure_prod P T,
    (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T)
      (ν := P)).ae hI.locallyBrownianIntegrable.ae_accumulatedEnergy_lt_top] with p hpT hfin
  dsimp only [Function.uncurry, energyStage]
  have hcut : nnvolume.finiteEnergyCutoff H p.1 p.2 = H p.1 p.2 :=
    nnvolume.finiteEnergyCutoff_eqOn (hfin T) hpT.2
  rw [hcut]

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
    (hI.stoppedProcess_energyStage hW (hτ_loc.isStoppingTime k) (hHs k)).martingale hW (hHs k)
      (hprog.stoppedProcess (hτ_loc.isStoppingTime k)).stronglyAdapted
  refine hprog.locally_martingale_of_ae_stopped_eq hτ_loc hmart fun k _ ↦ ?_
  rw [nnvolume.stoppedProcess_indicator_pos_energyLocalizer H I (by positivity)]

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
    (hI.stoppedProcess_energyStage hW (hτ_loc.isStoppingTime k)
      (hHs k)).martingale_sq_sub hW (hHs k)
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
    simp only [MeasureTheory.stoppedProcess_apply]
  rw [hstop_sub, ← hE_eq]
  simp only [energyStage, τ]

end IsItoIntegral

end Probability

/-! ### Localized existence -/

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
  have hI_ito := Probability.IsItoIntegral.of_stoppedProcess hH.isStronglyPredictable hI_cont
    (fun k ↦ (hτ_loc.isStoppingTime k).measurable') hτ_loc.tendsto_top hU_ito hI_stop
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
