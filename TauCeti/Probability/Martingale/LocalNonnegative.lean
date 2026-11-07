/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Nonnegative local martingales

A strongly adapted nonnegative local martingale with integrable initial value is a
supermartingale. This gives the expectation bound for positive stochastic exponentials
before a separate criterion establishes that they are true martingales.

Locality is Mathlib's `ProbabilityTheory.Locally`: its stopped stages include the indicator
of a strictly positive localizing time. Strong adaptation of the original process is a
separate hypothesis, even on a raw filtration. Nonnegativity holds simultaneously in time
outside one null set, so it also controls randomly stopped values. Neither path regularity
nor usual filtration conditions are needed.

The proof uses Fatou's lemma for integrability and conditional dominated convergence applied
to the minimum of a stopped stage and its limit for the supermartingale inequality.

## References

* Ioannis Karatzas and Steven E. Shreve, *Brownian Motion and Stochastic Calculus*,
  second edition, Chapter 1, §5.
-/

public section

open Filter ProbabilityTheory
open scoped ENNReal Topology

namespace MeasureTheory

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {ℱ : Filtration ι mΩ} {M : ι → Ω → ℝ}

private theorem localStage_tendsto
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P) (t : ι) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ stoppedProcess
      (fun u ↦ {ω | ⊥ < hM.localSeq n ω}.indicator (M u)) (hM.localSeq n) t ω)
      atTop (𝓝 (M t ω)) := by
  filter_upwards [hM.isLocalizingSequence_localSeq.tendsto_top] with ω hω
  have ht := hω.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))
  apply tendsto_const_nhds.congr'
  filter_upwards [ht] with n hn
  rw [stoppedProcess_eq_of_le hn.le, Set.indicator_of_mem]
  exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr bot_le) hn

private theorem localStage_nonneg
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hpos : ∀ᵐ ω ∂P, ∀ t, 0 ≤ M t ω) (n : ℕ) (t : ι) :
    0 ≤ᵐ[P] stoppedProcess
      (fun u ↦ {ω | ⊥ < hM.localSeq n ω}.indicator (M u)) (hM.localSeq n) t := by
  filter_upwards [hpos] with ω hω
  exact Set.indicator_nonneg (fun u _ ↦ hω _) _

private theorem integrable_of_nonneg_localMartingale [SigmaFiniteFiltration P ℱ]
    (hadp : StronglyAdapted ℱ M)
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hpos : ∀ᵐ ω ∂P, ∀ t, 0 ≤ M t ω) (h0 : Integrable (M ⊥) P) (t : ι) :
    Integrable (M t) P := by
  let Y := fun n ↦ stoppedProcess
    (fun u ↦ {ω | ⊥ < hM.localSeq n ω}.indicator (M u)) (hM.localSeq n)
  have hY : ∀ n, Martingale (Y n) ℱ P := hM.stoppedProcess_localSeq
  have hYpos : ∀ n u, 0 ≤ᵐ[P] Y n u := localStage_nonneg hM hpos
  have hbound : ∀ n, eLpNorm (Y n t) 1 P ≤ ENNReal.ofReal (∫ ω, M ⊥ ω ∂P) := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm ((hY n).integrable t).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hY n).integrable t)]
    apply ENNReal.ofReal_le_ofReal
    calc
      ∫ ω, ‖Y n t ω‖ ∂P = ∫ ω, Y n t ω ∂P := by
        apply integral_congr_ae
        filter_upwards [hYpos n t] with ω hω using Real.norm_of_nonneg hω
      _ = ∫ ω, Y n ⊥ ω ∂P := by
        rw [← integral_condExp (ℱ.le ⊥)]
        exact integral_congr_ae ((hY n).condExp_ae_eq bot_le)
      _ ≤ ∫ ω, M ⊥ ω ∂P := by
        apply integral_mono_ae ((hY n).integrable ⊥) h0
        filter_upwards [hpos] with ω hω
        have hbot : (↑(⊥ : ι) : WithTop ι) ≤ hM.localSeq n ω := by simp
        dsimp only [Y]
        rw [stoppedProcess_eq_of_le hbot]
        by_cases hmem : ⊥ < hM.localSeq n ω <;> simp [hmem, hω ⊥]
  -- Fatou bounds the limiting L¹ norm even when the stopped stages are not uniformly integrable.
  have hnorm := Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hbound)
    (fun n ↦ ((hY n).integrable t).aestronglyMeasurable)
    ((hadp t).mono (ℱ.le t)).aestronglyMeasurable (localStage_tendsto hM t)
  exact memLp_one_iff_integrable.mp (hnorm.trans_lt ENNReal.ofReal_lt_top)

/-- A strongly adapted nonnegative native local martingale with integrable initial value is a
supermartingale. Nonnegativity is simultaneous in time, as needed for random-time evaluations;
no continuity or usual conditions on the filtration are assumed. -/
theorem StronglyAdapted.supermartingale_of_locally_martingale_of_nonneg
    [SigmaFiniteFiltration P ℱ] (hadp : StronglyAdapted ℱ M)
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hpos : ∀ᵐ ω ∂P, ∀ t, 0 ≤ M t ω) (h0 : Integrable (M ⊥) P) :
    Supermartingale M ℱ P := by
  have hint := integrable_of_nonneg_localMartingale hadp hM hpos h0
  refine ⟨hadp, ?_, hint⟩
  intro s t hst
  let Y := fun n ↦ MeasureTheory.stoppedProcess
    (fun u ↦ {ω | ⊥ < hM.localSeq n ω}.indicator (M u)) (hM.localSeq n)
  have hY : ∀ n, Martingale (Y n) ℱ P := hM.stoppedProcess_localSeq
  -- These minima are dominated by the now-integrable limit, unlike the stopped stages themselves.
  let f := fun n ω ↦ min (Y n t ω) (M t ω)
  have hfint : ∀ n, Integrable (f n) P := fun n ↦ ((hY n).integrable t).inf (hint t)
  have hfbound : ∀ n, ∀ᵐ ω ∂P, ‖f n ω‖ ≤ M t ω := by
    intro n
    filter_upwards [localStage_nonneg hM hpos n t, hpos] with ω hn hω
    rw [Real.norm_of_nonneg (le_min hn (hω t))]
    exact min_le_right _ _
  have hflim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ f n ω) atTop (𝓝 (M t ω)) := by
    filter_upwards [localStage_tendsto hM t] with ω hω
    simpa only [min_self] using hω.min (tendsto_const_nhds (x := M t ω))
  have hL1 := tendsto_condExpL1_of_dominated_convergence (ℱ.le s) (M t)
    (fun n ↦ (hfint n).aestronglyMeasurable) (hint t) hfbound hflim
  -- An a.e.-convergent subsequence of the conditional expectations suffices for the inequality.
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hL1).exists_seq_tendsto_ae
  have hle : ∀ n, P[f n | ℱ s] ≤ᵐ[P] Y n s := fun n ↦
    (condExp_mono (hfint n) ((hY n).integrable t)
      (Eventually.of_forall fun ω ↦ min_le_left _ _)).trans_eq ((hY n).condExp_ae_eq hst)
  filter_upwards [hlim, ae_all_iff.mpr hle,
    ae_all_iff.mpr (fun n ↦ condExp_ae_eq_condExpL1 (ℱ.le s) (f n)),
    condExp_ae_eq_condExpL1 (ℱ.le s) (M t), localStage_tendsto hM s] with ω hω hleω heq hteq hs
  rw [hteq]
  exact le_of_tendsto_of_tendsto hω (hs.comp hns.tendsto_atTop)
    (Eventually.of_forall fun n ↦ (heq (ns n)).ge.trans (hleω (ns n)))

end MeasureTheory
