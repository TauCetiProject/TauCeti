/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Function.ConditionalExpectation.Order
public import TauCeti.Probability.Martingale.ContinuousStopping
import TauCeti.Probability.Martingale.NullAugmentation
import TauCeti.Probability.Process.HittingTime

/-!
# Nonattainment of zero for continuous density martingales

A real martingale with almost surely continuous paths and strictly positive terminal value
stays strictly positive simultaneously throughout the finite horizon. In particular, almost
every path is bounded away from zero on that horizon, so its reciprocal is bounded there.

The result holds on a raw filtration. Null augmentation is used only inside the proof to
replace exceptional paths before forming a closed-set hitting time; the conclusion concerns
the original process and measure. Fixed-time positivity alone would not suffice without
path regularity.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 3, §5 (density processes and changes of measure).
-/

public section

open Filter Set ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {M : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

private theorem Martingale.ae_forall_pos_of_terminal_pos_of_continuous
    {ℱ : Filtration ℝ≥0 mΩ} (hM : Martingale M ℱ μ) (hc : ∀ ω, Continuous (M · ω))
    (hT : ∀ᵐ ω ∂μ, 0 < M T ω) : ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 < M t ω := by
  let τ := hittingAfter M {0} 0
  have hτ : IsStoppingTime ℱ τ :=
    hM.stronglyAdapted.adapted.isStoppingTime_hittingAfter_of_isClosed hc
      (isClosed_singleton) 0
  have hρ := hτ.min (isStoppingTime_const ℱ T)
  have hsamp := hM.stoppedValue_ae_eq_condExp_of_le_const_of_ae_isRightContinuous
    (hM.stronglyAdapted.isStronglyProgressive_of_continuous hc)
    (Eventually.of_forall fun ω ↦ (hc ω).isRightContinuous) hρ
    (fun ω ↦ min_le_right (τ ω) (T : WithTop ℝ≥0))
  have hp := (hM.integrable T).condExp_pos hρ.measurableSpace_le hT
  filter_upwards [hsamp, hp, hT] with ω hω hpω hTω
  have hnohit : ¬ τ ω ≤ T := by
    intro hle
    obtain ⟨u, hu, -, hMu⟩ := isClosed_singleton.exists_hittingAfter_eq (hc ω)
      (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
    have hzero : stoppedValue M (fun ω ↦ min (τ ω) T) ω = 0 := by
      simp only [stoppedValue, min_eq_left hle]
      have hτu : τ ω = u := hu
      rw [hτu, WithTop.untopA_eq_untop WithTop.coe_ne_top]
      simpa only [WithTop.untop_coe, mem_singleton_iff] using hMu
    rw [← hω, hzero] at hpω
    exact lt_irrefl _ hpω
  intro t ht
  by_contra h
  obtain ⟨u, hu, hMu⟩ := intermediate_value_Icc ht (hc ω).continuousOn
    (show (0 : ℝ) ∈ Icc (M t ω) (M T ω) from ⟨le_of_not_gt h, hTω.le⟩)
  exact hnohit ((hittingAfter_le_of_mem (bot_le : (0 : ℝ≥0) ≤ u)
    (show M u ω ∈ ({0} : Set ℝ) from hMu)).trans (WithTop.coe_le_coe.mpr hu.2))

/-- A real martingale with almost surely continuous paths and positive terminal value
is positive at every time of the horizon, outside one common null set. Neither completeness
nor right continuity of the filtration is assumed. -/
theorem Martingale.ae_forall_pos_of_terminal_pos
    {ℱ : Filtration ℝ≥0 mΩ} (hM : Martingale M ℱ μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (M · ω) (Icc 0 T))
    (hT : ∀ᵐ ω ∂μ, 0 < M T ω) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 < M t ω := by
  classical
  let G := {ω | ContinuousOn (M · ω) (Icc 0 T)}
  let N := stoppedProcess M (fun _ ↦ (T : WithTop ℝ≥0))
  have hN : Martingale N ℱ μ := hM.stoppedProcess_of_countable_range
    (isStoppingTime_const ℱ T) (countable_singleton _ |>.mono range_const_subset)
  have hNt (t : ℝ≥0) (ω : Ω) : N t ω = M (min t T) ω := by
    simp only [N, stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  let Y : ℝ≥0 → NullMeasurableSpace Ω μ → ℝ := fun t ↦ G.indicator (N t)
  have hG (t : ℝ≥0) : MeasurableSet[ℱ.nullAugment μ t] G :=
    (ℱ.measurableSet_nullAugment_iff μ t G).mpr
      ⟨univ, MeasurableSet.univ, ae_eq_univ.mpr hc⟩
  -- The completion changes the measurable-space instance, not the underlying points.
  let : @IsFiniteMeasure (NullMeasurableSpace Ω μ) _ μ.completion :=
    ⟨lt_of_eq_of_lt (Measure.completion_apply μ univ) (measure_lt_top μ univ)⟩
  have hYa : StronglyAdapted (ℱ.nullAugment μ) Y := fun t ↦
    ((hN.stronglyMeasurable t).mono (ℱ.le_nullAugment μ t)).indicator (hG t)
  have hYc (ω : NullMeasurableSpace Ω μ) : Continuous (Y · ω) := by
    by_cases hω : ω ∈ G
    · have hcc : ContinuousOn (M · ω) (Icc 0 T) := hω
      have heq : (Y · ω) = (fun t ↦ M (min t T) ω) :=
        funext fun t ↦ (indicator_of_mem hω (N t)).trans (hNt t ω)
      rw [heq]
      exact hcc.comp_continuous (continuous_id.min continuous_const)
        fun t ↦ ⟨bot_le, min_le_right t T⟩
    · have heq : (Y · ω) = (fun _ ↦ 0) :=
        funext fun t ↦ indicator_of_notMem hω (N t)
      exact heq.symm ▸ continuous_const
  have hYeq : ∀ᵐ ω ∂μ, ∀ t, Y t ω = N t ω :=
    hc.mono fun ω hω t ↦ indicator_of_mem hω (N t)
  have hYM : Martingale Y (ℱ.nullAugment μ) μ.completion :=
    hN.nullAugment.congr hYa fun t ↦
      (hYeq.mono fun _ hω ↦ (hω t).symm).filter_mono μ.ae_completion.le
  have hYT : ∀ᵐ ω ∂μ.completion, 0 < Y T ω := by
    apply Filter.Eventually.filter_mono μ.ae_completion.le
    filter_upwards [hYeq, hT] with ω hω hpos
    have hNT : N T ω = M T ω := by rw [hNt, min_self]
    exact lt_of_lt_of_eq hpos (hNT.symm.trans (hω T).symm)
  have hpos := hYM.ae_forall_pos_of_terminal_pos_of_continuous
    (Ω := NullMeasurableSpace Ω μ) (mΩ := inferInstance) hYc hYT
  filter_upwards [hpos.filter_mono μ.ae_completion.ge, hYeq] with ω hω heq t ht
  simpa only [heq t, hNt, min_eq_left ht] using hω t ht

/-- On each finite horizon a continuous martingale with positive terminal value has a
pathwise strictly positive lower bound. The bound may depend on the path; no negative
moment or deterministic bound on the reciprocal density is required. -/
theorem Martingale.ae_exists_pos_forall_le_of_terminal_pos
    {ℱ : Filtration ℝ≥0 mΩ} (hM : Martingale M ℱ μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (M · ω) (Icc 0 T))
    (hT : ∀ᵐ ω ∂μ, 0 < M T ω) :
    ∀ᵐ ω ∂μ, ∃ c > 0, ∀ t ≤ T, c ≤ M t ω := by
  filter_upwards [hc, hM.ae_forall_pos_of_terminal_pos hc hT] with ω hω hpos
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (bot_le : (0 : ℝ≥0) ≤ T)) hω
  exact ⟨M t ω, hpos t ht.2, fun s hs ↦ hmin ⟨bot_le, hs⟩⟩

end MeasureTheory
