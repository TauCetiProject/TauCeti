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

For a real martingale with almost surely continuous paths and nonnegative terminal value,
almost every path with strictly positive terminal value stays strictly positive simultaneously
throughout the finite horizon. Such a path is bounded away from zero on that horizon,
so its reciprocal is bounded there.

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

private theorem Martingale.ae_terminal_pos_imp_forall_pos_of_continuous
    {ℱ : Filtration ℝ≥0 mΩ} (hM : Martingale M ℱ μ) (hc : ∀ ω, Continuous (M · ω))
    (hT : 0 ≤ᵐ[μ] M T) : ∀ᵐ ω ∂μ, 0 < M T ω → ∀ t ≤ T, 0 < M t ω := by
  let τ := hittingAfter M {0} 0
  have hτ : IsStoppingTime ℱ τ :=
    hM.stronglyAdapted.adapted.isStoppingTime_hittingAfter_of_isClosed hc
      (isClosed_singleton) 0
  have hρ := hτ.min_const T
  have hsamp := hM.stoppedValue_ae_eq_condExp_of_le_const_of_ae_isRightContinuous
    (hM.stronglyAdapted.isStronglyProgressive_of_continuous hc)
    (Eventually.of_forall fun ω ↦ (hc ω).isRightContinuous) hρ
    (fun ω ↦ min_le_right (τ ω) (T : WithTop ℝ≥0))
  have hp := (hM.integrable T).ae_pos_imp_condExp_pos hρ.measurableSpace_le hT
  filter_upwards [hsamp, hp] with ω hω hpω hTω t ht
  by_contra h
  obtain ⟨u, hu, hMu⟩ := intermediate_value_Icc ht (hc ω).continuousOn
    (mem_Icc.mpr ⟨le_of_not_gt h, hTω.le⟩)
  have hle : τ ω ≤ T := (isClosed_singleton.hittingAfter_le_iff (hc ω)).mpr
    ⟨u, mem_Icc.mpr ⟨bot_le, hu.2⟩, mem_singleton_iff.mpr hMu⟩
  obtain ⟨v, hv, -, hMv⟩ := isClosed_singleton.exists_hittingAfter_eq (hc ω)
    (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
  have hzero : stoppedValue M (fun ω ↦ min (τ ω) T) ω = 0 :=
    (stoppedValue_of_eq (u := M) (τ := fun ω ↦ min (τ ω) T) (ω := ω)
      ((min_eq_left hle).trans hv)).trans (mem_singleton_iff.mp hMv)
  have hpos := hpω hTω
  rw [← hω, hzero] at hpos
  exact lt_irrefl _ hpos

/-- A real martingale with almost surely continuous paths and nonnegative terminal value
is positive at every time of the horizon on the event where its terminal value is positive,
outside one common null set. Neither completeness nor right continuity of the filtration
is assumed. -/
theorem Martingale.ae_terminal_pos_imp_forall_pos
    {ℱ : Filtration ℝ≥0 mΩ} (hM : Martingale M ℱ μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (M · ω) (Icc 0 T)) (hT : 0 ≤ᵐ[μ] M T) :
    ∀ᵐ ω ∂μ, 0 < M T ω → ∀ t ≤ T, 0 < M t ω := by
  classical
  let G := {ω | ContinuousOn (M · ω) (Icc 0 T)}
  let N : ℝ≥0 → Ω → ℝ := fun t ↦ M (min T t)
  have hN : Martingale N ℱ μ := hM.const_min T
  let Y : ℝ≥0 → NullMeasurableSpace Ω μ → ℝ := fun t ↦ G.indicator (N t)
  have hG (t : ℝ≥0) : MeasurableSet[ℱ.nullAugment μ t] G :=
    (ℱ.measurableSet_nullAugment_iff μ t G).mpr
      ⟨univ, MeasurableSet.univ, ae_eq_univ.mpr hc⟩
  have hYa : StronglyAdapted (ℱ.nullAugment μ) Y := fun t ↦
    ((hN.stronglyMeasurable t).mono (ℱ.le_nullAugment μ t)).indicator (hG t)
  have hYc (ω : NullMeasurableSpace Ω μ) : Continuous (Y · ω) := by
    by_cases hω : ω ∈ G
    · have hcc : ContinuousOn (M · ω) (Icc 0 T) := hω
      have heq : (Y · ω) = (N · ω) := funext fun t ↦ indicator_of_mem hω (N t)
      rw [heq]
      exact hcc.comp_continuous (continuous_const.min continuous_id)
        fun t ↦ ⟨bot_le, min_le_left T t⟩
    · have heq : (Y · ω) = (fun _ ↦ 0) :=
        funext fun t ↦ indicator_of_notMem hω (N t)
      exact heq.symm ▸ continuous_const
  have hYeq : ∀ᵐ ω ∂μ, ∀ t, Y t ω = N t ω :=
    hc.mono fun ω hω t ↦ indicator_of_mem hω (N t)
  have hYM : Martingale Y (ℱ.nullAugment μ) μ.completion :=
    hN.nullAugment.congr hYa fun t ↦
      (hYeq.mono fun _ hω ↦ (hω t).symm).filter_mono μ.ae_completion.le
  have hYT : Y T =ᵐ[μ] M T := hYeq.mono fun ω hω ↦ by
    simpa only [N, min_self] using hω T
  have hpos := hYM.ae_terminal_pos_imp_forall_pos_of_continuous
    (Ω := NullMeasurableSpace Ω μ) (mΩ := inferInstance) hYc
    ((hT.trans_eq hYT.symm).filter_mono μ.ae_completion.le)
  filter_upwards [hpos.filter_mono μ.ae_completion.ge, hYeq, hYT] with ω hω heq hterm hTω t ht
  simpa only [heq t, N, min_eq_right ht] using hω (hterm.symm ▸ hTω) t ht

/-- A real martingale with almost surely continuous paths and positive terminal value
is positive at every time of the horizon, outside one common null set. Neither completeness
nor right continuity of the filtration is assumed. -/
theorem Martingale.ae_forall_pos_of_terminal_pos
    {ℱ : Filtration ℝ≥0 mΩ} (hM : Martingale M ℱ μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (M · ω) (Icc 0 T))
    (hT : ∀ᵐ ω ∂μ, 0 < M T ω) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 < M t ω :=
  hT.mp (hM.ae_terminal_pos_imp_forall_pos hc (hT.mono fun _ h ↦ h.le))

/-- For an almost surely continuous martingale with nonnegative terminal value,
almost every path with positive terminal value has a strictly positive lower bound on the
horizon. The bound may depend on the path. -/
theorem Martingale.ae_terminal_pos_imp_exists_pos_forall_le
    {ℱ : Filtration ℝ≥0 mΩ} (hM : Martingale M ℱ μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (M · ω) (Icc 0 T)) (hT : 0 ≤ᵐ[μ] M T) :
    ∀ᵐ ω ∂μ, 0 < M T ω → ∃ c > 0, ∀ t ≤ T, c ≤ M t ω := by
  filter_upwards [hc, hM.ae_terminal_pos_imp_forall_pos hc hT] with ω hω hpos hTω
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (bot_le : (0 : ℝ≥0) ≤ T)) hω
  exact ⟨M t ω, hpos hTω t ht.2, fun s hs ↦ hmin ⟨bot_le, hs⟩⟩

/-- On each finite horizon a martingale with almost surely continuous paths and positive
terminal value has a pathwise strictly positive lower bound, almost surely. The bound may
depend on the path. -/
theorem Martingale.ae_exists_pos_forall_le_of_terminal_pos
    {ℱ : Filtration ℝ≥0 mΩ} (hM : Martingale M ℱ μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (M · ω) (Icc 0 T))
    (hT : ∀ᵐ ω ∂μ, 0 < M T ω) :
    ∀ᵐ ω ∂μ, ∃ c > 0, ∀ t ≤ T, c ≤ M t ω :=
  hT.mp (hM.ae_terminal_pos_imp_exists_pos_forall_le hc (hT.mono fun _ h ↦ h.le))

end MeasureTheory
