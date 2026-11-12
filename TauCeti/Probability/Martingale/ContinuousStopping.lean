/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Cadlag
public import TauCeti.Probability.Martingale.CountableStopping
public import TauCeti.Probability.Martingale.LpLimit
public import TauCeti.MeasureTheory.Function.ConditionalExpectation.UniformIntegrable
public import TauCeti.Probability.Process.StoppingApproximation

/-!
# Stopping right-continuous martingales on raw filtrations

A strongly progressive martingale with almost surely right-continuous paths remains a
martingale after stopping at any stopping time. No completeness or right continuity of the
filtration is needed. Strong progressivity ensures literal adaptation of the stopped process;
almost sure path regularity alone would not supply that on a raw filtration.

For a martingale with almost surely right-continuous paths, upward dyadic stopping-time
approximations give Lᵖ convergence of the stopped processes at each deterministic observation
time T, assuming only that M T belongs to Lᵖ, for finite p ≥ 1. This convergence requires
neither progressivity nor a pathwise integrable bound. The initial-time indicator form of
martingale stopping retains the convention used by native localization.

Bounded optional sampling for a strongly progressive, almost surely right-continuous
martingale identifies its value at a stopping time τ ≤ T with M T conditioned on the
stopping sigma algebra. For ordered stopping times σ ≤ τ ≤ T, the value at σ is the
conditional expectation of the value at τ given the stopping sigma algebra at σ. Both
stopping times may have arbitrary range.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §3.
-/

public section

noncomputable section

open Filter Set TopologicalSpace
open scoped Topology ENNReal NNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → E} {τ : Ω → WithTop ℝ≥0}

/-- A dyadic stopping time capped at the observation time samples its terminal value. -/
private theorem Martingale.stoppedProcess_dyadicCeilTime_ae_eq_condExp
    (hM : Martingale M ℱ μ) (hτ : IsStoppingTime ℱ τ) (T : ℝ≥0) (n : ℕ) :
    stoppedProcess M (fun ω ↦ TauCeti.dyadicCeilTime n (τ ω)) T =ᵐ[μ]
      μ[M T | ((isStoppingTime_const ℱ T).min (hτ.dyadicCeilTime n)).measurableSpace] := by
  have hc : (range (fun ω ↦ min (T : WithTop ℝ≥0)
      (TauCeti.dyadicCeilTime n (τ ω)))).Countable :=
    ((countable_singleton (T : WithTop ℝ≥0)).mono range_const_subset).range_min
      (TauCeti.countable_range_dyadicCeilTime τ n)
  exact hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    ((isStoppingTime_const ℱ T).min (hτ.dyadicCeilTime n)) (fun _ ↦ min_le_left _ _) hc

/-- For a martingale with almost surely right-continuous paths, upward dyadic stopping-time
approximations give Lᵖ convergence of the stopped processes at each observation time, for
finite p ≥ 1. The moment assumption is only on the value at that observation time.
No progressivity assumption or pathwise integrable bound is needed. -/
theorem Martingale.tendsto_eLpNorm_stoppedProcess_dyadicCeilTime
    (hM : Martingale M ℱ μ)
    (hcont : ∀ᵐ ω ∂μ, IsRightContinuous (fun t ↦ M t ω))
    (hτ : IsStoppingTime ℱ τ) (T : ℝ≥0) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) (hT : MemLp (M T) p μ) :
    Tendsto (fun n ↦ eLpNorm
      (stoppedProcess M (fun ω ↦ TauCeti.dyadicCeilTime n (τ ω)) T -
        stoppedProcess M τ T) p μ) atTop (𝓝 0) := by
  have hui : UniformIntegrable
      (fun n ↦ stoppedProcess M (fun ω ↦ TauCeti.dyadicCeilTime n (τ ω)) T) p μ := by
    exact (hT.uniformIntegrable_condExp hp hp_top (fun n ↦
      ((isStoppingTime_const ℱ T).min (hτ.dyadicCeilTime n)).measurableSpace_le)).ae_eq
        fun n ↦ (hM.stoppedProcess_dyadicCeilTime_ae_eq_condExp hτ T n).symm
  have hlim : ∀ᵐ ω ∂μ, Tendsto
      (fun n ↦ stoppedProcess M (fun ω ↦ TauCeti.dyadicCeilTime n (τ ω)) T ω)
        atTop (𝓝 (stoppedProcess M τ T ω)) :=
    hcont.mono fun ω hω ↦ TauCeti.tendsto_stoppedProcess_dyadicCeilTime M τ T ω
      (continuousWithinAt_Ioi_iff_Ici.1 (hω _))
  have hmem := hui.memLp_of_ae_tendsto hlim
  exact tendsto_Lp_finite_of_tendsto_ae hp hp_top
    (fun n ↦ hui.aestronglyMeasurable n) hmem hui.1 hlim

/-- Stopping a strongly progressive martingale with almost surely right-continuous paths
preserves the martingale property on its original filtration. The stopping time may be
unbounded or infinite. -/
theorem Martingale.stoppedProcess_of_ae_isRightContinuous
    (hM : Martingale M ℱ μ) (hprog : IsStronglyProgressive ℱ M)
    (hcont : ∀ᵐ ω ∂μ, IsRightContinuous (fun t ↦ M t ω))
    (hτ : IsStoppingTime ℱ τ) : Martingale (stoppedProcess M τ) ℱ μ := by
  refine martingale_of_tendsto_eLpNorm_one
    (fun n ↦ hM.stoppedProcess_of_countable_range (hτ.dyadicCeilTime n)
      (TauCeti.countable_range_dyadicCeilTime τ n))
    (hprog.stoppedProcess hτ).stronglyAdapted fun T ↦ ?_
  exact hM.tendsto_eLpNorm_stoppedProcess_dyadicCeilTime hcont hτ T le_rfl
    ENNReal.one_ne_top (memLp_one_iff_integrable.2 (hM.integrable T))

/-- The indicator-stopped martingale used by native localization: a zero stopping time
suppresses the entire path, including a possibly nonzero initial value. -/
theorem Martingale.stoppedProcess_indicator_of_ae_isRightContinuous
    (hM : Martingale M ℱ μ) (hprog : IsStronglyProgressive ℱ M)
    (hcont : ∀ᵐ ω ∂μ, IsRightContinuous (fun t ↦ M t ω))
    (hτ : IsStoppingTime ℱ τ) :
    Martingale (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (M t)) τ) ℱ μ := by
  rw [stoppedProcess_indicator_comm']
  refine (hM.stoppedProcess_of_ae_isRightContinuous hprog hcont hτ).indicator
    (fun t ↦ ℱ.mono bot_le _ ?_)
  simpa only [compl_ofPred, not_le, WithTop.coe_zero] using (hτ 0).compl

/-- For a strongly progressive martingale with almost surely right-continuous paths and a
bounded stopping time τ ≤ T of arbitrary range, `stoppedValue M τ` equals M T conditioned on
`hτ.measurableSpace` almost everywhere. No completion of the filtration is needed. -/
theorem Martingale.stoppedValue_ae_eq_condExp_of_le_const_of_ae_isRightContinuous
    (hM : Martingale M ℱ μ) (hprog : IsStronglyProgressive ℱ M)
    (hcont : ∀ᵐ ω ∂μ, IsRightContinuous (fun t ↦ M t ω))
    (hτ : IsStoppingTime ℱ τ) {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    stoppedValue M τ =ᵐ[μ] μ[M T | hτ.measurableSpace] := by
  have hstop : stoppedProcess M τ T = stoppedValue M τ := by
    ext ω
    simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, min_eq_right (hb ω)]
  have hint : Integrable (stoppedValue M τ) μ := by
    rw [← hstop]
    exact (hM.stoppedProcess_of_ae_isRightContinuous hprog hcont hτ).integrable T
  have hm : StronglyMeasurable[hτ.measurableSpace] (stoppedValue M τ) := by
    borelize E
    exact stronglyMeasurable_iff_measurable_separable.2
      ⟨measurable_stoppedValue hprog hτ,
        (stronglyMeasurable_stoppedValue_of_le hprog hτ hb).isSeparable_range⟩
  refine ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le (hM.integrable T)
    (fun _ _ _ ↦ hint.integrableOn) (fun A hA _ ↦ ?_) hm.aestronglyMeasurable
  have hlim := hM.tendsto_eLpNorm_stoppedProcess_dyadicCeilTime hcont hτ T le_rfl
    ENNReal.one_ne_top (memLp_one_iff_integrable.2 (hM.integrable T))
  rw [hstop] at hlim
  have hsamp (n : ℕ) :
      ∫ ω in A, stoppedProcess M (fun ω ↦ TauCeti.dyadicCeilTime n (τ ω)) T ω ∂μ =
        ∫ ω in A, M T ω ∂μ := by
    have hρ := (isStoppingTime_const ℱ T).min (hτ.dyadicCeilTime n)
    have heq := hM.stoppedProcess_dyadicCeilTime_ae_eq_condExp hτ T n
    have hAρ := hτ.measurableSpace_mono hρ
      (fun ω ↦ le_min (hb ω) (TauCeti.le_dyadicCeilTime n (τ ω))) A hA
    exact (setIntegral_congr_ae (hτ.measurableSpace_le A hA)
      (heq.mono fun _ h _ ↦ h)).trans
        (setIntegral_condExp hρ.measurableSpace_le (hM.integrable T) hAρ)
  exact tendsto_nhds_unique
    (tendsto_setIntegral_of_L1' (stoppedValue M τ)
      (Eventually.of_forall fun n ↦
        (hM.stoppedProcess_of_countable_range (hτ.dyadicCeilTime n)
          (TauCeti.countable_range_dyadicCeilTime τ n)).integrable T) hlim A)
    (by simpa only [hsamp] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ∫ ω in A, M T ω ∂μ) atTop
        (𝓝 (∫ ω in A, M T ω ∂μ))))

/-- Bounded optional sampling at two ordered stopping times. Only the later time needs a
deterministic bound; both times may have uncountable range on the raw filtration. -/
theorem Martingale.stoppedValue_ae_eq_condExp_of_le_of_ae_isRightContinuous
    (hM : Martingale M ℱ μ) (hprog : IsStronglyProgressive ℱ M)
    (hcont : ∀ᵐ ω ∂μ, IsRightContinuous (fun t ↦ M t ω))
    (hτ : IsStoppingTime ℱ τ) {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ)
    (hle : σ ≤ τ) {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    stoppedValue M σ =ᵐ[μ] μ[stoppedValue M τ | hσ.measurableSpace] := by
  have heq := hM.stoppedValue_ae_eq_condExp_of_le_const_of_ae_isRightContinuous
    hprog hcont hτ hb
  exact (hM.stoppedValue_ae_eq_condExp_of_le_const_of_ae_isRightContinuous
    hprog hcont hσ (fun ω ↦ (hle ω).trans (hb ω))).trans
      ((condExp_condExp_of_le (hσ.measurableSpace_mono hτ hle)
        hτ.measurableSpace_le).symm.trans (condExp_congr_ae heq).symm)

end MeasureTheory
