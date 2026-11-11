/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Countdown.Basic
public import TauCeti.MeasureTheory.Integral.Lebesgue.Encard
public import Mathlib.Probability.Kernel.Invariance

/-!
# The invariant tail measure of a countdown chain

The countdown chain with reset law `μ` has an invariant measure assigning mass `μ [j, ∞)`
to state `j`. Its total mass is the extended mean of the reset plus one. Consequently it
can be normalized to an invariant probability exactly when this mean is finite. This gives
the explicit equilibrium weights used for arithmetic renewal limits, without a moment
assumption in the unnormalized balance identity.

The measure is concentrated on the natural countdown states. At zero its mass is one,
including when the reset is identically zero; the normalized zero mass is the inverse
mean gap.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition (1971), Chapter XI, the residual-life chain for arithmetic renewals.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- The tail measure of a countdown reset law: state `j` has mass `μ [j, ∞)`. -/
def countdownInvariantMeasure (μ : Measure ℕ) : Measure ℕ :=
  Measure.sum fun j => μ (Ici j) • dirac j

/-- Singleton masses of the countdown tail measure. -/
@[simp] theorem countdownInvariantMeasure_singleton (μ : Measure ℕ) (j : ℕ) :
    μ.countdownInvariantMeasure {j} = μ (Ici j) :=
  sum_smul_dirac_singleton

/-- Evaluation of the countdown tail measure on an arbitrary set. -/
theorem countdownInvariantMeasure_apply (μ : Measure ℕ) (s : Set ℕ) :
    μ.countdownInvariantMeasure s = ∑' j : s, μ (Ici (j : ℕ)) := by
  simpa using (tsum_measure_preimage_singleton (μ := μ.countdownInvariantMeasure)
    (f := id) (to_countable s) (fun j _ => measurableSet_singleton j)).symm

/-- The invariant tail measure depends measurably on the reset law. -/
@[fun_prop] theorem measurable_countdownInvariantMeasure :
    Measurable countdownInvariantMeasure := by
  apply Measure.measurable_measure.mpr
  intro s _
  simp_rw [countdownInvariantMeasure_apply]
  exact Measurable.tsum fun j => Measure.measurable_coe measurableSet_Ici

/-- The countdown tail measure charges only natural countdown states. -/
@[simp] theorem countdownInvariantMeasure_compl_countdownStates (μ : Measure ℕ) :
    μ.countdownInvariantMeasure μ.countdownStatesᶜ = 0 := by
  rw [countdownInvariantMeasure_apply]
  apply tsum_eq_zero_iff.mpr
  intro j
  have hj := j.property
  rw [Set.mem_compl_iff, mem_countdownStates] at hj
  exact nonpos_iff_eq_zero.mp (not_lt.mp hj)

/-- The total mass is the extended mean of one plus the reset, allowing infinite means. -/
theorem countdownInvariantMeasure_univ (μ : Measure ℕ) :
    μ.countdownInvariantMeasure univ = ∫⁻ j, (j + 1 : ℝ≥0∞) ∂μ := by
  have hcard (j : ℕ) : ({k : ℕ | k ≤ j}.encard : ℝ≥0∞) = j + 1 := by
    simp_rw [← Nat.lt_succ_iff, Set.Nat.encard_range]
    simp
  calc
    μ.countdownInvariantMeasure univ = ∑' k : ℕ, μ {j | k ≤ j} := by
      rw [countdownInvariantMeasure_apply]
      exact tsum_univ (fun k : ℕ => μ (Ici k))
    _ = ∫⁻ j, ({k : ℕ | k ≤ j}.encard : ℝ≥0∞) ∂μ :=
      (lintegral_encard_setOf_eq_tsum μ (fun _ => (to_countable _).measurableSet)).symm
    _ = _ := lintegral_congr hcard

/-- Each state has finite tail mass for finite reset laws, even with infinite first moment. -/
instance (μ : Measure ℕ) [IsFiniteMeasure μ] : SigmaFinite μ.countdownInvariantMeasure := by
  exact Measure.sigmaFinite_iff_measure_singleton_lt_top.mpr (fun j => by simp)

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

/-- Balance for the countdown chain: reset inflow plus deterministic inflow equals the tail. -/
theorem invariant_countdownInvariantMeasure :
    μ.countdownKernel.Invariant μ.countdownInvariantMeasure := by
  apply (Measure.ext_iff_singleton).2
  intro j
  rw [Measure.bind_apply (measurableSet_singleton j) μ.countdownKernel.measurable.aemeasurable,
    lintegral_countable', tsum_eq_zero_add' (by exact CompleteLattice.summable)]
  simp only [countdownKernel_zero, countdownKernel_succ, countdownInvariantMeasure_singleton]
  have hinflow : (∑' k : ℕ, dirac k {j} * μ (Ici (k + 1))) = μ (Ici (j + 1)) := by
    rw [tsum_eq_single j]
    · simp
    · intro k hk
      simp [hk]
  rw [hinflow]
  have hzero : μ (Ici 0) = 1 := by simp
  rw [hzero, mul_one]
  have hs : ({j} : Set ℕ) ∪ Ici (j + 1) = Ici j := by
    ext k
    simp only [mem_union, mem_singleton_iff, mem_Ici]
    omega
  rw [← hs, measure_union (by simp) (measurableSet_Ici)]

omit [IsProbabilityMeasure μ] in
/-- Finite mean is exactly finiteness of the total invariant tail mass. -/
theorem isFiniteMeasure_countdownInvariantMeasure_iff :
    IsFiniteMeasure μ.countdownInvariantMeasure ↔ ∫⁻ j, (j + 1 : ℝ≥0∞) ∂μ < ∞ := by
  rw [← countdownInvariantMeasure_univ]
  exact ⟨fun _ => measure_lt_top _ _, fun h => ⟨h⟩⟩

/-- Scaling the tail measure by the inverse mean gives a probability exactly for finite mean.
For infinite mean the inverse is zero, so this scaling is the zero measure instead. -/
theorem isProbabilityMeasure_inv_mean_smul_countdownInvariantMeasure_iff :
    IsProbabilityMeasure ((∫⁻ j, (j + 1 : ℝ≥0∞) ∂μ)⁻¹ • μ.countdownInvariantMeasure) ↔
      ∫⁻ j, (j + 1 : ℝ≥0∞) ∂μ ≠ ∞ := by
  constructor
  · intro h htop
    have hmass := h.measure_univ
    simp [htop] at hmass
  · intro hμ
    constructor
    rw [smul_apply, smul_eq_mul, countdownInvariantMeasure_univ]
    apply ENNReal.inv_mul_cancel _ hμ
    have hpos : 1 ≤ ∫⁻ j, (j + 1 : ℝ≥0∞) ∂μ := by
      calc
        1 = ∫⁻ _ : ℕ, (1 : ℝ≥0∞) ∂μ := by simp
        _ ≤ _ := lintegral_mono fun j => le_add_left le_rfl
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hpos)

/-- The normalized tail measure satisfies the stationarity equation. -/
theorem invariant_inv_mean_smul_countdownInvariantMeasure :
    μ.countdownKernel.Invariant
      ((∫⁻ j, (j + 1 : ℝ≥0∞) ∂μ)⁻¹ • μ.countdownInvariantMeasure) := by
  rw [Kernel.Invariant, Measure.comp_smul, μ.invariant_countdownInvariantMeasure.def]

omit [IsProbabilityMeasure μ] in
/-- The total invariant mass for a positive integer gap law is its extended first moment. -/
theorem countdownInvariantMeasure_map_pred_univ (hμ : μ {0} = 0) :
    (μ.map Nat.pred).countdownInvariantMeasure univ = ∫⁻ j, (j : ℝ≥0∞) ∂μ := by
  rw [countdownInvariantMeasure_univ,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  apply lintegral_congr_ae
  have hpos : ∀ᵐ n ∂μ, n ≠ 0 := by
    apply ae_iff.mpr
    simpa using hμ
  filter_upwards [hpos] with n hn
  norm_cast
  exact Nat.succ_pred_eq_of_ne_zero hn

end MeasureTheory.Measure
