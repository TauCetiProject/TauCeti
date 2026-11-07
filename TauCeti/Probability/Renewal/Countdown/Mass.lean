/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Countdown.Basic
public import TauCeti.Probability.Renewal.Measure
public import TauCeti.MeasureTheory.Group.Convolution.Nat

/-!
# Renewal masses as countdown return probabilities

For a reset law `μ` on `ℕ`, the countdown chain has positive gap law `μ.map Nat.succ`.
Its time-`n` transition mass at zero, when started at zero, equals the renewal mass at `n`
for that gap law. Both quantities solve the same finite renewal recursion. For probability
reset laws this is a return probability. No moment assumption or aperiodicity is needed.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition (1971), Chapter XI.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- A countdown chain cannot return to zero before its initial countdown is finished. -/
theorem countdownKernel_pow_apply_zero_of_lt (μ : Measure ℕ) {n j : ℕ} (hn : n < j) :
    (μ.countdownKernel ^ n) j {0} = 0 := by
  rw [countdownKernel_pow_apply_of_le μ hn.le]
  simp [Nat.sub_ne_zero_of_lt hn]

/-- Decomposing at the first reset gives the finite renewal recursion for the countdown
chain's zero-state transition masses. -/
theorem countdownKernel_pow_succ_apply_zero (μ : Measure ℕ) (n : ℕ) :
    (μ.countdownKernel ^ (n + 1)) 0 {0} =
      ∑ j ∈ Finset.range (n + 1), μ {j} * (μ.countdownKernel ^ (n - j)) 0 {0} := by
  conv_lhs =>
    rw [Nat.add_comm n 1, Kernel.pow_add_apply_eq_lintegral _ 1 n _ (measurableSet_singleton 0),
      pow_one, countdownKernel_zero, lintegral_countable']
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun j hj ↦ by
    have hjn : n < j := by simpa using hj
    simp [countdownKernel_pow_apply_zero_of_lt μ hjn])]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
  have heq : n = j + (n - j) := by omega
  rw [heq, countdownKernel_pow_add_apply]
  simp [mul_comm]

/-- The renewal measure of a strictly positive integer gap law has unit mass at zero. -/
@[simp] theorem renewalMeasure_map_succ_apply_zero (μ : Measure ℕ) [SFinite μ] :
    (μ.map Nat.succ).renewalMeasure {0} = 1 := by
  have hconv (ν : Measure ℕ) [SFinite ν] : (μ.map Nat.succ ∗ ν) {0} = 0 := by
    have hz : Nat.succ ⁻¹' ({0} : Set ℕ) = ∅ := by ext; simp
    simp [conv_apply_singleton_nat,
      map_apply (measurable_of_countable _) (measurableSet_singleton 0), hz]
  rw [renewalMeasure_eq_dirac_add_conv, _root_.add_apply, hconv]
  simp

/-- The renewal masses of positive integer gaps satisfy a finite recursion with the reset
masses as coefficients. -/
theorem renewalMeasure_map_succ_apply_succ (μ : Measure ℕ) [SFinite μ] (n : ℕ) :
    (μ.map Nat.succ).renewalMeasure {n + 1} =
      ∑ j ∈ Finset.range (n + 1), μ {j} *
        (μ.map Nat.succ).renewalMeasure {n - j} := by
  conv_lhs => rw [renewalMeasure_eq_dirac_add_conv, _root_.add_apply]
  have hd : dirac (0 : ℕ) {n + 1} = 0 := by simp
  rw [hd, zero_add, conv_apply_singleton_nat, Finset.sum_range_succ']
  simp only [map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hz : Nat.succ ⁻¹' ({0} : Set ℕ) = ∅ := by ext; simp
  have hs (j : ℕ) : Nat.succ ⁻¹' ({j + 1} : Set ℕ) = {j} := by ext; simp
  simp only [hz, measure_empty, zero_mul, add_zero, hs, Nat.add_sub_add_right]

/-- The renewal mass of positive integer gaps is the countdown chain's zero-state transition
mass. The artificial renewal at zero corresponds to the chain's initial state. -/
theorem renewalMeasure_map_succ_apply_singleton (μ : Measure ℕ) [SFinite μ] (n : ℕ) :
    (μ.map Nat.succ).renewalMeasure {n} = (μ.countdownKernel ^ n) 0 {0} := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simp [Kernel.one_def, Kernel.id_apply]
    | succ n =>
      rw [renewalMeasure_map_succ_apply_succ, countdownKernel_pow_succ_apply_zero]
      exact Finset.sum_congr rfl fun j hj ↦ by rw [ih (n - j) (by omega)]

/-- For any integer gap law without a zero atom, reset with the gap minus one. Its renewal
mass is the corresponding countdown zero-state transition mass, including time zero. -/
theorem renewalMeasure_apply_singleton_eq_countdownKernel_pow (ν : Measure ℕ) [SFinite ν]
    (hν : ν {0} = 0) (n : ℕ) :
    ν.renewalMeasure {n} = ((ν.map Nat.pred).countdownKernel ^ n) 0 {0} := by
  have hpos : ∀ᵐ j ∂ν, j ≠ 0 := by
    apply ae_iff.mpr
    simpa using hν
  have hmap : (ν.map Nat.pred).map Nat.succ = ν := by
    rw [map_map (measurable_of_countable _) (measurable_of_countable _)]
    conv_rhs => rw [← map_id (μ := ν)]
    apply map_congr
    filter_upwards [hpos] with j hj
    exact Nat.succ_pred_eq_of_ne_zero hj
  simpa only [hmap] using renewalMeasure_map_succ_apply_singleton (ν.map Nat.pred) n

end MeasureTheory.Measure
