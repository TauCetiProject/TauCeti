/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Countdown.Basic
public import TauCeti.Probability.MarkovChain.Period
public import TauCeti.Probability.Renewal.Lattice.Gap
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Period of the renewal countdown chain

The period at zero of a countdown kernel with reset law `μ` is the gcd of the
integers `k + 1` for which `μ {k} > 0`. The same period holds at every natural
countdown state, both for the ambient chain and for its closed-state restriction.
For a positive integer gap law `ν`, resetting with `ν.map Nat.pred` therefore
gives the gcd of the support of `ν`.

Applied to the positive gaps of a lattice interarrival law, this proves that
maximality of the span implies period one. In particular the countdown kernel on
its natural state space is aperiodic at maximal span, including laws with zero
increments and laws with infinite mean.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*,
  vol. II, second edition (1971), Chapter XI, the residual-life chain for arithmetic renewals.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal ProbabilityTheory

namespace MeasureTheory.Measure

/-- A possible reset to `k` supplies a positive return of length `k + 1`. -/
theorem succ_mem_countdownKernel_returnLengths (μ : Measure ℕ) {k : ℕ}
    (hk : 0 < μ {k}) : k + 1 ∈ μ.countdownKernel.returnLengths 0 := by
  rw [Kernel.mem_returnLengths]
  refine ⟨by omega, ?_⟩
  have hdown : 0 < (μ.countdownKernel ^ k) k {0} := by
    simp [countdownKernel_pow_apply_of_le μ le_rfl]
  simpa [Nat.add_comm] using
    Kernel.pow_add_apply_pos (by simpa using hk : 0 < (μ.countdownKernel ^ 1) 0 {k}) hdown

private theorem dvd_countdownKernel_return (μ : Measure ℕ) {d : ℕ}
    (hd : ∀ k, 0 < μ {k} → d ∣ k + 1) (n : ℕ)
    (hn : 0 < (μ.countdownKernel ^ n) 0 {0}) : d ∣ n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => exact dvd_zero d
    | succ n =>
      -- The first reset is followed either by a full countdown and further returns,
      -- or by a deterministic segment that has not yet reached zero.
      have hsum : 0 < ∑' k, (μ.countdownKernel ^ n) k {0} * μ {k} := by
        rw [Nat.add_comm n 1, Kernel.pow_add_apply_eq_lintegral _ 1 n _
          (measurableSet_singleton 0), pow_one, countdownKernel_zero,
          lintegral_countable'] at hn
        exact hn
      obtain ⟨k, hk⟩ : ∃ k, 0 < (μ.countdownKernel ^ n) k {0} * μ {k} := by
        by_contra h
        simp only [not_exists, not_lt, nonpos_iff_eq_zero] at h
        simp [h] at hsum
      have hreturn := (ENNReal.mul_pos_iff.mp hk).1
      have hreset := (ENNReal.mul_pos_iff.mp hk).2
      have hkn : k ≤ n := by
        by_contra h
        rw [countdownKernel_pow_apply_of_le μ (by omega : n ≤ k)] at hreturn
        simp [Nat.sub_ne_zero_iff_lt.mpr (by omega : n < k)] at hreturn
      have hshort : 0 < (μ.countdownKernel ^ (n - k)) 0 {0} := by
        have heq : k + (n - k) = n := by omega
        rw [← heq, countdownKernel_pow_add_apply] at hreturn
        exact hreturn
      have hdiv := dvd_add (ih (n - k) (by omega) hshort) (hd k hreset)
      convert hdiv using 1
      omega

/-- The period at zero is the gcd of all possible reset values plus one.
No normalization or moment assumption on the reset measure is required. -/
theorem countdownKernel_period_zero (μ : Measure ℕ) :
    μ.countdownKernel.period 0 =
      Nat.setGcd ((fun k : ℕ ↦ k + 1) '' {k | 0 < μ {k}}) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_setGcd_iff.mpr
    rintro _ ⟨k, hk, rfl⟩
    exact Kernel.period_dvd_of_mem_returnLengths (μ.succ_mem_countdownKernel_returnLengths hk)
  · apply Kernel.dvd_period_iff.mpr
    intro n hn
    exact dvd_countdownKernel_return μ
      (fun k hk ↦ Nat.setGcd_dvd_of_mem
        (Set.mem_image_of_mem (fun k : ℕ ↦ k + 1) hk)) n
      (Kernel.mem_returnLengths.mp hn).2

/-- Every natural countdown state has the period computed from the reset support. -/
theorem countdownKernel_period (μ : Measure ℕ) {j : ℕ} (hj : j ∈ μ.countdownStates) :
    μ.countdownKernel.period j =
      Nat.setGcd ((fun k : ℕ ↦ k + 1) '' {k | 0 < μ {k}}) := by
  obtain ⟨n, hn⟩ := ((Kernel.reaches_def 0 j).mp (μ.countdownKernel_zero_reaches hj))
  obtain ⟨m, hm⟩ := ((Kernel.reaches_def j 0).mp (μ.countdownKernel_reaches_zero j))
  exact (Kernel.period_eq_period_of_pos hm hn).trans μ.countdownKernel_period_zero

/-- The period on the closed natural state space is the gcd of the reset values plus one. -/
theorem countdownKernel_subtype_period (μ : Measure ℕ) (j : μ.countdownStates) :
    (μ.countdownKernel.subtype μ.measurableSet_countdownStates).period j =
      Nat.setGcd ((fun k : ℕ ↦ k + 1) '' {k | 0 < μ {k}}) := by
  rw [Kernel.period_subtype _ μ.countdownKernel_isClosedSet]
  exact μ.countdownKernel_period j.property

/-- For positive integer gaps, the countdown period is exactly the gcd of their support. -/
@[simp]
theorem countdownKernel_map_pred_period_zero (ν : Measure ℕ) (hν : ν {0} = 0) :
    (ν.map Nat.pred).countdownKernel.period 0 = Nat.setGcd {n | 0 < ν {n}} := by
  have hpos : ∀ᵐ n ∂ν, n ≠ 0 := by
    apply ae_iff.mpr
    simpa using hν
  have hmap : (ν.map Nat.pred).map Nat.succ = ν := by
    rw [map_map (measurable_of_countable _) (measurable_of_countable _)]
    conv_rhs => rw [← map_id (μ := ν)]
    apply map_congr
    filter_upwards [hpos] with n hn
    exact Nat.succ_pred_eq_of_ne_zero hn
  have hs : (fun k : ℕ ↦ k + 1) '' {k | 0 < (ν.map Nat.pred) {k}} =
      {n | 0 < ν {n}} := by
    ext n
    simp only [mem_ofPred_eq]
    conv_rhs => rw [← hmap]
    rw [map_apply (measurable_of_countable _) (measurableSet_singleton n)]
    cases n <;> simp [Set.preimage, Nat.succ_eq_add_one]
  rw [countdownKernel_period_zero, hs]

/-- A positive integer gap law with support gcd one yields an aperiodic countdown chain
on its natural states. -/
theorem isAperiodic_countdownKernel_map_pred_subtype (ν : Measure ℕ) (hν : ν {0} = 0)
    (hgcd : Nat.setGcd {n | 0 < ν {n}} = 1) :
    ((ν.map Nat.pred).countdownKernel.subtype
      (ν.map Nat.pred).measurableSet_countdownStates).IsAperiodic := by
  rw [Kernel.isAperiodic_iff]
  intro j
  rw [countdownKernel_subtype_period, ← countdownKernel_period_zero,
    ν.countdownKernel_map_pred_period_zero hν, hgcd]

/-- At greatest lattice span, removing zero increments and expressing positive gaps in
integer units gives an aperiodic countdown chain on the natural countdown states. -/
theorem IsLatticeSpan.isAperiodic_countdownKernel_subtype {μ : Measure ℝ≥0}
    [IsProbabilityMeasure μ] {a : ℝ≥0} (ha : μ.IsLatticeSpan a)
    (hmax : IsGreatest {b | μ.IsLatticeSpan b} a) :
    let ν := μ[|{0}ᶜ].map (fun x ↦ ⌊x / a⌋₊)
    ((ν.map Nat.pred).countdownKernel.subtype
      (ν.map Nat.pred).measurableSet_countdownStates).IsAperiodic := by
  apply isAperiodic_countdownKernel_map_pred_subtype
  · simp [ha.map_floor_div_cond_compl_zero_apply_singleton]
  · exact ha.isGreatest_iff_setGcd_map_floor_div_cond_eq_one.mp hmax

end MeasureTheory.Measure
