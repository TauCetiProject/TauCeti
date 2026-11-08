/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Countdown.Basic
public import TauCeti.Probability.Process.MarkovChain
public import Mathlib.Probability.Process.HittingTime

/-!
# First returns of the renewal countdown chain

For the countdown chain with reset law `μ`, the first entrance to zero at or after time `m`
is almost surely `m + X m`. In particular the positive return time to zero is `1 + X 1`.
Started at zero, `X 1` has law `μ`, so the return time has the law of the reset plus one.
If the reset is obtained by subtracting one from a positive integer gap law, the first return
has exactly that gap law, viewed in `WithTop ℕ`.

These identities identify the return cycles of the residual-life chain with renewal gaps.
They use no bounded-support or moment assumption; the extended return mean can be infinite.
The time-zero entrance and the positive return remain distinct even for the one-state chain.
Law transfer permits the same return-law assertion on arbitrary measurable sample spaces.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition (1971), Chapter XI, the residual-life chain for arithmetic renewals.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory TauCeti.Probability Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

private theorem ae_countdown_step (ν : Measure ℕ) [SFinite ν] :
    ∀ᵐ ω ∂markovChainLaw ν μ.countdownKernel,
      ∀ n, ω n ≠ 0 → ω (n + 1) = ω n - 1 := by
  apply ae_all_iff.2
  intro n
  have hpair : Measurable (fun ω : ℕ → ℕ => (ω n, ω (n + 1))) := by fun_prop
  rw [← ae_map_iff hpair.aemeasurable
    (p := fun z : ℕ × ℕ => z.1 ≠ 0 → z.2 = z.1 - 1)
    (to_countable _).measurableSet, markovChainLaw_map_pair_succ]
  apply (Measure.ae_compProd_iff (to_countable _).measurableSet).2
  apply ae_of_all
  intro j
  cases j <;> simp

/-- The first zero at or after any deterministic time is reached by counting down from the
state at that time. This includes entrance at time zero and allows any s-finite initial
law. -/
theorem ae_hittingAfter_countdownKernel (ν : Measure ℕ) [SFinite ν] (m : ℕ) :
    ∀ᵐ ω ∂markovChainLaw ν μ.countdownKernel,
      hittingAfter (fun n ω => ω n) {0} m ω = ((m + ω m : ℕ) : WithTop ℕ) := by
  filter_upwards [ae_countdown_step μ ν] with ω hω
  have hdown : ∀ k, k ≤ ω m → ω (m + k) = ω m - k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hi := ih (by omega)
      have hpos : ω (m + k) ≠ 0 := by omega
      rw [← Nat.add_assoc, hω (m + k) hpos, hi]
      omega
  apply le_antisymm
  · exact hittingAfter_le_of_mem (Nat.le_add_right _ _) (by simp [hdown _ le_rfl])
  · apply le_of_not_gt
    intro hlt
    obtain ⟨j, ⟨hmj, hj⟩, hj0⟩ := (hittingAfter_lt_iff
      (u := fun n (ω : ℕ → ℕ) => ω n) (i := m + ω m)).1 hlt
    have hd := hdown (j - m) (by omega)
    rw [Nat.add_sub_of_le hmj] at hd
    simp only [mem_singleton_iff] at hj0
    omega

/-- The first positive return to zero has the reset law shifted by one. The codomain retains
infinity, although this return is almost surely finite for every probability reset law. -/
theorem hasLaw_hittingAfter_countdownKernel :
    HasLaw (hittingAfter (fun n (ω : ℕ → ℕ) => ω n) {0} 1)
      (μ.map (fun j => ((j + 1 : ℕ) : WithTop ℕ)))
      (markovChainLaw (dirac 0) μ.countdownKernel) := by
  have heval : HasLaw (fun ω : ℕ → ℕ => ω 1) μ
      (markovChainLaw (dirac 0) μ.countdownKernel) := by
    refine ⟨(measurable_pi_apply 1).aemeasurable, ?_⟩
    rw [Measure.markovChainLaw_map_eval, pow_one,
      Measure.dirac_bind μ.countdownKernel.measurable, countdownKernel_zero]
  have hshift := (hasLaw_map
    (measurable_of_countable (fun j : ℕ => ((j + 1 : ℕ) : WithTop ℕ))).aemeasurable).fun_comp heval
  apply hshift.congr
  filter_upwards [μ.ae_hittingAfter_countdownKernel (dirac 0) 1] with ω hω
  simpa only [Nat.add_comm] using hω

/-- The probability of a positive return at time `j + 1` equals the reset mass at `j`,
including an immediate return when the reset is zero. -/
@[simp] theorem markovChainLaw_countdownKernel_hittingAfter_eq_succ (j : ℕ) :
    markovChainLaw (dirac 0) μ.countdownKernel
      {ω | hittingAfter (fun n (ω : ℕ → ℕ) => ω n) {0} 1 ω = (j : WithTop ℕ) + 1} = μ {j} := by
  rw [(μ.hasLaw_hittingAfter_countdownKernel).measure_eq (measurableSet_singleton _)]
  rw [Measure.map_apply (measurable_of_countable _) (by measurability)]
  congr 1
  ext k
  simp

/-- For a positive integer gap law, resetting with the gap minus one recovers exactly the
original gap law as the positive return-time law. No finite-mean hypothesis is needed. -/
theorem hasLaw_hittingAfter_countdownKernel_map_pred (hμ : μ {0} = 0) :
    HasLaw (hittingAfter (fun n (ω : ℕ → ℕ) => ω n) {0} 1)
      (μ.map (fun j : ℕ => (j : WithTop ℕ)))
      (markovChainLaw (dirac 0) (μ.map Nat.pred).countdownKernel) := by
  have hpos : ∀ᵐ j ∂μ, j ≠ 0 := by
    apply ae_iff.mpr
    simpa using hμ
  have heq : (μ.map Nat.pred).map (fun j => ((j + 1 : ℕ) : WithTop ℕ)) =
      μ.map (fun j : ℕ => (j : WithTop ℕ)) := by
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    apply Measure.map_congr
    filter_upwards [hpos] with j hj
    exact congrArg (fun j : ℕ => (j : WithTop ℕ)) (Nat.succ_pred_eq_of_ne_zero hj)
  rw [← heq]
  exact (μ.map Nat.pred).hasLaw_hittingAfter_countdownKernel

/-- The extended mean positive return time is the extended mean gap. This identity includes
infinite means and uses the return time in `WithTop ℕ`, not a real-valued integral. -/
theorem lintegral_hittingAfter_countdownKernel_map_pred (hμ : μ {0} = 0) :
    ∫⁻ ω, ENat.toENNReal (hittingAfter (fun n (ω : ℕ → ℕ) => ω n) {0} 1 ω)
        ∂markovChainLaw (dirac 0) (μ.map Nat.pred).countdownKernel =
      ∫⁻ j, (j : ℝ≥0∞) ∂μ := by
  rw [(μ.hasLaw_hittingAfter_countdownKernel_map_pred hμ).lintegral_comp
    (f := fun t : WithTop ℕ => ENat.toENNReal t) (measurable_of_countable _).aemeasurable,
    lintegral_map (f := fun t : WithTop ℕ => ENat.toENNReal t)
      (measurable_of_countable _) (measurable_of_countable _)]
  exact lintegral_congr fun j => ENat.toENNReal_coe j

end MeasureTheory.Measure

namespace ProbabilityTheory.HasLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : ℕ → Ω → ℕ} {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- Transfer the countdown first-return law to any measurable realization of its path law. -/
theorem hittingAfter_countdownKernel_map_pred
    (hX : HasLaw (fun ω n => X n ω)
      (markovChainLaw (Measure.dirac 0) (μ.map Nat.pred).countdownKernel) P)
    (hμ : μ {0} = 0) :
    HasLaw (hittingAfter X {0} 1) (μ.map (fun j : ℕ => (j : WithTop ℕ))) P :=
  (μ.hasLaw_hittingAfter_countdownKernel_map_pred hμ).fun_comp hX

end ProbabilityTheory.HasLaw
