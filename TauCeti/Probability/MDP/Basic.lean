/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import TauCeti.Analysis.Normed.Lp.Infty

/-!
# Markov decision processes with bounded rewards

An `MDP` specifies transition probabilities and uniformly bounded real rewards.
`MDP.expect` integrates a next-state value against a transition law. Bounded value
functions live in `BoundedFn S`, Mathlib's `lp` at exponent infinity, so their sup norm controls
every transition expectation. These estimates allow Bellman operators to act on a Banach space.

The expected next value is linear and monotone on integrable functions, and on a countable state
space with measurable singletons every bounded function is integrable for every transition law
(`MDP.integrable_trans`).

The conventions follow M. L. Puterman, *Markov Decision Processes* (1994), §§2.1 and 6.2.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

/-- A Markov decision process with a uniform bound on the absolute reward. -/
structure MDP (S A : Type*) where
  /-- The distribution of the next state after taking an action. -/
  trans : S → A → PMF S
  /-- The mean immediate reward. -/
  reward : S → A → ℝ
  /-- A uniform bound on absolute rewards. -/
  rewardBound : ℝ
  /-- Every immediate reward satisfies the bound. -/
  abs_reward_le : ∀ s a, |reward s a| ≤ rewardBound

namespace MDP

variable {S A : Type*} [MeasurableSpace S] (M : MDP S A)

omit [MeasurableSpace S] in
/-- The reward bound is nonnegative as soon as there is a state and an action. -/
theorem rewardBound_nonneg [Nonempty S] [Nonempty A] : 0 ≤ M.rewardBound :=
  (abs_nonneg _).trans (M.abs_reward_le (Classical.arbitrary S) (Classical.arbitrary A))

/-- The expected next-state value after choosing action `a` at state `s`. -/
def expect (v : S → ℝ) (s : S) (a : A) : ℝ :=
  ∫ t, v t ∂(M.trans s a).toMeasure

/-- Transition expectation is integration against the next-state probability measure. -/
theorem expect_eq_integral (v : S → ℝ) (s : S) (a : A) :
    M.expect v s a = ∫ t, v t ∂(M.trans s a).toMeasure := (rfl)

/-- Transition expectation preserves constants. -/
@[simp]
theorem expect_const (c : ℝ) (s : S) (a : A) : M.expect (fun _ => c) s a = c := by
  simp [expect]

/-- The expected next value of `0` is `0`. -/
@[simp]
theorem expect_zero (s : S) (a : A) : M.expect 0 s a = 0 :=
  M.expect_const 0 s a

/-- The expected next value of `1` is `1`. -/
@[simp]
theorem expect_one (s : S) (a : A) : M.expect 1 s a = 1 :=
  M.expect_const 1 s a

/-- A deterministic transition evaluates the next-state value at its destination. -/
theorem expect_eq_of_trans_eq_pure [MeasurableSingletonClass S] {v : S → ℝ} {s t : S} {a : A}
    (h : M.trans s a = PMF.pure t) : M.expect v s a = v t := by
  simp [expect, h, PMF.toMeasure_pure]

/-- A bounded next-state value has expectation bounded by its sup norm. -/
theorem abs_expect_le (v : BoundedFn S) (s : S) (a : A) :
    |M.expect v s a| ≤ ‖v‖ := by
  simpa [expect] using
    (norm_integral_le_of_norm_le_const (μ := (M.trans s a).toMeasure)
      (Filter.Eventually.of_forall fun t => lp.norm_apply_le_norm ENNReal.top_ne_zero v t))

/-- The one-step discounted reward is uniformly bounded for every nonnegative discount. -/
theorem abs_reward_add_expect_le (γ : ℝ≥0) (v : BoundedFn S) (s : S) (a : A) :
    |M.reward s a + γ * M.expect v s a| ≤ M.rewardBound + γ * ‖v‖ := by
  calc
    _ ≤ |M.reward s a| + |(γ : ℝ) * M.expect v s a| := abs_add_le _ _
    _ ≤ M.rewardBound + γ * ‖v‖ := by
      rw [abs_mul, abs_of_nonneg γ.coe_nonneg]
      gcongr
      · exact M.abs_reward_le s a
      · exact M.abs_expect_le v s a

section Integrable

variable {s : S} {a : A} {v w : S → ℝ}

/-- The expected next value is additive on integrable functions. -/
theorem expect_add (hv : Integrable v (M.trans s a).toMeasure)
    (hw : Integrable w (M.trans s a).toMeasure) :
    M.expect (v + w) s a = M.expect v s a + M.expect w s a :=
  integral_add hv hw

/-- The expected next value commutes with subtraction of integrable functions. -/
theorem expect_sub (hv : Integrable v (M.trans s a).toMeasure)
    (hw : Integrable w (M.trans s a).toMeasure) :
    M.expect (v - w) s a = M.expect v s a - M.expect w s a :=
  integral_sub hv hw

/-- The expected next value is homogeneous. -/
theorem expect_smul (c : ℝ) (v : S → ℝ) : M.expect (c • v) s a = c * M.expect v s a :=
  integral_smul c v

/-- Adding a constant to an integrable function adds it to the expected next value. -/
theorem expect_add_const (hv : Integrable v (M.trans s a).toMeasure) (c : ℝ) :
    M.expect (fun s' ↦ v s' + c) s a = M.expect v s a + c := by
  have h := M.expect_add hv (integrable_const c)
  rwa [M.expect_const] at h

/-- The expected next value is monotone on integrable functions. -/
theorem expect_mono (hv : Integrable v (M.trans s a).toMeasure)
    (hw : Integrable w (M.trans s a).toMeasure) (h : ∀ s', v s' ≤ w s') :
    M.expect v s a ≤ M.expect w s a :=
  integral_mono hv hw h

end Integrable

section Countable

variable [Countable S] [MeasurableSingletonClass S]

/-- Bounded values are integrable for every transition law on a countable state space. -/
theorem integrable_trans (v : BoundedFn S) (s : S) (a : A) :
    Integrable v (M.trans s a).toMeasure :=
  Integrable.of_bound (measurable_of_countable v).aestronglyMeasurable ‖v‖
    (Filter.Eventually.of_forall fun t => lp.norm_apply_le_norm ENNReal.top_ne_zero v t)

/-- The expected next value of a bounded function is the weighted sum of its values. -/
theorem expect_eq_tsum (v : BoundedFn S) (s : S) (a : A) :
    M.expect v s a = ∑' s', (M.trans s a s').toReal * v s' := by
  simp only [expect_eq_integral, PMF.integral_eq_tsum _ _ (M.integrable_trans v s a),
    smul_eq_mul]

/-- Raising a bounded function by the constant `c` raises its expected next value by `c`. -/
theorem expect_add_smul_one (v : BoundedFn S) (c : ℝ) (s : S) (a : A) :
    M.expect ⇑(v + c • 1) s a = M.expect v s a + c := by
  rw [lp.infty_coeFn_add_smul_one, M.expect_add_const (M.integrable_trans v s a)]

/-- A transition law cannot increase the sup-norm distance between bounded values. -/
theorem abs_expect_sub_le (v w : BoundedFn S) (s : S) (a : A) :
    |M.expect v s a - M.expect w s a| ≤ ‖v - w‖ := by
  rw [← M.expect_sub (M.integrable_trans v s a) (M.integrable_trans w s a), ← lp.coeFn_sub]
  exact M.abs_expect_le (v - w) s a

end Countable

/-- On a finite state space, the expected next value is the weighted sum of the values. -/
theorem expect_eq_sum [Fintype S] [MeasurableSingletonClass S] (v : S → ℝ) (s : S) (a : A) :
    M.expect v s a = ∑ s', (M.trans s a s').toReal * v s' := by
  simp only [expect_eq_integral, PMF.integral_eq_sum, smul_eq_mul]

end MDP
end TauCeti
