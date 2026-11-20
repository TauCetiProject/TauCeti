/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Markov decision processes with bounded rewards

An `MDP` specifies transition probabilities and uniformly bounded real rewards.
`MDP.expect` integrates a next-state value against a transition law. Bounded value
functions use Mathlib's `lp` at exponent infinity, so their sup norm controls every
transition expectation. These estimates allow Bellman operators to act on a Banach space.

The conventions follow M. L. Puterman, *Markov Decision Processes* (1994), §§2.1 and 6.2.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

/-- Bounded real functions, equipped with the sup norm. -/
abbrev BoundedFn (S : Type*) := lp (fun _ : S => ℝ) ∞

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

variable [Countable S] [MeasurableSingletonClass S]

/-- Bounded values are integrable for every transition law on a countable state space. -/
theorem integrable_trans (v : BoundedFn S) (s : S) (a : A) :
    Integrable v (M.trans s a).toMeasure :=
  Integrable.of_bound (measurable_of_countable v).aestronglyMeasurable ‖v‖
    (Filter.Eventually.of_forall fun t => lp.norm_apply_le_norm ENNReal.top_ne_zero v t)

/-- Transition expectation is monotone on bounded values. -/
theorem expect_mono {v w : BoundedFn S} (h : ∀ t, v t ≤ w t) (s : S) (a : A) :
    M.expect v s a ≤ M.expect w s a :=
  integral_mono (M.integrable_trans v s a) (M.integrable_trans w s a) h

/-- Transition expectation commutes with subtraction of bounded values. -/
@[simp]
theorem expect_sub (v w : BoundedFn S) (s : S) (a : A) :
    M.expect (v - w) s a = M.expect v s a - M.expect w s a :=
  integral_sub (M.integrable_trans v s a) (M.integrable_trans w s a)

/-- A transition law cannot increase the sup-norm distance between bounded values. -/
theorem abs_expect_sub_le (v w : BoundedFn S) (s : S) (a : A) :
    |M.expect v s a - M.expect w s a| ≤ ‖v - w‖ := by
  rw [← M.expect_sub]
  exact M.abs_expect_le (v - w) s a

end MDP
end TauCeti
