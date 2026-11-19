/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Markov decision processes and the expected next value

A Markov decision process `M : MDP S A` with state type `S` and action type `A` consists of a
transition law `M.trans s a : PMF S` and a mean reward `M.reward s a : ℝ`, bounded in absolute
value by `M.rewardBound`. Value functions of a discounted MDP live in the Banach space
`BoundedFn S` of bounded real functions on `S` with the sup norm, which is Mathlib's
`lp (fun _ : S ↦ ℝ) ∞`.

The basic operation shared by every Bellman operator is the expected next value
`M.expect v s a = ∫ v ∂(M.trans s a)`. This file proves its elementary properties: its value on
constants and on deterministic transitions, linearity and monotonicity for integrable functions,
and the bound `|M.expect v s a| ≤ ‖v‖` for bounded `v`, which gives the one-step bound
`|M.reward s a + γ M.expect v s a| ≤ M.rewardBound + γ ‖v‖` keeping the Bellman operators inside
`BoundedFn S`.

On a countable state space with measurable singletons every function is measurable, so every
bounded function is integrable for every transition law (`MDP.integrable_trans`).

The file also proves Blackwell's sufficient conditions
(`TauCeti.lipschitzWith_of_mono_of_le_add_const`): a monotone operator on `BoundedFn ι` that
raises by at most `γ c` when its argument is raised by a constant `c ≥ 0` is `γ`-Lipschitz. The
Bellman operators are contractions for this reason.

## References

* D. Blackwell, *Discounted dynamic programming*, Ann. Math. Statist. **36** (1965), 226–235,
  Theorem 5.

* M. L. Puterman, *Markov decision processes: discrete stochastic dynamic programming*, Wiley,
  1994, Sections 2.1 and 6.1.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

/-- The Banach space of bounded real functions on `ι` with the sup norm: Mathlib's `lp` space of
real families with exponent `∞`. -/
abbrev BoundedFn (ι : Type*) : Type _ := lp (fun _ : ι ↦ ℝ) ∞

/-- A Markov decision process with states `S` and actions `A`: in state `s`, the action `a` earns
the mean reward `reward s a` and moves to a state drawn from `trans s a`. The rewards are bounded
in absolute value by `rewardBound`. -/
structure MDP (S A : Type*) where
  /-- The law of the next state after playing the action `a` in the state `s`. -/
  trans : S → A → PMF S
  /-- The mean reward of playing the action `a` in the state `s`. -/
  reward : S → A → ℝ
  /-- A bound on the absolute values of the rewards. -/
  rewardBound : ℝ
  /-- The rewards are bounded in absolute value by `rewardBound`. -/
  abs_reward_le : ∀ s a, |reward s a| ≤ rewardBound

/-- Adding `c • 1` to a bounded function raises each of its values by the constant `c`. -/
theorem BoundedFn.coeFn_add_smul_one {ι : Type*} (v : BoundedFn ι) (c : ℝ) :
    ⇑(v + c • 1) = fun i ↦ v i + c := by
  ext i
  simp only [lp.coeFn_add, lp.coeFn_smul, lp.infty_coeFn_one, Pi.add_apply, Pi.smul_apply,
    Pi.one_apply, smul_eq_mul, mul_one]

/-- **Blackwell's sufficient conditions.** An operator on the bounded functions that is monotone
and raises by at most `γ * c` when its argument is raised by the constant `c ≥ 0` is
`γ`-Lipschitz for the sup norm. -/
theorem lipschitzWith_of_mono_of_le_add_const {ι : Type*} {γ : ℝ≥0}
    {T : BoundedFn ι → BoundedFn ι}
    (mono : ∀ ⦃v w : BoundedFn ι⦄, (∀ i, v i ≤ w i) → ∀ i, T v i ≤ T w i)
    (le_add_const : ∀ (v : BoundedFn ι) (c : ℝ), 0 ≤ c → ∀ i, T (v + c • 1) i ≤ T v i + γ * c) :
    LipschitzWith γ T := by
  have key (v w : BoundedFn ι) (i : ι) : T v i - T w i ≤ γ * ‖v - w‖ := by
    have hle (j : ι) : v j ≤ (w + ‖v - w‖ • 1 : BoundedFn ι) j := by
      have h := lp.norm_apply_le_norm ENNReal.top_ne_zero (v - w) j
      simp only [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] at h
      rw [BoundedFn.coeFn_add_smul_one]
      linarith [le_abs_self (v j - w j)]
    linarith [mono hle i, le_add_const w ‖v - w‖ (norm_nonneg _) i]
  refine LipschitzWith.of_dist_le_mul fun v w ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  refine lp.norm_le_of_forall_le (by positivity) fun i ↦ ?_
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  exact ⟨key v w i, norm_sub_rev v w ▸ key w v i⟩

namespace MDP

variable {S A : Type*} (M : MDP S A)

/-- The reward bound is nonnegative as soon as there is a state and an action. -/
theorem rewardBound_nonneg [Nonempty S] [Nonempty A] : 0 ≤ M.rewardBound :=
  (abs_nonneg _).trans (M.abs_reward_le (Classical.arbitrary S) (Classical.arbitrary A))

variable [MeasurableSpace S]

/-- The expected next value `∫ v ∂(trans s a)` of a function `v` on the states, after playing
the action `a` in the state `s`. -/
def expect (v : S → ℝ) (s : S) (a : A) : ℝ :=
  ∫ s', v s' ∂(M.trans s a).toMeasure

/-- The defining formula of the expected next value. -/
theorem expect_def (v : S → ℝ) (s : S) (a : A) :
    M.expect v s a = ∫ s', v s' ∂(M.trans s a).toMeasure := (rfl)

/-- The expected next value of a constant is that constant. -/
@[simp]
theorem expect_const (c : ℝ) (s : S) (a : A) : M.expect (fun _ ↦ c) s a = c := by
  simp [expect_def]

/-- The expected next value of `0` is `0`. -/
@[simp]
theorem expect_zero (s : S) (a : A) : M.expect 0 s a = 0 :=
  M.expect_const 0 s a

/-- The expected next value of `1` is `1`. -/
@[simp]
theorem expect_one (s : S) (a : A) : M.expect 1 s a = 1 :=
  M.expect_const 1 s a

/-- After a deterministic transition to `s'`, the expected next value is the value at `s'`. -/
theorem expect_of_trans_eq_pure [MeasurableSingletonClass S] {v : S → ℝ} {s s' : S} {a : A}
    (h : M.trans s a = PMF.pure s') : M.expect v s a = v s' := by
  rw [expect_def, h, PMF.toMeasure_pure, integral_dirac]

/-- The expected next value of a bounded function is bounded by its sup norm. -/
theorem abs_expect_le (v : BoundedFn S) (s : S) (a : A) : |M.expect v s a| ≤ ‖v‖ := by
  simpa [expect_def] using norm_integral_le_of_norm_le_const (μ := (M.trans s a).toMeasure)
    (ae_of_all _ fun s' ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero v s')

/-- The one-step bound: the reward plus the discounted expected next value of a bounded function
is bounded by `rewardBound + γ ‖v‖`. -/
theorem abs_reward_add_expect_le (γ : ℝ≥0) (v : BoundedFn S) (s : S) (a : A) :
    |M.reward s a + γ * M.expect v s a| ≤ M.rewardBound + γ * ‖v‖ := by
  calc |M.reward s a + γ * M.expect v s a|
      ≤ |M.reward s a| + |(γ : ℝ) * M.expect v s a| := abs_add_le _ _
    _ ≤ M.rewardBound + γ * ‖v‖ := by
        rw [abs_mul, abs_of_nonneg γ.coe_nonneg]
        exact add_le_add (M.abs_reward_le s a)
          (mul_le_mul_of_nonneg_left (M.abs_expect_le v s a) γ.coe_nonneg)

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

/-- On a countable state space with measurable singletons, a bounded function is integrable for
every transition law. -/
theorem integrable_trans (v : BoundedFn S) (s : S) (a : A) :
    Integrable v (M.trans s a).toMeasure :=
  .of_bound (measurable_of_countable _).aestronglyMeasurable ‖v‖
    (ae_of_all _ fun s' ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero v s')

/-- The expected next value of a bounded function is the weighted sum of its values. -/
theorem expect_eq_tsum (v : BoundedFn S) (s : S) (a : A) :
    M.expect v s a = ∑' s', (M.trans s a s').toReal * v s' := by
  rw [expect_def, PMF.integral_eq_tsum _ _ (M.integrable_trans v s a)]
  rfl

/-- Raising a bounded function by the constant `c` raises its expected next value by `c`. -/
theorem expect_add_smul_one (v : BoundedFn S) (c : ℝ) (s : S) (a : A) :
    M.expect ⇑(v + c • 1) s a = M.expect v s a + c := by
  rw [BoundedFn.coeFn_add_smul_one, M.expect_add_const (M.integrable_trans v s a)]

/-- The expected next values of two bounded functions differ by at most their distance. -/
theorem abs_expect_sub_expect_le (v w : BoundedFn S) (s : S) (a : A) :
    |M.expect v s a - M.expect w s a| ≤ ‖v - w‖ := by
  rw [← M.expect_sub (M.integrable_trans v s a) (M.integrable_trans w s a), ← lp.coeFn_sub]
  exact M.abs_expect_le (v - w) s a

end Countable

/-- On a finite state space, the expected next value is the weighted sum of the values. -/
theorem expect_eq_sum [Fintype S] [MeasurableSingletonClass S] (v : S → ℝ) (s : S) (a : A) :
    M.expect v s a = ∑ s', (M.trans s a s').toReal * v s' := by
  rw [expect_def, PMF.integral_eq_sum]
  rfl

end MDP

end TauCeti
