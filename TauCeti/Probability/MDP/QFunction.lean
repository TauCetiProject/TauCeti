/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MDP.Bellman
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Q-functions of a discounted Markov decision process

A bounded Q-function is an element `q` of `BoundedFn (S × A)`: a bounded value for each state and
action. For finitely many nonempty actions, `MDP.maxQ q s = ⨆ b, q (s, b)` is the best value of
`q` at the state `s`, and the **Q-Bellman operator**
`M.qBellman γ q (s, a) = M.reward s a + γ * M.expect (maxQ q) s a` is the one-step lookahead of
`maxQ q`. The **optimal Q-function** `M.optimalQ γ` is the limit of the iterates of the Q-Bellman
operator from `0`.

The Q-Bellman operator and the Bellman optimality operator `MDP.bellman` are related by
`maxQ (M.qBellman γ q) = M.bellman γ (maxQ q)`. For `γ < 1` this identity transports the Bellman
optimality equation to Q-functions: the optimal Q-function is the one-step lookahead of the optimal
value, and the optimal value is its maximum over the actions.

## Main results

* `MDP.norm_maxQ_le`, `MDP.lipschitzWith_maxQ`: `maxQ` does not increase the sup norm and is
  `1`-Lipschitz.
* `MDP.maxQ_qBellman`: `maxQ (M.qBellman γ q) = M.bellman γ (maxQ q)`.
* `MDP.contractingWith_qBellman`: for `γ < 1` the Q-Bellman operator is a `γ`-contraction of
  `BoundedFn (S × A)`.
* `MDP.qBellman_optimalQ`, `MDP.qBellman_eq_self_iff`: for `γ < 1` the optimal Q-function is the
  unique fixed point of the Q-Bellman operator; `MDP.tendsto_iterate_qBellman`: the iterates from
  any bounded Q-function converge to it.
* `MDP.optimalQ_apply`: `M.optimalQ γ (s, a) = M.reward s a + γ * M.expect (M.optimalValue γ) s a`.
* `MDP.maxQ_optimalQ`: `maxQ (M.optimalQ γ) = M.optimalValue γ`.
* `MDP.isGreedy_optimalValue_iff`: a deterministic policy is greedy for the optimal value if and
  only if each of its actions maximizes the optimal Q-function.

## References

* C. J. C. H. Watkins and P. Dayan, *Q-learning*, Machine Learning **8** (1992), 279–292,
  Section 2.
* J. N. Tsitsiklis, *Asynchronous stochastic approximation and Q-learning*, Machine Learning
  **16** (1994), 185–202, Section 7.
-/

public section

noncomputable section

open Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.MDP

variable {S A : Type*}

section Finite

variable [Finite A] [Nonempty A]

/-! ### The maximum over the actions -/

private theorem abs_iSup_apply_le (q : BoundedFn (S × A)) (s : S) :
    |⨆ b, q (s, b)| ≤ ‖q‖ := by
  obtain ⟨b, hb⟩ := exists_eq_ciSup_of_finite (f := fun b ↦ q (s, b))
  rw [← hb, ← Real.norm_eq_abs]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero q (s, b)

/-- The state function `s ↦ ⨆ b, q (s, b)` of a bounded Q-function `q`: the largest value of `q`
over the actions at each state. -/
def maxQ (q : BoundedFn (S × A)) : BoundedFn S :=
  ⟨fun s ↦ ⨆ b, q (s, b),
    memℓp_infty ⟨‖q‖, by
      rintro _ ⟨s, rfl⟩
      exact (Real.norm_eq_abs _).trans_le (abs_iSup_apply_le q s)⟩⟩

/-- The value of `maxQ q` at a state is the supremum of `q` over the actions. -/
theorem maxQ_apply (q : BoundedFn (S × A)) (s : S) : maxQ q s = ⨆ b, q (s, b) := (rfl)

/-- Every action value is below the maximum over the actions. -/
theorem le_maxQ (q : BoundedFn (S × A)) (s : S) (a : A) : q (s, a) ≤ maxQ q s := by
  rw [maxQ_apply]
  exact le_ciSup (f := fun b ↦ q (s, b)) (Set.finite_range _).bddAbove a

/-- Bounding the maximum over the actions is equivalent to bounding every action value. -/
theorem maxQ_le_iff (q : BoundedFn (S × A)) (s : S) (c : ℝ) :
    maxQ q s ≤ c ↔ ∀ a, q (s, a) ≤ c := by
  rw [maxQ_apply]
  exact ciSup_le_iff (Set.finite_range _).bddAbove

/-- The maximum over the actions does not increase the sup norm. -/
theorem norm_maxQ_le (q : BoundedFn (S × A)) : ‖maxQ q‖ ≤ ‖q‖ :=
  lp.norm_le_of_forall_le (norm_nonneg q) fun s ↦ by
    rw [Real.norm_eq_abs, maxQ_apply]
    exact abs_iSup_apply_le q s

/-- The maximum over the actions preserves pointwise inequalities. -/
theorem maxQ_mono {q q' : BoundedFn (S × A)} (h : ∀ sa, q sa ≤ q' sa) (s : S) :
    maxQ q s ≤ maxQ q' s :=
  (maxQ_le_iff q s _).2 fun a ↦ (h (s, a)).trans (le_maxQ q' s a)

/-- Raising a Q-function by a constant `c` raises its maximum over the actions by `c`. -/
theorem maxQ_add_smul_one (q : BoundedFn (S × A)) (c : ℝ) :
    maxQ (q + c • 1) = maxQ q + c • 1 := by
  refine lp.ext (funext fun s ↦ ?_)
  simp only [lp.infty_coeFn_add_smul_one, maxQ_apply]
  exact ((OrderIso.addRight c).map_ciSup (Set.finite_range fun b ↦ q (s, b)).bddAbove).symm

private theorem maxQ_sub_le (q q' : BoundedFn (S × A)) (s : S) :
    maxQ q s - maxQ q' s ≤ ‖q - q'‖ := by
  refine sub_le_iff_le_add.2 ((maxQ_le_iff q s _).2 fun a ↦ ?_)
  have h := lp.norm_apply_le_norm ENNReal.top_ne_zero (q - q') (s, a)
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] at h
  linarith [le_abs_self (q (s, a) - q' (s, a)), le_maxQ q' s a]

/-- The maximum over the actions does not increase sup-norm distances. -/
theorem norm_maxQ_sub_le (q q' : BoundedFn (S × A)) : ‖maxQ q - maxQ q'‖ ≤ ‖q - q'‖ := by
  refine lp.norm_le_of_forall_le (norm_nonneg _) fun s ↦ ?_
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  exact ⟨maxQ_sub_le q q' s, norm_sub_rev q q' ▸ maxQ_sub_le q' q s⟩

/-- The maximum over the actions is `1`-Lipschitz for the sup norms. -/
theorem lipschitzWith_maxQ : LipschitzWith 1 (maxQ : BoundedFn (S × A) → BoundedFn S) :=
  LipschitzWith.of_dist_le_mul fun q q' ↦ by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact norm_maxQ_sub_le q q'

/-! ### The Q-Bellman operator -/

variable [MeasurableSpace S] (M : MDP S A)

/-- The Q-Bellman operator `q ↦ ((s, a) ↦ reward s a + γ * expect (maxQ q) s a)`, acting on bounded
Q-functions. -/
def qBellman (γ : ℝ≥0) (q : BoundedFn (S × A)) : BoundedFn (S × A) :=
  ⟨fun sa ↦ M.reward sa.1 sa.2 + γ * M.expect (maxQ q) sa.1 sa.2,
    memℓp_infty ⟨M.rewardBound + γ * ‖maxQ q‖, by
      rintro _ ⟨sa, rfl⟩
      exact (Real.norm_eq_abs _).trans_le (M.abs_reward_add_expect_le γ (maxQ q) sa.1 sa.2)⟩⟩

/-- The value of the Q-Bellman operator at a state and an action. -/
@[simp]
theorem qBellman_apply (γ : ℝ≥0) (q : BoundedFn (S × A)) (s : S) (a : A) :
    M.qBellman γ q (s, a) = M.reward s a + γ * M.expect (maxQ q) s a := (rfl)

/-- At discount zero the Q-Bellman operator returns the immediate reward. -/
theorem qBellman_zero_apply (q : BoundedFn (S × A)) (s : S) (a : A) :
    M.qBellman 0 q (s, a) = M.reward s a := by
  simp

/-- The one-step bound for the Q-Bellman operator: `‖qBellman γ q‖ ≤ rewardBound + γ ‖q‖`. -/
theorem norm_qBellman_le [Nonempty S] (γ : ℝ≥0) (q : BoundedFn (S × A)) :
    ‖M.qBellman γ q‖ ≤ M.rewardBound + γ * ‖q‖ := by
  refine lp.norm_le_of_forall_le' _ fun ⟨s, a⟩ ↦ ?_
  rw [Real.norm_eq_abs, qBellman_apply]
  refine (M.abs_reward_add_expect_le γ (maxQ q) s a).trans ?_
  gcongr
  exact norm_maxQ_le q

/-- The maximum over the actions of the Q-Bellman operator is the Bellman optimality operator
applied to the maximum over the actions. -/
theorem maxQ_qBellman (γ : ℝ≥0) (q : BoundedFn (S × A)) :
    maxQ (M.qBellman γ q) = M.bellman γ (maxQ q) :=
  lp.ext (funext fun s ↦ by simp only [maxQ_apply, qBellman_apply, bellman_apply])

/-- The optimal Q-function, the limit of the iterates of the Q-Bellman operator from `0`. It is
meaningful for `γ < 1`. -/
def optimalQ (γ : ℝ≥0) : BoundedFn (S × A) :=
  limUnder atTop fun k ↦ (M.qBellman γ)^[k] 0

section Countable

variable [Countable S] [MeasurableSingletonClass S]

/-- The Q-Bellman operator preserves pointwise inequalities. -/
theorem qBellman_mono (γ : ℝ≥0) {q q' : BoundedFn (S × A)} (h : ∀ sa, q sa ≤ q' sa) :
    ∀ sa, M.qBellman γ q sa ≤ M.qBellman γ q' sa := by
  rintro ⟨s, a⟩
  simp only [qBellman_apply]
  gcongr
  exact M.expect_mono (M.integrable_trans _ s a) (M.integrable_trans _ s a) (maxQ_mono h)

/-- Raising the argument of the Q-Bellman operator by a constant `c` raises its value by
`γ * c`. -/
theorem qBellman_add_smul_one (γ : ℝ≥0) (q : BoundedFn (S × A)) (c : ℝ) :
    M.qBellman γ (q + c • 1) = M.qBellman γ q + ((γ : ℝ) * c) • 1 := by
  refine lp.ext (funext fun ⟨s, a⟩ ↦ ?_)
  rw [lp.infty_coeFn_add_smul_one (M.qBellman γ q)]
  simp only [qBellman_apply, maxQ_add_smul_one, expect_add_smul_one, mul_add, add_assoc]

/-- The Q-Bellman operator is `γ`-Lipschitz for the sup norm, for every `γ`. -/
theorem lipschitzWith_qBellman (γ : ℝ≥0) : LipschitzWith γ (M.qBellman γ) :=
  lp.lipschitzWith_of_mono_of_le_add_const (fun _ _ h ↦ M.qBellman_mono γ h)
    fun q c _ sa ↦ by rw [qBellman_add_smul_one, lp.infty_coeFn_add_smul_one]

/-- For `γ < 1` the Q-Bellman operator is a `γ`-contraction of the sup norm. -/
theorem contractingWith_qBellman {γ : ℝ≥0} (hγ : γ < 1) : ContractingWith γ (M.qBellman γ) :=
  ⟨hγ, M.lipschitzWith_qBellman γ⟩

variable {γ : ℝ≥0}

/-- The optimal Q-function is the fixed point of the contraction `qBellman γ`. -/
private theorem optimalQ_eq_fixedPoint (hγ : γ < 1) :
    M.optimalQ γ = ContractingWith.fixedPoint _ (M.contractingWith_qBellman hγ) :=
  ((M.contractingWith_qBellman hγ).tendsto_iterate_fixedPoint 0).limUnder_eq

/-- For `γ < 1` the iterates of the Q-Bellman operator from any bounded Q-function converge to the
optimal Q-function. -/
theorem tendsto_iterate_qBellman (hγ : γ < 1) (q : BoundedFn (S × A)) :
    Tendsto (fun k ↦ (M.qBellman γ)^[k] q) atTop (𝓝 (M.optimalQ γ)) := by
  rw [M.optimalQ_eq_fixedPoint hγ]
  exact (M.contractingWith_qBellman hγ).tendsto_iterate_fixedPoint q

/-- **The Bellman optimality equation for Q-functions.** For `γ < 1` the optimal Q-function is a
fixed point of the Q-Bellman operator. -/
theorem qBellman_optimalQ (hγ : γ < 1) : M.qBellman γ (M.optimalQ γ) = M.optimalQ γ := by
  rw [M.optimalQ_eq_fixedPoint hγ]
  exact ContractingWith.fixedPoint_isFixedPt _

/-- For `γ < 1` the optimal Q-function is the unique fixed point of the Q-Bellman operator. -/
theorem qBellman_eq_self_iff (hγ : γ < 1) {q : BoundedFn (S × A)} :
    M.qBellman γ q = q ↔ q = M.optimalQ γ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ M.qBellman_optimalQ hγ⟩
  rw [M.optimalQ_eq_fixedPoint hγ]
  exact ContractingWith.fixedPoint_unique _ h

/-- For `γ < 1` the optimal Q-function is bounded by `rewardBound / (1 - γ)`. -/
theorem norm_optimalQ_le [Nonempty S] (hγ : γ < 1) :
    ‖M.optimalQ γ‖ ≤ M.rewardBound / (1 - γ) :=
  norm_le_div_of_isFixedPt (NNReal.coe_lt_one.2 hγ) (M.norm_qBellman_le γ _)
    (M.qBellman_optimalQ hγ)

end Countable

end Finite

/-! ### The optimal Q-function and the optimal value -/

section Fintype

variable [Fintype A] [Nonempty A] [MeasurableSpace S] (M : MDP S A) [Countable S]
  [MeasurableSingletonClass S] {γ : ℝ≥0}

/-- For `γ < 1` the optimal value is the maximum of the optimal Q-function over the actions. -/
theorem maxQ_optimalQ (hγ : γ < 1) : maxQ (M.optimalQ γ) = M.optimalValue γ :=
  (M.bellman_eq_self_iff hγ).1 (by rw [← maxQ_qBellman, M.qBellman_optimalQ hγ])

/-- For `γ < 1` the optimal Q-function is the one-step lookahead of the optimal value. -/
theorem optimalQ_apply (hγ : γ < 1) (s : S) (a : A) :
    M.optimalQ γ (s, a) = M.reward s a + γ * M.expect (M.optimalValue γ) s a := by
  rw [← M.qBellman_optimalQ hγ, qBellman_apply, M.maxQ_optimalQ hγ]

/-- For `γ < 1` a deterministic policy is greedy for the optimal value if and only if, at every
state, its action maximizes the optimal Q-function. -/
theorem isGreedy_optimalValue_iff (hγ : γ < 1) (π : S → A) :
    M.IsGreedy γ (M.optimalValue γ) π ↔ ∀ s a, M.optimalQ γ (s, a) ≤ M.optimalQ γ (s, π s) := by
  simp only [isGreedy_iff, M.optimalQ_apply hγ]

end Fintype

end TauCeti.MDP
