/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Contracting
public import TauCeti.Probability.MarkovDecisionProcess.Basic
public import TauCeti.Probability.ProbabilityMassFunction.Finite
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Bellman operators of a discounted Markov decision process

For an MDP `M` with finitely many actions, a discount factor `γ : ℝ≥0` and a randomized
stationary policy `π : S → PMF A`, this file defines on the bounded functions `BoundedFn S`

* the **Bellman evaluation operator**
  `M.bellmanEval γ π v s = ∑ a, π s a * (M.reward s a + γ * M.expect v s a)`;
* the **Bellman optimality operator**
  `M.bellman γ v s = max_a (M.reward s a + γ * M.expect v s a)`;
* the **value** `M.value γ π` and the **optimal value** `M.optimalValue γ`, the limits of the
  iterates of these operators from `0`;
* the randomized policy `ofDet π` of a deterministic policy `π : S → A`, and the predicate
  `M.IsGreedy γ v π` saying that `π s` maximizes `a ↦ M.reward s a + γ * M.expect v s a` at
  every state.

## Main results

The results up to and including the norm bounds assume a countable state space `S` with
measurable singletons, where every bounded function is integrable for every transition law
(`MDP.integrable_trans`); the greedy-policy results hold for every measurable state space.

* `MDP.bellmanEval_mono`, `MDP.bellman_mono`: both operators are monotone, and
  `MDP.bellmanEval_add_smul_one`, `MDP.bellman_add_smul_one`: raising the argument by a constant
  `c` raises the result by `γ c`.
* `MDP.contractingWith_bellmanEval`, `MDP.contractingWith_bellman`: for `γ < 1` both operators
  are `γ`-contractions of `BoundedFn S`, by Blackwell's sufficient conditions.
* `MDP.bellmanEval_value`, `MDP.bellman_optimalValue`: for `γ < 1` the value is the unique fixed
  point of the evaluation operator (the policy evaluation equation) and the optimal value is the
  unique fixed point of the optimality operator (the Bellman optimality equation);
  `MDP.tendsto_iterate_bellmanEval`, `MDP.tendsto_iterate_bellman`: the iterates from any bounded
  function converge to them.
* `MDP.norm_value_le`, `MDP.norm_optimalValue_le`: both are bounded by `rewardBound / (1 - γ)`.
* `MDP.exists_isGreedy`: every function has a greedy deterministic policy, and
  `MDP.bellmanEval_ofDet_eq_bellman_iff`: the evaluation operator of a deterministic policy
  agrees with the optimality operator at `v` exactly when the policy is greedy for `v`.

The value is defined for every `γ`, but is meaningful only for `γ < 1`, which every statement
about it assumes: for `γ = 1` and the one-state MDP with reward `1`, the iterates `k` of `0` have
no limit.

## References

* M. L. Puterman, *Markov decision processes: discrete stochastic dynamic programming*, Wiley,
  1994, Theorem 6.1.1, Proposition 6.2.4 and Theorem 6.2.5.
* D. Blackwell, *Discounted dynamic programming*, Ann. Math. Statist. **36** (1965), 226–235.
-/

public section

noncomputable section

open Filter Topology
open scoped ENNReal NNReal

namespace TauCeti

namespace MDP

variable {S A : Type*} [MeasurableSpace S] [Fintype A] (M : MDP S A)

/-! ### The Bellman evaluation operator -/

/-- The Bellman evaluation operator of a randomized stationary policy `π` with discount `γ`:
`T^π v s = ∑ a, π s a * (reward s a + γ * expect v s a)`. -/
def bellmanEval (γ : ℝ≥0) (π : S → PMF A) (v : BoundedFn S) : BoundedFn S :=
  ⟨fun s ↦ ∑ a, (π s a).toReal * (M.reward s a + γ * M.expect v s a),
    memℓp_infty ⟨M.rewardBound + γ * ‖v‖, by
      rintro _ ⟨s, rfl⟩
      exact (π s).abs_sum_toReal_mul_le fun a ↦ M.abs_reward_add_expect_le γ v s a⟩⟩

/-- The value of the evaluation operator at a state. -/
@[simp]
theorem bellmanEval_apply (γ : ℝ≥0) (π : S → PMF A) (v : BoundedFn S) (s : S) :
    M.bellmanEval γ π v s = ∑ a, (π s a).toReal * (M.reward s a + γ * M.expect v s a) := (rfl)

/-- The one-step bound for the evaluation operator: `‖T^π v‖ ≤ rewardBound + γ ‖v‖`. -/
theorem norm_bellmanEval_le [Nonempty S] (γ : ℝ≥0) (π : S → PMF A) (v : BoundedFn S) :
    ‖M.bellmanEval γ π v‖ ≤ M.rewardBound + γ * ‖v‖ :=
  lp.norm_le_of_forall_le' _ fun s ↦
    (π s).abs_sum_toReal_mul_le fun a ↦ M.abs_reward_add_expect_le γ v s a

section Countable

variable [Countable S] [MeasurableSingletonClass S]

/-- The evaluation operator is monotone. -/
theorem bellmanEval_mono (γ : ℝ≥0) (π : S → PMF A) {v w : BoundedFn S} (h : ∀ s, v s ≤ w s)
    (s : S) : M.bellmanEval γ π v s ≤ M.bellmanEval γ π w s := by
  simp only [bellmanEval_apply]
  gcongr with a
  exact M.expect_mono (M.integrable_trans v s a) (M.integrable_trans w s a) h

/-- Raising the argument of the evaluation operator by a constant `c` raises its value by
`γ * c`. -/
theorem bellmanEval_add_smul_one (γ : ℝ≥0) (π : S → PMF A) (v : BoundedFn S) (c : ℝ) :
    M.bellmanEval γ π (v + c • 1) = M.bellmanEval γ π v + ((γ : ℝ) * c) • 1 := by
  refine lp.ext (funext fun s ↦ ?_)
  rw [lp.infty_coeFn_add_smul_one (M.bellmanEval γ π v)]
  simp only [bellmanEval_apply, expect_add_smul_one, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, PMF.sum_toReal_eq_one, one_mul, add_assoc]

/-- The evaluation operator is `γ`-Lipschitz for the sup norm, for every `γ`. -/
theorem lipschitzWith_bellmanEval (γ : ℝ≥0) (π : S → PMF A) :
    LipschitzWith γ (M.bellmanEval γ π) :=
  lp.lipschitzWith_of_mono_of_le_add_const (fun _ _ h ↦ M.bellmanEval_mono γ π h)
    fun v c _ s ↦ by rw [bellmanEval_add_smul_one, lp.infty_coeFn_add_smul_one]

/-- For `γ < 1` the evaluation operator is a `γ`-contraction of the sup norm. -/
theorem contractingWith_bellmanEval {γ : ℝ≥0} (hγ : γ < 1) (π : S → PMF A) :
    ContractingWith γ (M.bellmanEval γ π) :=
  ⟨hγ, M.lipschitzWith_bellmanEval γ π⟩

end Countable

/-! ### The Bellman optimality operator -/

variable [Nonempty A]

/-- The one-step bound for the greedy lookahead: the maximum over the actions of
`reward s a + γ * expect v s a` is bounded by `rewardBound + γ ‖v‖`. -/
theorem abs_sup'_reward_add_expect_le (γ : ℝ≥0) (v : BoundedFn S) (s : S) :
    |Finset.univ.sup' Finset.univ_nonempty fun a ↦ M.reward s a + γ * M.expect v s a| ≤
      M.rewardBound + γ * ‖v‖ := by
  obtain ⟨a₀⟩ := ‹Nonempty A›
  exact abs_le.2 ⟨(abs_le.1 (M.abs_reward_add_expect_le γ v s a₀)).1.trans
    (Finset.le_sup' (fun a ↦ M.reward s a + γ * M.expect v s a) (Finset.mem_univ a₀)),
    Finset.sup'_le _ _ fun a _ ↦ (abs_le.1 (M.abs_reward_add_expect_le γ v s a)).2⟩

/-- The Bellman optimality operator with discount `γ`:
`T v s = max_a (reward s a + γ * expect v s a)`. -/
def bellman (γ : ℝ≥0) (v : BoundedFn S) : BoundedFn S :=
  ⟨fun s ↦ Finset.univ.sup' Finset.univ_nonempty fun a ↦ M.reward s a + γ * M.expect v s a,
    memℓp_infty ⟨M.rewardBound + γ * ‖v‖, by
      rintro _ ⟨s, rfl⟩
      exact M.abs_sup'_reward_add_expect_le γ v s⟩⟩

/-- The value of the optimality operator at a state. -/
@[simp]
theorem bellman_apply (γ : ℝ≥0) (v : BoundedFn S) (s : S) :
    M.bellman γ v s =
      Finset.univ.sup' Finset.univ_nonempty fun a ↦ M.reward s a + γ * M.expect v s a := (rfl)

/-- Every action's one-step lookahead is at most the optimality operator. -/
theorem reward_add_expect_le_bellman (γ : ℝ≥0) (v : BoundedFn S) (s : S) (a : A) :
    M.reward s a + γ * M.expect v s a ≤ M.bellman γ v s :=
  Finset.le_sup' (fun a ↦ M.reward s a + γ * M.expect v s a) (Finset.mem_univ a)

/-- The one-step bound for the optimality operator: `‖T v‖ ≤ rewardBound + γ ‖v‖`. -/
theorem norm_bellman_le [Nonempty S] (γ : ℝ≥0) (v : BoundedFn S) :
    ‖M.bellman γ v‖ ≤ M.rewardBound + γ * ‖v‖ :=
  lp.norm_le_of_forall_le' _ fun s ↦ M.abs_sup'_reward_add_expect_le γ v s

/-- The evaluation operator of any policy is at most the optimality operator. -/
theorem bellmanEval_le_bellman (γ : ℝ≥0) (π : S → PMF A) (v : BoundedFn S) (s : S) :
    M.bellmanEval γ π v s ≤ M.bellman γ v s :=
  (π s).sum_toReal_mul_le_of_forall_le fun a ↦ M.reward_add_expect_le_bellman γ v s a

section Countable

variable [Countable S] [MeasurableSingletonClass S]

/-- The optimality operator is monotone. -/
theorem bellman_mono (γ : ℝ≥0) {v w : BoundedFn S} (h : ∀ s, v s ≤ w s) (s : S) :
    M.bellman γ v s ≤ M.bellman γ w s :=
  Finset.sup'_le Finset.univ_nonempty _ fun a _ ↦ le_trans (by
    gcongr
    exact M.expect_mono (M.integrable_trans v s a) (M.integrable_trans w s a) h)
    (M.reward_add_expect_le_bellman γ w s a)

/-- Raising the argument of the optimality operator by a constant `c` raises its value by
`γ * c`. -/
theorem bellman_add_smul_one (γ : ℝ≥0) (v : BoundedFn S) (c : ℝ) :
    M.bellman γ (v + c • 1) = M.bellman γ v + ((γ : ℝ) * c) • 1 := by
  refine lp.ext (funext fun s ↦ ?_)
  rw [lp.infty_coeFn_add_smul_one (M.bellman γ v)]
  simp only [bellman_apply, expect_add_smul_one, Finset.sup'_add, mul_add, add_assoc]

/-- The optimality operator is `γ`-Lipschitz for the sup norm, for every `γ`. -/
theorem lipschitzWith_bellman (γ : ℝ≥0) : LipschitzWith γ (M.bellman γ) :=
  lp.lipschitzWith_of_mono_of_le_add_const (fun _ _ h ↦ M.bellman_mono γ h)
    fun v c _ s ↦ by rw [bellman_add_smul_one, lp.infty_coeFn_add_smul_one]

/-- For `γ < 1` the optimality operator is a `γ`-contraction of the sup norm. -/
theorem contractingWith_bellman {γ : ℝ≥0} (hγ : γ < 1) : ContractingWith γ (M.bellman γ) :=
  ⟨hγ, M.lipschitzWith_bellman γ⟩

end Countable

/-! ### Values -/

omit [Nonempty A] in
/-- The value of a randomized stationary policy, the limit of the iterates of its evaluation
operator from `0`. It is meaningful for `γ < 1`. -/
def value (γ : ℝ≥0) (π : S → PMF A) : BoundedFn S :=
  limUnder atTop fun k ↦ (M.bellmanEval γ π)^[k] 0

/-- The optimal value, the limit of the iterates of the optimality operator from `0`. It is
meaningful for `γ < 1`. -/
def optimalValue (γ : ℝ≥0) : BoundedFn S :=
  limUnder atTop fun k ↦ (M.bellman γ)^[k] 0

section Countable

variable [Countable S] [MeasurableSingletonClass S] {γ : ℝ≥0}

omit [Nonempty A] in
/-- The value is the fixed point of the contraction `T^π`. -/
private theorem value_eq_fixedPoint (hγ : γ < 1) (π : S → PMF A) :
    M.value γ π = ContractingWith.fixedPoint _ (M.contractingWith_bellmanEval hγ π) :=
  ((M.contractingWith_bellmanEval hγ π).tendsto_iterate_fixedPoint 0).limUnder_eq

/-- The optimal value is the fixed point of the contraction `T`. -/
private theorem optimalValue_eq_fixedPoint (hγ : γ < 1) :
    M.optimalValue γ = ContractingWith.fixedPoint _ (M.contractingWith_bellman hγ) :=
  ((M.contractingWith_bellman hγ).tendsto_iterate_fixedPoint 0).limUnder_eq

omit [Nonempty A] in
/-- For `γ < 1` the iterates of the evaluation operator from any bounded function converge to the
value. -/
theorem tendsto_iterate_bellmanEval (hγ : γ < 1) (π : S → PMF A) (v : BoundedFn S) :
    Tendsto (fun k ↦ (M.bellmanEval γ π)^[k] v) atTop (𝓝 (M.value γ π)) := by
  rw [M.value_eq_fixedPoint hγ π]
  exact (M.contractingWith_bellmanEval hγ π).tendsto_iterate_fixedPoint v

/-- For `γ < 1` the iterates of the optimality operator from any bounded function converge to the
optimal value. -/
theorem tendsto_iterate_bellman (hγ : γ < 1) (v : BoundedFn S) :
    Tendsto (fun k ↦ (M.bellman γ)^[k] v) atTop (𝓝 (M.optimalValue γ)) := by
  rw [M.optimalValue_eq_fixedPoint hγ]
  exact (M.contractingWith_bellman hγ).tendsto_iterate_fixedPoint v

omit [Nonempty A] in
/-- **The policy evaluation equation.** For `γ < 1` the value is a fixed point of the evaluation
operator. -/
theorem bellmanEval_value (hγ : γ < 1) (π : S → PMF A) :
    M.bellmanEval γ π (M.value γ π) = M.value γ π := by
  rw [M.value_eq_fixedPoint hγ π]
  exact ContractingWith.fixedPoint_isFixedPt _

/-- **The Bellman optimality equation.** For `γ < 1` the optimal value is a fixed point of the
optimality operator. -/
theorem bellman_optimalValue (hγ : γ < 1) : M.bellman γ (M.optimalValue γ) = M.optimalValue γ := by
  rw [M.optimalValue_eq_fixedPoint hγ]
  exact ContractingWith.fixedPoint_isFixedPt _

omit [Nonempty A] in
/-- For `γ < 1` the value is the unique fixed point of the evaluation operator. -/
theorem bellmanEval_eq_self_iff (hγ : γ < 1) (π : S → PMF A) {v : BoundedFn S} :
    M.bellmanEval γ π v = v ↔ v = M.value γ π := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ M.bellmanEval_value hγ π⟩
  rw [M.value_eq_fixedPoint hγ π]
  exact ContractingWith.fixedPoint_unique _ h

/-- For `γ < 1` the optimal value is the unique fixed point of the optimality operator. -/
theorem bellman_eq_self_iff (hγ : γ < 1) {v : BoundedFn S} :
    M.bellman γ v = v ↔ v = M.optimalValue γ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ M.bellman_optimalValue hγ⟩
  rw [M.optimalValue_eq_fixedPoint hγ]
  exact ContractingWith.fixedPoint_unique _ h

omit [Nonempty A] in
/-- For `γ < 1` the value of every policy is bounded by `rewardBound / (1 - γ)`. -/
theorem norm_value_le [Nonempty S] (hγ : γ < 1) (π : S → PMF A) :
    ‖M.value γ π‖ ≤ M.rewardBound / (1 - γ) :=
  norm_le_div_of_isFixedPt (NNReal.coe_lt_one.2 hγ) (M.norm_bellmanEval_le γ π _)
    (M.bellmanEval_value hγ π)

/-- For `γ < 1` the optimal value is bounded by `rewardBound / (1 - γ)`. -/
theorem norm_optimalValue_le [Nonempty S] (hγ : γ < 1) :
    ‖M.optimalValue γ‖ ≤ M.rewardBound / (1 - γ) :=
  norm_le_div_of_isFixedPt (NNReal.coe_lt_one.2 hγ) (M.norm_bellman_le γ _)
    (M.bellman_optimalValue hγ)

end Countable

/-! ### Deterministic and greedy policies -/

omit [MeasurableSpace S] [Fintype A] [Nonempty A] in
/-- The randomized policy that plays the action `π s` with probability one in the state `s`. -/
def ofDet (π : S → A) : S → PMF A := fun s ↦ PMF.pure (π s)

omit [MeasurableSpace S] [Fintype A] [Nonempty A] in
/-- The defining formula of `ofDet`. -/
@[simp]
theorem ofDet_apply (π : S → A) (s : S) : ofDet π s = PMF.pure (π s) := (rfl)

omit [Nonempty A] in
/-- The evaluation operator of a deterministic policy is its one-step lookahead. -/
theorem bellmanEval_ofDet_apply (γ : ℝ≥0) (π : S → A) (v : BoundedFn S) (s : S) :
    M.bellmanEval γ (ofDet π) v s = M.reward s (π s) + γ * M.expect v s (π s) := by
  classical
  simp [PMF.pure_apply, apply_ite ENNReal.toReal, ite_mul]

omit [Fintype A] [Nonempty A] in
/-- The deterministic policy `π` is greedy for `v` if, in every state `s`, the action `π s`
maximizes the one-step lookahead `a ↦ reward s a + γ * expect v s a`. -/
def IsGreedy (γ : ℝ≥0) (v : S → ℝ) (π : S → A) : Prop :=
  ∀ s a, M.reward s a + γ * M.expect v s a ≤ M.reward s (π s) + γ * M.expect v s (π s)

omit [Fintype A] [Nonempty A] in
/-- The characterization of greedy policies: `π` is greedy for `v` exactly when `π s` maximizes
the one-step lookahead in every state. -/
theorem isGreedy_iff (γ : ℝ≥0) (v : S → ℝ) (π : S → A) :
    M.IsGreedy γ v π ↔
      ∀ s a, M.reward s a + γ * M.expect v s a ≤ M.reward s (π s) + γ * M.expect v s (π s) :=
  Iff.rfl

omit [Fintype A] in
/-- Every function has a greedy deterministic policy. -/
theorem exists_isGreedy [Finite A] (γ : ℝ≥0) (v : S → ℝ) : ∃ π : S → A, M.IsGreedy γ v π := by
  choose π hπ using fun s ↦ Finite.exists_max fun a ↦ M.reward s a + γ * M.expect v s a
  exact ⟨π, (M.isGreedy_iff γ v π).2 hπ⟩

/-- The evaluation operator of a deterministic policy agrees with the optimality operator at `v`
if and only if the policy is greedy for `v`. -/
theorem bellmanEval_ofDet_eq_bellman_iff (γ : ℝ≥0) (π : S → A) (v : BoundedFn S) :
    M.bellmanEval γ (ofDet π) v = M.bellman γ v ↔ M.IsGreedy γ v π := by
  rw [isGreedy_iff]
  refine ⟨fun h s a ↦ ?_, fun h ↦ ?_⟩
  · rw [← M.bellmanEval_ofDet_apply, h]
    exact M.reward_add_expect_le_bellman γ v s a
  · refine lp.ext (funext fun s ↦ ?_)
    rw [M.bellmanEval_ofDet_apply]
    exact le_antisymm (M.reward_add_expect_le_bellman γ v s (π s))
      (Finset.sup'_le Finset.univ_nonempty _ fun a _ ↦ h s a)

end MDP

end TauCeti
