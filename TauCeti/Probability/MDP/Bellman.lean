/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MDP.Basic
public import TauCeti.Probability.ProbabilityMassFunction.Finite
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Bellman operators of a discounted Markov decision process

For finitely many nonempty actions, the **Bellman optimality operator** `MDP.bellman` maximizes
the one-step discounted reward `M.reward s a + γ * M.expect v s a` over actions. It preserves
boundedness and order and is Lipschitz with the discount as constant. For discounts below one it
is a contraction, allowing Banach's fixed-point theorem to supply the optimality equation. A
greedy deterministic policy exists for every value function and is characterized by attaining the
Bellman maximum.

For a randomized stationary policy `π : S → PMF A`, the **Bellman evaluation operator**
`M.bellmanEval γ π v s = ∑ a, π s a * (M.reward s a + γ * M.expect v s a)` is likewise a
`γ`-contraction, by Blackwell's sufficient conditions. The **value** `M.value γ π` and the
**optimal value** `M.optimalValue γ` are the limits of the iterates of these operators from `0`.

## Main results

* `MDP.contractingWith_bellmanEval`, `MDP.contractingWith_bellman`: for `γ < 1` both operators
  are `γ`-contractions of `BoundedFn S`.
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

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.MDP

section Optimality

variable {S A : Type*} [MeasurableSpace S] [Finite A] [Nonempty A] (M : MDP S A)

private theorem abs_bellman_le (γ : ℝ≥0) (v : BoundedFn S) (s : S) :
    |⨆ a, M.reward s a + γ * M.expect v s a| ≤ M.rewardBound + γ * ‖v‖ := by
  obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite
    (f := fun a => M.reward s a + (γ : ℝ) * M.expect v s a)
  rw [← ha]
  exact M.abs_reward_add_expect_le γ v s a

/-- The maximum one-step discounted reward, acting on bounded value functions. -/
def bellman (γ : ℝ≥0) (v : BoundedFn S) : BoundedFn S :=
  ⟨fun s => ⨆ a, M.reward s a + γ * M.expect v s a,
    memℓp_infty ⟨M.rewardBound + γ * ‖v‖, by
      rintro _ ⟨s, rfl⟩
      exact (Real.norm_eq_abs _).trans_le (M.abs_bellman_le γ v s)⟩⟩

/-- The Bellman operator takes the maximum over the available actions. -/
theorem bellman_apply (γ : ℝ≥0) (v : BoundedFn S) (s : S) :
    M.bellman γ v s = ⨆ a, M.reward s a + γ * M.expect v s a := (rfl)

/-- Every action's one-step discounted reward is below the Bellman value. -/
theorem le_bellman (γ : ℝ≥0) (v : BoundedFn S) (s : S) (a : A) :
    M.reward s a + γ * M.expect v s a ≤ M.bellman γ v s := by
  rw [bellman_apply]
  exact le_ciSup (f := fun a => M.reward s a + (γ : ℝ) * M.expect v s a)
    (Set.finite_range _).bddAbove a

/-- Bounding the Bellman value is equivalent to bounding every action value. -/
theorem bellman_le_iff (γ : ℝ≥0) (v : BoundedFn S) (s : S) (c : ℝ) :
    M.bellman γ v s ≤ c ↔ ∀ a, M.reward s a + γ * M.expect v s a ≤ c := by
  rw [bellman_apply]
  exact ciSup_le_iff (Set.finite_range _).bddAbove

/-- The Bellman operator preserves boundedness with the one-step reward bound. -/
theorem norm_bellman_le [Nonempty S] (γ : ℝ≥0) (v : BoundedFn S) :
    ‖M.bellman γ v‖ ≤ M.rewardBound + γ * ‖v‖ := by
  apply lp.norm_le_of_forall_le'
  intro s
  simpa only [Real.norm_eq_abs, bellman_apply] using M.abs_bellman_le γ v s

/-- At discount zero the Bellman value is the largest immediate reward. -/
@[simp]
theorem bellman_zero_apply (v : BoundedFn S) (s : S) :
    M.bellman 0 v s = ⨆ a, M.reward s a := by
  simp [bellman_apply]

omit [Finite A] [Nonempty A] in
/-- A deterministic stationary policy is greedy for `v` if, in every state `s`, the action `π s`
maximizes the one-step value `a ↦ reward s a + γ * expect v s a`. -/
def IsGreedy (γ : ℝ≥0) (v : S → ℝ) (π : S → A) : Prop :=
  ∀ s a, M.reward s a + γ * M.expect v s a ≤
    M.reward s (π s) + γ * M.expect v s (π s)

omit [Finite A] [Nonempty A] in
/-- A policy is greedy precisely when its chosen action dominates every action value. -/
theorem isGreedy_iff (γ : ℝ≥0) (v : S → ℝ) (π : S → A) :
    M.IsGreedy γ v π ↔ ∀ s a, M.reward s a + γ * M.expect v s a ≤
      M.reward s (π s) + γ * M.expect v s (π s) := Iff.rfl

/-- A policy is greedy precisely when each chosen action attains the Bellman value. -/
theorem isGreedy_iff_eq_bellman (γ : ℝ≥0) (v : BoundedFn S) (π : S → A) :
    M.IsGreedy γ v π ↔ ∀ s,
      M.reward s (π s) + γ * M.expect v s (π s) = M.bellman γ v s := by
  constructor
  · intro h s
    exact le_antisymm (M.le_bellman γ v s (π s))
      ((M.bellman_le_iff γ v s _).2 (h s))
  · intro h s a
    rw [h s]
    exact M.le_bellman γ v s a

/-- Every function on the states admits a greedy deterministic stationary policy. -/
theorem exists_isGreedy (γ : ℝ≥0) (v : S → ℝ) : ∃ π : S → A, M.IsGreedy γ v π := by
  choose π hπ using fun s ↦ Finite.exists_max fun a ↦ M.reward s a + γ * M.expect v s a
  exact ⟨π, (M.isGreedy_iff γ v π).2 hπ⟩

section Countable

variable [Countable S] [MeasurableSingletonClass S]

/-- The Bellman operator preserves pointwise inequalities. -/
theorem bellman_mono (γ : ℝ≥0) {v w : BoundedFn S} (h : ∀ s, v s ≤ w s) :
    ∀ s, M.bellman γ v s ≤ M.bellman γ w s := by
  intro s
  apply (M.bellman_le_iff γ v s _).2
  intro a
  calc
    _ ≤ M.reward s a + γ * M.expect w s a := by
      gcongr
      exact M.expect_mono (M.integrable_trans v s a) (M.integrable_trans w s a) h
    _ ≤ M.bellman γ w s := M.le_bellman γ w s a

private theorem bellman_sub_le (γ : ℝ≥0) (v w : BoundedFn S) (s : S) :
    M.bellman γ v s - M.bellman γ w s ≤ γ * ‖v - w‖ := by
  apply sub_le_iff_le_add.2
  apply (M.bellman_le_iff γ v s _).2
  intro a
  have h := (le_abs_self (M.expect v s a - M.expect w s a)).trans
    (M.abs_expect_sub_le v w s a)
  have hm := mul_le_mul_of_nonneg_left h γ.coe_nonneg
  have ha := M.le_bellman γ w s a
  nlinarith

/-- Bellman updates shrink sup-norm distances by at most the discount factor. -/
theorem norm_bellman_sub_le (γ : ℝ≥0) (v w : BoundedFn S) :
    ‖M.bellman γ v - M.bellman γ w‖ ≤ γ * ‖v - w‖ := by
  apply lp.norm_le_of_forall_le (by positivity)
  intro s
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor
  · have h := M.bellman_sub_le γ w v s
    rw [norm_sub_rev] at h
    linarith
  · exact M.bellman_sub_le γ v w s

/-- The Bellman optimality operator is Lipschitz with constant equal to the discount. -/
theorem lipschitzWith_bellman (γ : ℝ≥0) : LipschitzWith γ (M.bellman γ) := by
  apply lipschitzWith_iff_dist_le_mul.2
  intro v w
  simpa only [dist_eq_norm] using M.norm_bellman_sub_le γ v w

/-- For discount below one, the Bellman optimality operator is a contraction. -/
theorem contractingWith_bellman {γ : ℝ≥0} (hγ : γ < 1) :
    ContractingWith γ (M.bellman γ) :=
  ⟨hγ, M.lipschitzWith_bellman γ⟩

/-- Raising the argument of the optimality operator by a constant `c` raises its value by
`γ * c`. -/
theorem bellman_add_smul_one (γ : ℝ≥0) (v : BoundedFn S) (c : ℝ) :
    M.bellman γ (v + c • 1) = M.bellman γ v + ((γ : ℝ) * c) • 1 := by
  refine lp.ext (funext fun s ↦ ?_)
  rw [lp.infty_coeFn_add_smul_one (M.bellman γ v)]
  simp only [bellman_apply, expect_add_smul_one, mul_add, ← add_assoc]
  exact ((OrderIso.addRight ((γ : ℝ) * c)).map_ciSup (Set.finite_range _).bddAbove).symm

end Countable

end Optimality

section Evaluation

variable {S A : Type*} [MeasurableSpace S] [Fintype A] (M : MDP S A)

/-! ### The Bellman evaluation operator -/

/-- The Bellman evaluation operator of a randomized stationary policy `π` with discount `γ`:
`T^π v s = ∑ a, π s a * (reward s a + γ * expect v s a)`. -/
def bellmanEval (γ : ℝ≥0) (π : S → PMF A) (v : BoundedFn S) : BoundedFn S :=
  ⟨fun s ↦ ∑ a, (π s a).toReal * (M.reward s a + γ * M.expect v s a),
    memℓp_infty ⟨M.rewardBound + γ * ‖v‖, by
      rintro _ ⟨s, rfl⟩
      dsimp only
      rw [Real.norm_eq_abs]
      exact (π s).abs_sum_toReal_mul_le fun a ↦ M.abs_reward_add_expect_le γ v s a⟩⟩

/-- The value of the evaluation operator at a state. -/
@[simp]
theorem bellmanEval_apply (γ : ℝ≥0) (π : S → PMF A) (v : BoundedFn S) (s : S) :
    M.bellmanEval γ π v s = ∑ a, (π s a).toReal * (M.reward s a + γ * M.expect v s a) := (rfl)

/-- The one-step bound for the evaluation operator: `‖T^π v‖ ≤ rewardBound + γ ‖v‖`. -/
theorem norm_bellmanEval_le [Nonempty S] (γ : ℝ≥0) (π : S → PMF A) (v : BoundedFn S) :
    ‖M.bellmanEval γ π v‖ ≤ M.rewardBound + γ * ‖v‖ :=
  lp.norm_le_of_forall_le' _ fun s ↦ by
    rw [bellmanEval_apply, Real.norm_eq_abs]
    exact (π s).abs_sum_toReal_mul_le fun a ↦ M.abs_reward_add_expect_le γ v s a

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

/-! ### Comparison with the optimality operator -/

variable [Nonempty A]

/-- The evaluation operator of any policy is at most the optimality operator. -/
theorem bellmanEval_le_bellman (γ : ℝ≥0) (π : S → PMF A) (v : BoundedFn S) (s : S) :
    M.bellmanEval γ π v s ≤ M.bellman γ v s :=
  (π s).sum_toReal_mul_le_of_forall_le fun a ↦ M.le_bellman γ v s a

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
@[simp high]
theorem bellmanEval_ofDet_apply (γ : ℝ≥0) (π : S → A) (v : BoundedFn S) (s : S) :
    M.bellmanEval γ (ofDet π) v s = M.reward s (π s) + γ * M.expect v s (π s) := by
  classical
  simp [PMF.pure_apply, apply_ite ENNReal.toReal, ite_mul]

/-- The evaluation operator of a deterministic policy agrees with the optimality operator at `v`
if and only if the policy is greedy for `v`. -/
theorem bellmanEval_ofDet_eq_bellman_iff (γ : ℝ≥0) (π : S → A) (v : BoundedFn S) :
    M.bellmanEval γ (ofDet π) v = M.bellman γ v ↔ M.IsGreedy γ v π := by
  rw [isGreedy_iff]
  refine ⟨fun h s a ↦ ?_, fun h ↦ ?_⟩
  · rw [← M.bellmanEval_ofDet_apply, h]
    exact M.le_bellman γ v s a
  · refine lp.ext (funext fun s ↦ ?_)
    rw [M.bellmanEval_ofDet_apply]
    exact le_antisymm (M.le_bellman γ v s (π s)) ((M.bellman_le_iff γ v s _).2 (h s))

end Evaluation

end TauCeti.MDP
