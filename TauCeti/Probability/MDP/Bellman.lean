/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MDP.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# The Bellman optimality operator

For finitely many nonempty actions, `MDP.bellman` maximizes the one-step discounted
reward over actions. It preserves boundedness and order and is Lipschitz with the
discount as constant. For discounts below one it is a contraction, allowing Banach's
fixed-point theorem to supply the optimality equation. A greedy deterministic policy
exists at every bounded value and is characterized by attaining the Bellman maximum.

See M. L. Puterman, *Markov Decision Processes* (1994), Proposition 6.2.4.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti.MDP

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

/-- A deterministic stationary policy is greedy if it maximizes every one-step value. -/
def IsGreedy (γ : ℝ≥0) (v : BoundedFn S) (π : S → A) : Prop :=
  ∀ s a, M.reward s a + γ * M.expect v s a ≤
    M.reward s (π s) + γ * M.expect v s (π s)

omit [Finite A] [Nonempty A] in
/-- A policy is greedy precisely when its chosen action dominates every action value. -/
theorem isGreedy_iff (γ : ℝ≥0) (v : BoundedFn S) (π : S → A) :
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

/-- Every bounded value admits a greedy deterministic stationary policy. -/
theorem exists_isGreedy (γ : ℝ≥0) (v : BoundedFn S) : ∃ π, M.IsGreedy γ v π := by
  classical
  have h (s : S) : ∃ a, M.reward s a + γ * M.expect v s a = M.bellman γ v s := by
    rw [bellman_apply]
    exact exists_eq_ciSup_of_finite
  choose π hπ using h
  exact ⟨π, (M.isGreedy_iff_eq_bellman γ v π).2 hπ⟩

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
      exact M.expect_mono h s a
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

end TauCeti.MDP
