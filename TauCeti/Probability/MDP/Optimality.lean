/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MDP.Bellman

/-!
# Optimality of stationary policies in a discounted Markov decision process

For a discount `γ < 1`, finitely many nonempty actions and countably many states, this file
compares the value `M.value γ π` of a stationary policy with the optimal value
`V⋆ = M.optimalValue γ`, the fixed point of the Bellman optimality operator `T = M.bellman γ`.

A bounded function `v` with `v ≤ T v` stays below every iterate `T^[k] v`, and these iterates
converge to `V⋆`, so `v ≤ V⋆`. The value of a randomized stationary policy `π` is such a
function, since `V^π = T^π V^π ≤ T V^π`. A deterministic policy that is greedy for `V⋆` has
an evaluation operator that fixes `V⋆`, so its value is `V⋆`, and such a policy exists.

## Main results

* `MDP.le_optimalValue_of_le_bellman`: a bounded function with `v ≤ T v` is below `V⋆`.
* `MDP.value_le_optimalValue`: every randomized stationary policy has value at most `V⋆`.
* `MDP.value_eq_optimalValue_of_isGreedy`: a deterministic policy greedy for `V⋆` attains `V⋆`,
  and `MDP.exists_value_ofDet_eq_optimalValue`: such a policy exists.
* `MDP.value_ofDet_eq_optimalValue_iff_isGreedy_optimalValue`,
  `MDP.value_ofDet_eq_optimalValue_iff_isGreedy_value`: a deterministic policy is optimal if and
  only if it is greedy for `V⋆`, and if and only if it is greedy for its own value.

## References

* M. L. Puterman, *Markov decision processes: discrete stochastic dynamic programming*, Wiley,
  1994, Section 6.2.
-/

public section

noncomputable section

open scoped ENNReal NNReal

namespace TauCeti.MDP

variable {S A : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [Fintype A] [Nonempty A] (M : MDP S A) {γ : ℝ≥0}

/-- For `γ < 1`, a bounded function that is at most its Bellman update `T v` is at most the
optimal value. -/
theorem le_optimalValue_of_le_bellman (hγ : γ < 1) {v : BoundedFn S}
    (hv : ∀ s, v s ≤ M.bellman γ v s) (s : S) : v s ≤ M.optimalValue γ s := by
  have hk : ∀ k s, v s ≤ (M.bellman γ)^[k] v s := by
    intro k
    induction k with
    | zero => exact fun _ ↦ le_rfl
    | succ k ih =>
      intro s
      rw [Function.iterate_succ_apply']
      exact (hv s).trans (M.bellman_mono γ ih s)
  exact ge_of_tendsto' (((lp.lipschitzWith_one_eval ∞ s).continuous.tendsto _).comp
    (M.tendsto_iterate_bellman hγ v)) fun k ↦ hk k s

/-- For `γ < 1`, the value of every randomized stationary policy is at most the optimal
value. -/
theorem value_le_optimalValue (hγ : γ < 1) (π : S → PMF A) (s : S) :
    M.value γ π s ≤ M.optimalValue γ s := by
  refine M.le_optimalValue_of_le_bellman hγ (fun s ↦ ?_) s
  have h := M.bellmanEval_le_bellman γ π (M.value γ π) s
  rwa [M.bellmanEval_value hγ π] at h

/-- For `γ < 1`, a deterministic stationary policy that is greedy for the optimal value attains
the optimal value. -/
theorem value_eq_optimalValue_of_isGreedy (hγ : γ < 1) {π : S → A}
    (hπ : M.IsGreedy γ (M.optimalValue γ) π) :
    M.value γ (ofDet π) = M.optimalValue γ :=
  ((M.bellmanEval_eq_self_iff hγ (ofDet π)).1 <|
    ((M.bellmanEval_ofDet_eq_bellman_iff γ π _).2 hπ).trans (M.bellman_optimalValue hγ)).symm

/-- For `γ < 1`, some deterministic stationary policy attains the optimal value. -/
theorem exists_value_ofDet_eq_optimalValue (hγ : γ < 1) :
    ∃ π : S → A, M.value γ (ofDet π) = M.optimalValue γ := by
  obtain ⟨π, hπ⟩ := M.exists_isGreedy γ (M.optimalValue γ)
  exact ⟨π, M.value_eq_optimalValue_of_isGreedy hγ hπ⟩

/-- For `γ < 1`, a deterministic stationary policy attains the optimal value if and only if it is
greedy for the optimal value. -/
theorem value_ofDet_eq_optimalValue_iff_isGreedy_optimalValue (hγ : γ < 1) (π : S → A) :
    M.value γ (ofDet π) = M.optimalValue γ ↔ M.IsGreedy γ (M.optimalValue γ) π := by
  refine ⟨fun h ↦ ?_, M.value_eq_optimalValue_of_isGreedy hγ⟩
  rw [← M.bellmanEval_ofDet_eq_bellman_iff, M.bellman_optimalValue hγ, ← h,
    M.bellmanEval_value hγ]

/-- For `γ < 1`, a deterministic stationary policy attains the optimal value if and only if it is
greedy for its own value. -/
theorem value_ofDet_eq_optimalValue_iff_isGreedy_value (hγ : γ < 1) (π : S → A) :
    M.value γ (ofDet π) = M.optimalValue γ ↔ M.IsGreedy γ (M.value γ (ofDet π)) π := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h]
    exact (M.value_ofDet_eq_optimalValue_iff_isGreedy_optimalValue hγ π).1 h
  · have h' := (M.bellmanEval_ofDet_eq_bellman_iff γ π _).2 h
    rw [M.bellmanEval_value hγ] at h'
    exact (M.bellman_eq_self_iff hγ).1 h'.symm

end TauCeti.MDP
