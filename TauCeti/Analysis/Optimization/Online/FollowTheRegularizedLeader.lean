/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Topology.Semicontinuity.Defs
public import TauCeti.Analysis.Optimization.Online.Regret

import Mathlib.Topology.Semicontinuity.Basic
import TauCeti.Analysis.Convex.Function.Minimizer
import TauCeti.Analysis.Convex.Function.Uniform

/-!
# Follow the regularized leader

Let `K` be a subset of a real normed space `F`, `ψ : F → ℝ` a regularizer, `η` a step size and
`g t` continuous linear functionals, the linear losses. Follow the regularized leader plays at
round `t` a minimizer over `K` of the regularized cumulative loss
`y ↦ ψ y + η * ∑_{s < t} g s y`. This file proves its regret bound: if `ψ` is `μ`-strongly convex
on `K` with `μ > 0` and `η > 0`, then against every `u ∈ K`

`∑_{t < T} g t (x t - u) ≤ (ψ u - ψ (x 0)) / η + η / (2 * μ) * ∑_{t < T} ‖g t‖ ^ 2`,

where `‖g t‖` is the operator norm, that is the dual norm. By the linearization of the regret,
the same bound holds for the regret on convex losses `f t` of which `g t` is a subgradient at the
iterate `x t`.

The proof compares consecutive regularized cumulative losses: the objective of round `t + 1` is
that of round `t` plus `η * g t`, and its decrease from `x t` to `x (t + 1)` is at most
`η ^ 2 / (2 * μ) * ‖g t‖ ^ 2`, because the objective of round `t` grows quadratically away from
its minimizer `x t`. Summing, the decreases telescope against the total linear loss of the
iterates, and the minimality of `x T` compares it with the comparator.

The iterates exist and are unique when `K` is nonempty and complete and `ψ` is lower
semicontinuous on `K`.

## Main definitions

* `TauCeti.OnlineConvexOptimization.IsFTRL K ψ η g x`: each `x t` lies in `K` and minimizes the
  regularized cumulative loss of the rounds before `t` over `K`.

## Main results

* `TauCeti.OnlineConvexOptimization.existsUnique_isFTRL`: for a lower semicontinuous regularizer
  that is strongly convex with positive modulus on a nonempty complete set, the iterates of
  follow the regularized leader exist and are unique.
* `TauCeti.OnlineConvexOptimization.sum_apply_sub_le_of_isFTRL`: the regret bound on the linear
  losses.
* `TauCeti.OnlineConvexOptimization.regret_le_of_isFTRL`: the regret bound on convex losses with
  subgradients `g t`.

## References

* F. Orabona, *A modern introduction to online learning*, arXiv:1912.13213, Lemma 7.1, Lemma 7.5
  and Corollary 7.6, with constant step `η` and regularizer `ψ / η`.
* E. Hazan, *Introduction to online convex optimization*, 2nd ed., MIT Press, 2022, Theorem 5.2.
-/

public section

open Finset

namespace TauCeti.OnlineConvexOptimization

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Set F} {ψ : F → ℝ} {μ η : ℝ} {g : ℕ → StrongDual ℝ F} {x : ℕ → F}

/-- The sequence `x` consists of iterates of follow the regularized leader on `K` with the
regularizer `ψ`, the step `η` and the linear losses `g`: for every `t`, `x t` lies in `K` and
minimizes `y ↦ ψ y + η * ∑_{s < t} g s y` over `K`. -/
def IsFTRL (K : Set F) (ψ : F → ℝ) (η : ℝ) (g : ℕ → StrongDual ℝ F) (x : ℕ → F) : Prop :=
  ∀ t, x t ∈ K ∧ IsMinOn (fun y ↦ ψ y + η * ∑ s ∈ range t, g s y) K (x t)

theorem isFTRL_iff :
    IsFTRL K ψ η g x ↔
      ∀ t, x t ∈ K ∧ IsMinOn (fun y ↦ ψ y + η * ∑ s ∈ range t, g s y) K (x t) :=
  Iff.rfl

namespace IsFTRL

/-- Each iterate of follow the regularized leader lies in `K`. -/
theorem mem (hx : IsFTRL K ψ η g x) (t : ℕ) : x t ∈ K :=
  (hx t).1

/-- The iterate `x t` minimizes the regularized cumulative loss of the rounds before `t` over
`K`. -/
theorem isMinOn (hx : IsFTRL K ψ η g x) (t : ℕ) :
    IsMinOn (fun y ↦ ψ y + η * ∑ s ∈ range t, g s y) K (x t) :=
  (hx t).2

/-- The first iterate of follow the regularized leader minimizes the regularizer over `K`. -/
theorem isMinOn_zero (hx : IsFTRL K ψ η g x) : IsMinOn ψ K (x 0) := by
  simpa using hx.isMinOn 0

end IsFTRL

/-- The regularized cumulative loss of the rounds before `t` is `μ`-strongly convex on `K` when
the regularizer is: the cumulative loss is linear. -/
private theorem strongConvexOn_add_mul_sum (hψ : StrongConvexOn K μ ψ) (η : ℝ)
    (g : ℕ → StrongDual ℝ F) (t : ℕ) :
    StrongConvexOn K μ (fun y ↦ ψ y + η * ∑ s ∈ range t, g s y) := by
  have hlin : ConvexOn ℝ K fun y ↦ η * ∑ s ∈ range t, g s y := by
    convert (((η • ∑ s ∈ range t, g s : StrongDual ℝ F) : F →ₗ[ℝ] ℝ).convexOn hψ.1) using 1
    funext y
    simp
  simpa [StrongConvexOn, Pi.add_def] using UniformConvexOn.add hψ (uniformConvexOn_zero.2 hlin)

/-- **Existence and uniqueness of the iterates of follow the regularized leader.** If `K` is
nonempty and complete and the regularizer `ψ` is lower semicontinuous and `μ`-strongly convex
on `K` with `μ > 0`, then for every step `η` and linear losses `g` there is exactly one sequence
of iterates of follow the regularized leader. -/
theorem existsUnique_isFTRL (hψ : StrongConvexOn K μ ψ) (hμ : 0 < μ)
    (hlsc : LowerSemicontinuousOn ψ K) (hK : IsComplete K) (hne : K.Nonempty) (η : ℝ)
    (g : ℕ → StrongDual ℝ F) : ∃! x, IsFTRL K ψ η g x := by
  have h t : ∃! y, y ∈ K ∧ IsMinOn (fun y ↦ ψ y + η * ∑ s ∈ range t, g s y) K y := by
    refine (strongConvexOn_add_mul_sum hψ η g t).existsUnique_isMinOn hμ hK hne ?_
    exact hlsc.add ((by fun_prop : Continuous _).lowerSemicontinuous.lowerSemicontinuousOn K)
  choose x hx hxu using h
  exact ⟨x, hx, fun y hy ↦ funext fun t ↦ hxu t (y t) (hy t)⟩

/-- One round of follow the regularized leader: the objective of round `t + 1` decreases from
`x t` to `x (t + 1)` by at most `η ^ 2 / (2 * μ) * ‖g t‖ ^ 2`. -/
private theorem add_mul_sum_succ_sub_le (hψ : StrongConvexOn K μ ψ) (hμ : 0 < μ) (hη : 0 < η)
    (hx : IsFTRL K ψ η g x) (t : ℕ) :
    (ψ (x t) + η * ∑ s ∈ range (t + 1), g s (x t)) -
        (ψ (x (t + 1)) + η * ∑ s ∈ range (t + 1), g s (x (t + 1))) ≤
      η ^ 2 / (2 * μ) * ‖g t‖ ^ 2 := by
  -- The objective of round `t` grows quadratically away from its minimizer `x t`.
  have hgrow := (strongConvexOn_add_mul_sum hψ η g t).mul_norm_sub_sq_le_sub_of_isMinOn
    (hx.mem t) (hx.isMinOn t) (hx.mem (t + 1))
  -- The new linear loss is bounded by its dual norm.
  have hg : g t (x t) - g t (x (t + 1)) ≤ ‖g t‖ * ‖x t - x (t + 1)‖ := by
    rw [← map_sub]
    exact (Real.le_norm_self _).trans ((g t).le_opNorm _)
  have hηg := mul_le_mul_of_nonneg_left hg hη.le
  simp only [sum_range_succ] at hgrow ⊢
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (η * ‖g t‖ - μ * ‖x t - x (t + 1)‖)]

/-- **The regret bound of follow the regularized leader** on linear losses. If the regularizer
`ψ` is `μ`-strongly convex on `K` with `μ > 0`, `η > 0` and `x` are the iterates of follow the
regularized leader, then for every `u ∈ K` the regret on the linear losses `g t` satisfies
`∑_{t < T} g t (x t - u) ≤ (ψ u - ψ (x 0)) / η + η / (2 * μ) * ∑_{t < T} ‖g t‖ ^ 2`. -/
theorem sum_apply_sub_le_of_isFTRL (hψ : StrongConvexOn K μ ψ) (hμ : 0 < μ) (hη : 0 < η)
    (hx : IsFTRL K ψ η g x) (T : ℕ) {u : F} (hu : u ∈ K) :
    ∑ t ∈ range T, g t (x t - u) ≤
      (ψ u - ψ (x 0)) / η + η / (2 * μ) * ∑ t ∈ range T, ‖g t‖ ^ 2 := by
  -- The decreases of the objectives telescope against the linear loss of the iterates.
  have htel : ∀ n, η * ∑ t ∈ range n, g t (x t) + ψ (x 0) -
      (ψ (x n) + η * ∑ s ∈ range n, g s (x n)) ≤
        η ^ 2 / (2 * μ) * ∑ t ∈ range n, ‖g t‖ ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep := add_mul_sum_succ_sub_le hψ hμ hη hx n
      simp only [sum_range_succ] at hstep ⊢
      linarith
  -- The last iterate minimizes the objective of round `T`, in particular below `u`.
  have hmin := isMinOn_iff.1 (hx.isMinOn T) u hu
  have hsum : ∑ t ∈ range T, g t (x t - u) =
      ∑ t ∈ range T, g t (x t) - ∑ t ∈ range T, g t u := by
    simp only [map_sub, sum_sub_distrib]
  have hrhs : (ψ u - ψ (x 0)) / η + η / (2 * μ) * ∑ t ∈ range T, ‖g t‖ ^ 2 =
      (ψ u - ψ (x 0) + η ^ 2 / (2 * μ) * ∑ t ∈ range T, ‖g t‖ ^ 2) / η := by
    field_simp
  rw [hrhs, le_div_iff₀ hη, hsum]
  linarith [htel T]

/-- **The regret bound of follow the regularized leader.** If the regularizer `ψ` is
`μ`-strongly convex on `K` with `μ > 0`, `η > 0`, `x` are the iterates of follow the regularized
leader for the linear losses `g`, and `u ∈ K` is a comparator at which each `g t` with `t < T`
satisfies the subgradient inequality `f t (x t) + g t (u - x t) ≤ f t u` of the loss `f t` at
`x t`, then `regret f x T u ≤ (ψ u - ψ (x 0)) / η + η / (2 * μ) * ∑_{t < T} ‖g t‖ ^ 2`. This holds
in particular when each `g t` is a subgradient of `f t` at `x t` relative to `K`. -/
theorem regret_le_of_isFTRL (hψ : StrongConvexOn K μ ψ) (hμ : 0 < μ) (hη : 0 < η)
    (hx : IsFTRL K ψ η g x) (f : ℕ → F → ℝ) {T : ℕ} {u : F} (hu : u ∈ K)
    (hf : ∀ t < T, f t (x t) + g t (u - x t) ≤ f t u) :
    regret f x T u ≤ (ψ u - ψ (x 0)) / η + η / (2 * μ) * ∑ t ∈ range T, ‖g t‖ ^ 2 :=
  (regret_le_sum_apply_sub f x g hf).trans (sum_apply_sub_le_of_isFTRL hψ hμ hη hx T hu)

end TauCeti.OnlineConvexOptimization
