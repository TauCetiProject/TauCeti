/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Regret in online convex optimization

In online convex optimization a learner plays points `x 0, x 1, …`; after it plays `x t`, a loss
`f t` is revealed and the learner pays `f t (x t)`. Its performance after `T` rounds is measured
against a fixed comparator `u` by the regret `∑_{t < T} (f t (x t) - f t u)`.

Every regret bound for a first-order method starts by replacing the losses by linear ones: if
`g t` is a subgradient of `f t` at `x t`, the regret on `f` is at most the regret on the linear
losses `g t`. The losses may be strongly convex, with modulus `m t`, in which case the quadratic
term of the subgradient inequality is subtracted from the bound.

## Main definitions

* `TauCeti.OnlineConvexOptimization.regret f x T u`: the regret after `T` rounds of the plays `x`
  on the losses `f` against the comparator `u`.

## Main results

* `TauCeti.OnlineConvexOptimization.regret_succ`: the regret grows by the loss gap of the last
  round.
* `TauCeti.OnlineConvexOptimization.regret_le_sum_apply_sub_sub`: if `g t` is a subgradient with
  modulus `m t` of `f t` at `x t`, that is,
  `f t (x t) + g t (u - x t) + m t / 2 * ‖u - x t‖ ^ 2 ≤ f t u`, then the regret is at most
  `∑_{t < T} (g t (x t - u) - m t / 2 * ‖x t - u‖ ^ 2)`; here `g t` is a continuous linear
  functional on a real normed space.
* `TauCeti.OnlineConvexOptimization.regret_le_sum_apply_sub`: the case `m = 0`.
* `TauCeti.OnlineConvexOptimization.regret_le_sum_inner_sub_sub`: the same bound in a real inner
  product space, with the subgradients `g t` given as vectors.
* `TauCeti.OnlineConvexOptimization.regret_le_sum_inner_sub`: its case `m = 0`.

## References

* F. Orabona, *A modern introduction to online learning*, arXiv:1912.13213, Chapter 1 for the
  definition, and Lemma 2.31 and Lemma 4.2 for the linearization.
* E. Hazan, *Introduction to online convex optimization*, 2nd ed., MIT Press, 2022,
  equation (1.1).
-/

public section

open Finset
open scoped RealInnerProductSpace

namespace TauCeti.OnlineConvexOptimization

variable {α : Type*}

/-- The regret after `T` rounds of the plays `x` on the losses `f` against the comparator `u`:
the total loss `∑_{t < T} f t (x t)` of the plays minus the total loss of `u`. -/
def regret (f : ℕ → α → ℝ) (x : ℕ → α) (T : ℕ) (u : α) : ℝ :=
  ∑ t ∈ range T, (f t (x t) - f t u)

theorem regret_def (f : ℕ → α → ℝ) (x : ℕ → α) (T : ℕ) (u : α) :
    regret f x T u = ∑ t ∈ range T, (f t (x t) - f t u) :=
  (rfl)

@[simp]
theorem regret_zero (f : ℕ → α → ℝ) (x : ℕ → α) (u : α) : regret f x 0 u = 0 := by
  simp [regret_def]

/-- The regret after `T + 1` rounds is the regret after `T` rounds plus the loss gap of round
`T`. -/
theorem regret_succ (f : ℕ → α → ℝ) (x : ℕ → α) (T : ℕ) (u : α) :
    regret f x (T + 1) u = regret f x T u + (f T (x T) - f T u) := by
  simp only [regret_def, sum_range_succ]

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Linearization of the regret.** If, at each round `t < T`, the continuous linear functional
`g t` satisfies the subgradient inequality of `f t` at `x t` with modulus `m t` at the
comparator `u`, then the regret against `u` is at most
`∑_{t < T} (g t (x t - u) - m t / 2 * ‖x t - u‖ ^ 2)`. -/
theorem regret_le_sum_apply_sub_sub (f : ℕ → F → ℝ) (x : ℕ → F) (g : ℕ → StrongDual ℝ F)
    (m : ℕ → ℝ) {T : ℕ} {u : F}
    (h : ∀ t < T, f t (x t) + g t (u - x t) + m t / 2 * ‖u - x t‖ ^ 2 ≤ f t u) :
    regret f x T u ≤ ∑ t ∈ range T, (g t (x t - u) - m t / 2 * ‖x t - u‖ ^ 2) := by
  rw [regret_def]
  refine sum_le_sum fun t ht ↦ ?_
  have ht := h t (mem_range.1 ht)
  rw [← neg_sub (x t) u, map_neg, norm_neg] at ht
  linarith

/-- **Linearization of the regret**, without modulus: if, at each round `t < T`, the continuous
linear functional `g t` satisfies the subgradient inequality of `f t` at `x t` at the comparator
`u`, then the regret on `f` is at most the regret `∑_{t < T} g t (x t - u)` on the linear losses
`g t`. -/
theorem regret_le_sum_apply_sub (f : ℕ → F → ℝ) (x : ℕ → F) (g : ℕ → StrongDual ℝ F) {T : ℕ}
    {u : F} (h : ∀ t < T, f t (x t) + g t (u - x t) ≤ f t u) :
    regret f x T u ≤ ∑ t ∈ range T, g t (x t - u) := by
  simpa using regret_le_sum_apply_sub_sub f x g 0 (u := u) fun t ht ↦ by simpa using h t ht

end Normed

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Linearization of the regret** in a real inner product space. If, at each round `t < T`,
the vector `g t` satisfies the subgradient inequality of `f t` at `x t` with modulus `m t` at the
comparator `u`, then the regret against `u` is at most
`∑_{t < T} (⟪g t, x t - u⟫ - m t / 2 * ‖x t - u‖ ^ 2)`. -/
theorem regret_le_sum_inner_sub_sub (f : ℕ → E → ℝ) (x : ℕ → E) (g : ℕ → E) (m : ℕ → ℝ)
    {T : ℕ} {u : E} (h : ∀ t < T, f t (x t) + ⟪g t, u - x t⟫ + m t / 2 * ‖u - x t‖ ^ 2 ≤ f t u) :
    regret f x T u ≤ ∑ t ∈ range T, (⟪g t, x t - u⟫ - m t / 2 * ‖x t - u‖ ^ 2) := by
  simpa only [innerSL_apply_apply] using
    regret_le_sum_apply_sub_sub f x (fun t ↦ innerSL ℝ (g t)) m
      (u := u) fun t ht ↦ by simpa only [innerSL_apply_apply] using h t ht

/-- **Linearization of the regret** in a real inner product space, without modulus: if, at each
round `t < T`, the vector `g t` satisfies the subgradient inequality of `f t` at `x t` at the
comparator `u`, then the regret on `f` is at most the regret `∑_{t < T} ⟪g t, x t - u⟫` on the
linear losses `⟪g t, ·⟫`. -/
theorem regret_le_sum_inner_sub (f : ℕ → E → ℝ) (x : ℕ → E) (g : ℕ → E) {T : ℕ} {u : E}
    (h : ∀ t < T, f t (x t) + ⟪g t, u - x t⟫ ≤ f t u) :
    regret f x T u ≤ ∑ t ∈ range T, ⟪g t, x t - u⟫ := by
  simpa using regret_le_sum_inner_sub_sub f x g 0 (u := u) fun t ht ↦ by simpa using h t ht

end Inner

end TauCeti.OnlineConvexOptimization
