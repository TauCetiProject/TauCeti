/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The perceptron and Novikoff's bound

For instances `x : ℕ → E` in a real inner product space and labels `y : ℕ → ℝ`, the perceptron
keeps a weight vector `w t`. It starts at `w 0 = 0`. In round `t` it updates the weight to
`w t + y t • x t` when `y t * ⟪w t, x t⟫ ≤ 0`, and keeps it otherwise. Novikoff's bound says
that, if the labels have absolute value at most `1` (for example `±1`), the instances have norm
at most `R`, and some `u` satisfies `γ ≤ y t * ⟪u, x t⟫` in every round for a margin `γ > 0`,
then the number of update rounds is at most `(R * ‖u‖ / γ) ^ 2`, whatever the dimension of `E`.

## Main definitions

* `TauCeti.perceptronWeight x y t`: the perceptron weight `w t` before round `t`.
* `TauCeti.perceptronUpdates x y T`: the update rounds among the first `T` rounds.

## Main results

* `TauCeti.perceptronWeight_eq_sum`: `w T` is the sum of `y t • x t` over the update rounds
  `t < T`.
* `TauCeti.mul_card_perceptronUpdates_le_inner`: with `M` update rounds and margin `γ`,
  `γ * M ≤ ⟪u, w T⟫`.
* `TauCeti.norm_perceptronWeight_sq_le`: `‖w T‖ ^ 2 ≤ R ^ 2 * M`.
* `TauCeti.card_perceptronUpdates_le`: Novikoff's bound `M ≤ (R * ‖u‖ / γ) ^ 2`.

## References

* A. B. J. Novikoff, *On convergence proofs on perceptrons*, Symposium on the Mathematical
  Theory of Automata 12 (1962), 615–622.
* S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning*, Cambridge University
  Press (2014), §21.4, Theorem 21.16.
* M. Mohri, A. Rostamizadeh and A. Talwalkar, *Foundations of Machine Learning*, second
  edition, MIT Press (2018), equation (8.23) and Theorem 8.8.
-/

public section

open Finset
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The perceptron weights for instances `x` and labels `y`: `w 0 = 0`, and
`w (t + 1) = w t + y t • x t` when `y t * ⟪w t, x t⟫ ≤ 0`, `w (t + 1) = w t` otherwise. -/
noncomputable def perceptronWeight (x : ℕ → E) (y : ℕ → ℝ) : ℕ → E
  | 0 => 0
  | t + 1 =>
    if y t * ⟪perceptronWeight x y t, x t⟫ ≤ 0 then perceptronWeight x y t + y t • x t
    else perceptronWeight x y t

/-- The update rounds of the perceptron among the first `T` rounds: the `t < T` with
`y t * ⟪w t, x t⟫ ≤ 0`. -/
noncomputable def perceptronUpdates (x : ℕ → E) (y : ℕ → ℝ) (T : ℕ) : Finset ℕ :=
  {t ∈ range T | y t * ⟪perceptronWeight x y t, x t⟫ ≤ 0}

variable (x : ℕ → E) (y : ℕ → ℝ)

/-- The perceptron starts at the zero weight. -/
@[simp]
theorem perceptronWeight_zero : perceptronWeight x y 0 = 0 := by
  rw [perceptronWeight]

/-- The recursion of the perceptron weight. -/
theorem perceptronWeight_succ (t : ℕ) :
    perceptronWeight x y (t + 1) =
      if y t * ⟪perceptronWeight x y t, x t⟫ ≤ 0 then perceptronWeight x y t + y t • x t
      else perceptronWeight x y t := by
  rw [perceptronWeight]

variable {x y}

/-- At an update round the weight moves by `y t • x t`. -/
theorem perceptronWeight_succ_of_nonpos {t : ℕ} (h : y t * ⟪perceptronWeight x y t, x t⟫ ≤ 0) :
    perceptronWeight x y (t + 1) = perceptronWeight x y t + y t • x t := by
  simp [perceptronWeight_succ, h]

/-- Outside the update rounds the weight does not change. -/
theorem perceptronWeight_succ_of_pos {t : ℕ} (h : 0 < y t * ⟪perceptronWeight x y t, x t⟫) :
    perceptronWeight x y (t + 1) = perceptronWeight x y t := by
  simp [perceptronWeight_succ, h.not_ge]

/-- A round `t` is an update round among the first `T` when `t < T` and
`y t * ⟪w t, x t⟫ ≤ 0`. -/
@[simp]
theorem mem_perceptronUpdates {T t : ℕ} :
    t ∈ perceptronUpdates x y T ↔ t < T ∧ y t * ⟪perceptronWeight x y t, x t⟫ ≤ 0 := by
  simp [perceptronUpdates]

variable (x y) in
/-- There are no update rounds among the first `0` rounds. -/
@[simp]
theorem perceptronUpdates_zero : perceptronUpdates x y 0 = ∅ := by
  simp [perceptronUpdates]

/-- If round `T` is an update round, the update rounds among the first `T + 1` rounds are those
among the first `T` together with `T`. -/
theorem perceptronUpdates_succ_of_nonpos {T : ℕ}
    (h : y T * ⟪perceptronWeight x y T, x T⟫ ≤ 0) :
    perceptronUpdates x y (T + 1) = insert T (perceptronUpdates x y T) := by
  simp [perceptronUpdates, range_add_one, filter_insert, h]

/-- If round `T` is not an update round, the update rounds among the first `T + 1` rounds are
those among the first `T`. -/
theorem perceptronUpdates_succ_of_pos {T : ℕ}
    (h : 0 < y T * ⟪perceptronWeight x y T, x T⟫) :
    perceptronUpdates x y (T + 1) = perceptronUpdates x y T := by
  simp [perceptronUpdates, range_add_one, filter_insert, h.not_ge]

/-- Round `0` is always an update round, since `w 0 = 0`. -/
theorem zero_mem_perceptronUpdates {T : ℕ} (hT : 0 < T) : 0 ∈ perceptronUpdates x y T := by
  simp [hT]

variable (x y) in
/-- The perceptron weight `w T` is the sum of `y t • x t` over the update rounds `t < T`. -/
theorem perceptronWeight_eq_sum (T : ℕ) :
    perceptronWeight x y T = ∑ t ∈ perceptronUpdates x y T, y t • x t := by
  rw [perceptronUpdates, sum_filter]
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, ← ih, perceptronWeight_succ]
    split_ifs <;> simp

/-- If `u` has margin `γ` on the first `T` examples, then `γ` times the number of update rounds
among them is at most `⟪u, w T⟫`. -/
theorem mul_card_perceptronUpdates_le_inner {T : ℕ} {γ : ℝ} {u : E}
    (hmargin : ∀ t < T, γ ≤ y t * ⟪u, x t⟫) :
    γ * #(perceptronUpdates x y T) ≤ ⟪u, perceptronWeight x y T⟫ := by
  rw [perceptronWeight_eq_sum, inner_sum, mul_comm, ← nsmul_eq_mul]
  refine card_nsmul_le_sum _ _ _ fun t ht ↦ ?_
  rw [real_inner_smul_right]
  exact hmargin t (mem_perceptronUpdates.mp ht).1

/-- If the labels have absolute value at most `1` and the instances have norm at most `R` on the
first `T` rounds, then `‖w T‖ ^ 2` is at most `R ^ 2` times the number of update rounds among
them. -/
theorem norm_perceptronWeight_sq_le {T : ℕ} {R : ℝ} (hy : ∀ t < T, |y t| ≤ 1)
    (hR : ∀ t < T, ‖x t‖ ≤ R) :
    ‖perceptronWeight x y T‖ ^ 2 ≤ R ^ 2 * #(perceptronUpdates x y T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have ih := ih (fun t ht ↦ hy t (ht.trans T.lt_add_one))
      (fun t ht ↦ hR t (ht.trans T.lt_add_one))
    rcases le_or_gt (y T * ⟪perceptronWeight x y T, x T⟫) 0 with h | h
    · rw [perceptronWeight_succ_of_nonpos h, perceptronUpdates_succ_of_nonpos h,
        card_insert_of_notMem (fun hT ↦ (mem_perceptronUpdates.mp hT).1.false),
        norm_add_sq_real, real_inner_smul_right]
      have hxy : ‖y T • x T‖ ≤ R := by
        rw [norm_smul, Real.norm_eq_abs]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hy T T.lt_add_one)).trans
          (hR T T.lt_add_one)
      have hsq : ‖y T • x T‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxy 2
      push_cast
      nlinarith
    · rw [perceptronWeight_succ_of_pos h, perceptronUpdates_succ_of_pos h]
      exact ih

/-- **Novikoff's bound.** If the labels have absolute value at most `1` (for example `±1`), the
instances have norm at most `R` and `u` separates the first `T` examples with margin `γ > 0`,
then the perceptron updates at most `(R * ‖u‖ / γ) ^ 2` times in the first `T` rounds. -/
theorem card_perceptronUpdates_le {T : ℕ} {R γ : ℝ} {u : E} (hy : ∀ t < T, |y t| ≤ 1)
    (hR : ∀ t < T, ‖x t‖ ≤ R) (hγ : 0 < γ) (hmargin : ∀ t < T, γ ≤ y t * ⟪u, x t⟫) :
    (#(perceptronUpdates x y T) : ℝ) ≤ (R * ‖u‖ / γ) ^ 2 := by
  set M : ℝ := ((perceptronUpdates x y T).card : ℝ)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have h₁ : γ * M ≤ ‖u‖ * ‖perceptronWeight x y T‖ :=
    (mul_card_perceptronUpdates_le_inner hmargin).trans (real_inner_le_norm _ _)
  have h₂ := norm_perceptronWeight_sq_le hy hR
  -- Squaring `h₁` and inserting `h₂` gives `γ ^ 2 * M ^ 2 ≤ ‖u‖ ^ 2 * R ^ 2 * M`.
  have h₃ : (γ * M) ^ 2 ≤ ‖u‖ ^ 2 * (R ^ 2 * M) := by
    calc (γ * M) ^ 2 ≤ (‖u‖ * ‖perceptronWeight x y T‖) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hγ.le hM) h₁ 2
      _ = ‖u‖ ^ 2 * ‖perceptronWeight x y T‖ ^ 2 := mul_pow _ _ _
      _ ≤ ‖u‖ ^ 2 * (R ^ 2 * M) := mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
  rcases hM.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · rw [div_pow, le_div_iff₀ (pow_pos hγ 2)]
    nlinarith

end TauCeti
