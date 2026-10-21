/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Nat.Choose.Sum

/-!
# Alternating binomial sums

Pascal's identity expresses an alternating binomial sum at order `n + 1` as the
order-`n` sum of the differences `f k - f (k + 1)`.
-/

public section

namespace TauCeti

/-- An alternating binomial sum at the next order is the current-order sum of
successive differences. -/
theorem sum_neg_one_pow_mul_choose_succ {R : Type*} [Ring R] (f : ℕ → R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2), (-1 : R) ^ k * ((n + 1).choose k : R) * f k) =
      ∑ k ∈ Finset.range (n + 1), (-1 : R) ^ k * (n.choose k : R) *
        (f k - f (k + 1)) := by
  calc
    _ = ∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : R) *
        ((-1 : R) ^ k * f k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← mul_assoc, Nat.cast_comm]
    _ = _ := Finset.sum_choose_succ_mul (fun k _ ↦ (-1 : R) ^ k * f k) n
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      simp [pow_succ, sub_eq_add_neg, mul_add, mul_assoc, Nat.cast_comm]

end TauCeti
