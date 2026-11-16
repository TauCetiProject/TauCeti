/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import TauCeti.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Falling-factorial ratio bounds in ordered fields

Bounds on `(n.descFactorial k : K) / n ^ k` in any linearly ordered field `K`:
`Nat.descFactorial_div_pow_le_one`, `Nat.one_sub_descFactorial_div_pow_le`, and
`Nat.abs_descFactorial_div_pow_sub_one_le`.
-/

public section

namespace Nat

/-- The ratio `(n.descFactorial k : K) / n ^ k` is at most `1` in a linearly ordered semifield. -/
theorem descFactorial_div_pow_le_one {K : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] (n k : ℕ) : (n.descFactorial k : K) / (n : K) ^ k ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast descFactorial_le_pow n k) (by positivity)

/-- In a linearly ordered field with `n ≠ 0`,
`1 - (n.descFactorial k : K) / n ^ k ≤ k.choose 2 / n`. -/
theorem one_sub_descFactorial_div_pow_le {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    1 - (n.descFactorial k : K) / (n : K) ^ k ≤ (k.choose 2 : K) / n := by
  rcases k with _ | m
  · simp
  · have hn_pos : (0 : K) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hdiv := div_le_div_of_nonneg_right (show (n : K) ^ (m + 1) ≤
      (n.descFactorial (m + 1) : K) + ((m + 1).choose 2 : K) * (n : K) ^ m by
        exact_mod_cast pow_le_descFactorial_add_choose_two_mul_pow n (m + 1))
      (pow_pos hn_pos (m + 1)).le
    rw [div_self (pow_pos hn_pos (m + 1)).ne', add_div, _root_.pow_succ',
      mul_div_mul_right _ _ (pow_pos hn_pos m).ne', ← _root_.pow_succ'] at hdiv
    linarith

/-- In a linearly ordered field with `n ≠ 0`,
`|(n.descFactorial k : K) / n ^ k - 1| ≤ k.choose 2 / n`. -/
theorem abs_descFactorial_div_pow_sub_one_le {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    |(n.descFactorial k : K) / (n : K) ^ k - 1| ≤ (k.choose 2 : K) / n := by
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (descFactorial_div_pow_le_one n k))]
  exact one_sub_descFactorial_div_pow_le hn k

end Nat
