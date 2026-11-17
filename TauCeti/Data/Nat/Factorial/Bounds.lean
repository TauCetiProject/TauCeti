/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Field.Basic
import TauCeti.Data.Nat.Factorial.Basic

/-!
# Normalized descending-factorial bounds

For nonzero `n`, dividing the natural-number collision inequality
`n ^ (k + 1) ≤ (n)_{k + 1} + (k + 1).choose 2 * n ^ k`
(`Nat.pow_succ_le_descFactorial_add_choose_two_mul_pow`) by `n ^ (k + 1)` gives the normalized
deficit bound `|(n)_k / n ^ k - 1| ≤ k.choose 2 / n` in any linearly ordered field (holding
trivially for `k = 0` as well).

## Main results

* `Nat.abs_descFactorial_div_pow_sub_one_le`: `|(n.descFactorial k : α) / (n : α) ^ k - 1| ≤
  (k.choose 2 : α) / n` for `n ≠ 0` and any `k : ℕ` in a linearly ordered field `α`.
-/

public section

namespace Nat

/-- **Normalized descending-factorial deficit bound.** For `n ≠ 0` and any `k : ℕ`, the normalized
falling factorial `(n)_k / n ^ k` lies within `k.choose 2 / n` of `1` in any linearly ordered
field. -/
theorem abs_descFactorial_div_pow_sub_one_le {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    |(n.descFactorial k : α) / (n : α) ^ k - 1| ≤ (k.choose 2 : α) / n := by
  rcases k with _ | m
  · simp
  · have hnα : (0 : α) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hpow : (0 : α) < (n : α) ^ (m + 1) := pow_pos hnα _
    have hdf_le : (n.descFactorial (m + 1) : α) ≤ (n : α) ^ (m + 1) := by
      exact_mod_cast Nat.descFactorial_le_pow n (m + 1)
    have hsub_le : (n : α) ^ (m + 1) - n.descFactorial (m + 1) ≤
        ((m + 1).choose 2 : α) * (n : α) ^ m := by
      have hnat : (n : α) ^ (m + 1) ≤
          n.descFactorial (m + 1) + ((m + 1).choose 2 : α) * (n : α) ^ m := by
        exact_mod_cast Nat.pow_succ_le_descFactorial_add_choose_two_mul_pow n m
      exact sub_le_iff_le_add'.mpr hnat
    rw [abs_of_nonpos (sub_nonpos.mpr ((div_le_one hpow).mpr hdf_le)), neg_sub,
      one_sub_div hpow.ne']
    calc ((n : α) ^ (m + 1) - n.descFactorial (m + 1)) / (n : α) ^ (m + 1)
        ≤ (((m + 1).choose 2 : α) * (n : α) ^ m) / (n : α) ^ (m + 1) :=
          div_le_div_of_nonneg_right hsub_le hpow.le
      _ = ((m + 1).choose 2 : α) / n := by
          rw [_root_.pow_succ', mul_div_mul_right _ _ (pow_pos hnα m).ne']

end Nat
