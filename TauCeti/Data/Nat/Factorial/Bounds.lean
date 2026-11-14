/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import TauCeti.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Falling-factorial ratio bounds in ordered fields

Dividing the collision bound `n ^ k ≤ n.descFactorial k + k.choose 2 * n ^ (k - 1)` by `n ^ k`
quantifies how close the ratio `(n.descFactorial k : K) / n ^ k` is to `1` in any linearly ordered
field `K`: it lies in `[0, 1]` for all `n, k`, and for `n ≠ 0` its deficit from `1` is at most
`k.choose 2 / n`.

## Main results

* `Nat.descFactorial_div_pow_le_one`: `(n.descFactorial k : K) / n ^ k ≤ 1`.
* `Nat.one_sub_descFactorial_div_pow_le`: `1 - (n.descFactorial k : K) / n ^ k ≤ k.choose 2 / n`
  for `n ≠ 0`.
* `Nat.abs_descFactorial_div_pow_sub_one_le`:
  `|(n.descFactorial k : K) / n ^ k - 1| ≤ k.choose 2 / n` for `n ≠ 0`.
-/

public section

namespace Nat

/-- Cast into a linearly ordered semifield, the ratio `(n.descFactorial k : K) / n ^ k` is at most
`1` (including `n = 0`, by `0 / 0 = 0`). -/
theorem descFactorial_div_pow_le_one {K : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] (n k : ℕ) :
    (n.descFactorial k : K) / (n : K) ^ k ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast descFactorial_le_pow n k) (by positivity)

/-- For `n ≠ 0` in a linearly ordered field, `1 - (n.descFactorial k : K) / n ^ k` is at most
`(k.choose 2 : K) / n`. -/
theorem one_sub_descFactorial_div_pow_le {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    1 - (n.descFactorial k : K) / (n : K) ^ k ≤ (k.choose 2 : K) / n := by
  rcases k with _ | m
  · simp
  · have hn_pos : (0 : K) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hpow_pos : (0 : K) < (n : K) ^ (m + 1) := pow_pos hn_pos _
    have hle : ((n : K) ^ (m + 1) - (n.descFactorial (m + 1) : K)) ≤
        ((m + 1).choose 2 : K) * (n : K) ^ m := by
      have hnat : (n ^ (m + 1) : K) ≤
          (n.descFactorial (m + 1) : K) + ((m + 1).choose 2 : K) * (n : K) ^ m := by
        exact_mod_cast pow_le_descFactorial_add_choose_two_mul_pow n (m + 1)
      linarith
    calc
      1 - (n.descFactorial (m + 1) : K) / (n : K) ^ (m + 1)
        = ((n : K) ^ (m + 1) - (n.descFactorial (m + 1) : K)) / (n : K) ^ (m + 1) := by
          rw [sub_div, div_self hpow_pos.ne']
      _ ≤ (((m + 1).choose 2 : K) * (n : K) ^ m) / (n : K) ^ (m + 1) :=
          div_le_div_of_nonneg_right hle hpow_pos.le
      _ = ((m + 1).choose 2 : K) / n := by
          rw [_root_.pow_succ']
          field_simp [hn_pos.ne']

/-- For `n ≠ 0` in a linearly ordered field, `|(n.descFactorial k : K) / n ^ k - 1|` is at most
`(k.choose 2 : K) / n`. -/
theorem abs_descFactorial_div_pow_sub_one_le {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    |(n.descFactorial k : K) / (n : K) ^ k - 1| ≤ (k.choose 2 : K) / n := by
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (descFactorial_div_pow_le_one n k))]
  exact one_sub_descFactorial_div_pow_le hn k

end Nat
