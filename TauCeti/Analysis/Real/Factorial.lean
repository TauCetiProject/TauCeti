/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.IntervalCases

/-!
# The unit threshold for `π ^ n / n!`

The ratio is at most one in dimension zero and in dimensions at least seven. This is the
threshold for dropping the one-row volume factor in Hua's complex matrix integral bound.
-/

public section

namespace Real

/-- The factorial dominates the corresponding power of `π` exactly at zero and from seven on. -/
theorem pi_pow_le_factorial_iff {n : ℕ} : π ^ n ≤ (n.factorial : ℝ) ↔ n = 0 ∨ 7 ≤ n := by
  constructor
  · intro h
    by_contra! hn
    have hlo : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn.1
    have hhi : n ≤ 6 := by omega
    have h₃ := (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) pi_gt_three.le n).trans h
    interval_cases n <;> norm_num [Nat.factorial] at h₃
  · rintro (rfl | hn)
    · simp
    induction n, hn using Nat.le_induction with
    | base =>
      exact (pow_le_pow_left₀ pi_pos.le pi_lt_d2.le 7).trans
        (by norm_num [Nat.factorial])
    | succ n hn ih =>
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, mul_comm ((n + 1 : ℕ) : ℝ)]
      have hn' : (4 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (by omega : 4 ≤ n + 1)
      exact mul_le_mul ih (pi_lt_four.le.trans hn') pi_pos.le (by positivity)

end Real
