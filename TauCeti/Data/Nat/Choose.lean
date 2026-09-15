/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Elementary identities for binomial coefficients

This file records arithmetic identities involving natural-number binomial coefficients.

## Main results

* `Nat.choose_two_add_mul_succ_div_two`: the sum of the second binomial coefficient and
  the triangular number is the corresponding square.
* `Nat.add_choose_two`: the second binomial coefficient of a sum, with its cross term.
-/

public section

namespace Nat

/-- The sum of `N.choose 2` and the `N`th triangular number is `N ^ 2`. -/
theorem choose_two_add_mul_succ_div_two (N : ℕ) :
    N.choose 2 + N * (N + 1) / 2 = N * N := by
  rw [Nat.choose_two_right]
  apply Nat.mul_right_cancel (by norm_num : 0 < 2)
  rw [Nat.add_mul, Nat.div_mul_cancel (Nat.even_mul_pred_self N).two_dvd,
    Nat.div_mul_cancel (Nat.even_mul_succ_self N).two_dvd]
  by_cases hN : N = 0
  · simp [hN]
  · rw [← Nat.mul_add]
    have hsum : N - 1 + (N + 1) = 2 * N := by omega
    rw [hsum]
    ring

/-- The second binomial coefficient of a sum: `C(m + n, 2) = C(m, 2) + C(n, 2) + mn`. -/
theorem add_choose_two (m n : ℕ) : (m + n).choose 2 = m.choose 2 + n.choose 2 + m * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : (m + (n + 1)).choose 2 = (m + n).choose 1 + (m + n).choose 2 := by
        rw [← Nat.add_assoc]
        exact Nat.choose_succ_succ (m + n) 1
      have h2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
      rw [h1, h2, ih, Nat.choose_one_right, Nat.choose_one_right]
      ring

end Nat
