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

## Main result

* `Nat.choose_two_add_mul_succ_div_two`: the sum of the second binomial coefficient and
  the triangular number is the corresponding square.
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

end Nat
