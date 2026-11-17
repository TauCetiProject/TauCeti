/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Linarith

/-!
# A growth inequality in the natural numbers

If `m * (n + 1) ≤ n * d + n` then `m ≤ d`: the left side grows by `m` with each step of `n`
while the right side grows by `d + 1`, so `m` cannot exceed `d`. This is the numerical step of a
growth argument that compares two linear bounds in an auxiliary parameter `n`.

## Main results

* `Nat.le_of_mul_succ_le_mul_add`: `m * (n + 1) ≤ n * d + n → m ≤ d`.
-/

public section

namespace Nat

/-- If `m * (n + 1) ≤ n * d + n`, then `m ≤ d`. -/
theorem le_of_mul_succ_le_mul_add {m d n : ℕ} (h : m * (n + 1) ≤ n * d + n) : m ≤ d := by
  by_contra hnot
  have hgt : d + 1 ≤ m := Nat.lt_of_not_ge hnot
  have hmul := Nat.mul_le_mul_right (n + 1) hgt
  nlinarith

end Nat
