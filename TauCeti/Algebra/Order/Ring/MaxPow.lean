/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring

/-!
# A sixth-power bound by a maximum

For natural numbers `x`, `y`, the product `(x * y) ^ 6` is at most `(max (x ^ 3) (y ^ 2)) ^ 5`
(`TauCeti.mul_pow_six_le_max_pow_five`). Consequently a bound `g * R ≤ K * (x * y * N)` gives
`(g * R) ^ 6 ≤ K ^ 6 * (max (x ^ 3) (y ^ 2)) ^ 5 * N ^ 6` (`TauCeti.pow_six_le_of_le_mul`), the
sixth-power bookkeeping of the estimates of a Weierstrass invariant pair `(c₄, c₆)` against
`max (|c₄| ^ 3, c₆ ^ 2)`.
-/

public section

namespace TauCeti

/-- For natural numbers `x`, `y`, one has `(x * y) ^ 6 ≤ (max (x ^ 3) (y ^ 2)) ^ 5`. -/
theorem mul_pow_six_le_max_pow_five (x y : ℕ) :
    (x * y) ^ 6 ≤ (max (x ^ 3) (y ^ 2)) ^ 5 :=
  calc (x * y) ^ 6 = (x ^ 3) ^ 2 * (y ^ 2) ^ 3 := by ring
    _ ≤ (max (x ^ 3) (y ^ 2)) ^ 2 * (max (x ^ 3) (y ^ 2)) ^ 3 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left _ _) 2)
        (Nat.pow_le_pow_left (le_max_right _ _) 3)
    _ = (max (x ^ 3) (y ^ 2)) ^ 5 := by ring

/-- A bound `g * R ≤ K * (x * y * N)` bounds `(g * R) ^ 6` by `K ^ 6 * M ^ 5 * N ^ 6`, where
`M = max (x ^ 3) (y ^ 2)`. -/
theorem pow_six_le_of_le_mul {x y N g R K : ℕ} (h : g * R ≤ K * (x * y * N)) :
    (g * R) ^ 6 ≤ K ^ 6 * (max (x ^ 3) (y ^ 2)) ^ 5 * N ^ 6 :=
  calc (g * R) ^ 6 ≤ (K * (x * y * N)) ^ 6 := Nat.pow_le_pow_left h 6
    _ = K ^ 6 * (x * y) ^ 6 * N ^ 6 := by ring
    _ ≤ K ^ 6 * (max (x ^ 3) (y ^ 2)) ^ 5 * N ^ 6 := 
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (mul_pow_six_le_max_pow_five x y))

end TauCeti
