/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Common

/-!
# Linear inequality comparing `(p - 1) * e` and `(p - 2) * (2 * e)`

For `3 ≤ p`, `p - 1 ≤ 2 * (p - 2)`, hence `(p - 1) * e ≤ (p - 2) * (2 * e)` for every `e : ℕ`.

## Main results

* `Nat.sub_one_mul_le_two_mul`: `(p - 1) * e ≤ (p - 2) * (2 * e)` for `3 ≤ p`.
-/

public section

namespace Nat

/-- For `3 ≤ p` and `e : ℕ`, `(p - 1) * e ≤ (p - 2) * (2 * e)`. -/
theorem sub_one_mul_le_two_mul {p : ℕ} (hp : 3 ≤ p) (e : ℕ) :
    (p - 1) * e ≤ (p - 2) * (2 * e) := by
  calc (p - 1) * e ≤ ((p - 2) * 2) * e := Nat.mul_le_mul_right e (by omega)
    _ = (p - 2) * (2 * e) := Nat.mul_assoc _ _ _

end Nat
