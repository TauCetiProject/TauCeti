/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A polynomial barrier dominates a bounded function

If `r ≤ M` and `n` is larger than `|M| / ε`, then the barrier `ε * (c * (1 + n ^ 2))` with
`c ≥ 1` exceeds `r`.

## Main results

* `TauCeti.sub_mul_mul_one_add_sq_neg_of_lt`: the strict inequality
  `r - ε * (c * (1 + n ^ 2)) < 0`.
-/

public section

namespace TauCeti

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- The barrier `ε * (c * (1 + n ^ 2))` dominates an upper bound `r ≤ M` once the radius `n`
exceeds `|M| / ε`, for `c ≥ 1` and `ε > 0`. -/
theorem sub_mul_mul_one_add_sq_neg_of_lt {c ε M r n : α} (hc : 1 ≤ c) (hε : 0 < ε)
    (hr : r ≤ M) (hn : |M| / ε < n) :
    r - ε * (c * (1 + n ^ 2)) < 0 := by
  have h2 : |M| < ε * n := by
    rw [← div_lt_iff₀' hε]
    linarith
  have h3 : n ≤ 1 + n ^ 2 := by
    have : 0 ≤ |M| / ε := by positivity
    nlinarith [sq_nonneg (n - 1)]
  have h4 : ε * (1 + n ^ 2) ≤ ε * (c * (1 + n ^ 2)) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hc) hε.le
  nlinarith [le_abs_self M, mul_le_mul_of_nonneg_left h3 hε.le]

end TauCeti
