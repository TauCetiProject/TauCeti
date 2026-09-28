/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Lemmas

/-!
# The abc triple of a rational number

Writing a rational `q` in lowest terms as `a / c` with `a = q.num` and `c = q.den`, and setting
`b = c - a`, gives integers with `a + b = c`, pairwise coprime since `a` and `c` are
(`Rat.isCoprime_num_den`). This is how an abc triple is read off a rational number, as for the
`j`-invariant of an elliptic curve over `ℚ` divided by `1728`. The three integers are nonzero
exactly when `q ≠ 0` and `q ≠ 1`: `a = 0` means `q = 0` (`Rat.num_ne_zero`), `c` is a
denominator, and `b = 0` means `q = 1`.

## Main results

* `Rat.den_sub_num_ne_zero`: `q.den - q.num ≠ 0` if and only if `q ≠ 1`.
-/

public section

namespace Rat

/-- The middle term `q.den - q.num` of the abc triple of `q` is nonzero if and only if `q ≠ 1`. -/
@[simp]
theorem den_sub_num_ne_zero (q : ℚ) : (q.den : ℤ) - q.num ≠ 0 ↔ q ≠ 1 := by
  refine sub_ne_zero.trans (not_congr ⟨fun h => ?_, fun h => by simp [h]⟩)
  rw [← q.num_div_den, ← h, Int.cast_natCast, div_self (Nat.cast_ne_zero.mpr q.den_ne_zero)]

end Rat

end
