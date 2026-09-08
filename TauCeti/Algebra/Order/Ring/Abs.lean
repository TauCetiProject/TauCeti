/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Products of nearby reals

If `x` and a nonnegative `y` are each within `e` of a nonnegative `q`, their product is within
`e (2q + e)` of `q²`: the quantitative form of continuity of multiplication used when a measure is
compared with its own square. Stated for any linearly ordered commutative ring.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `|x y - q²| ≤ e (2q + e)` when `x` is within `e` of `q` and so is `y`, with `y` and `q`
nonnegative; `x` may have either sign. -/
theorem abs_mul_sub_mul_self_le {x y q e : R} (hx : |x - q| ≤ e) (hy : |y - q| ≤ e)
    (hy0 : 0 ≤ y) (hq0 : 0 ≤ q) :
    |x * y - q * q| ≤ e * (2 * q + e) := by
  have he : 0 ≤ e := (abs_nonneg _).trans hx
  have heq : x * y - q * q = (x - q) * y + q * (y - q) := by ring
  have hyq : y ≤ q + e := by linarith [(abs_le.1 hy).2]
  calc |x * y - q * q| ≤ |(x - q) * y| + |q * (y - q)| := by
        rw [heq]; exact abs_add_le _ _
    _ = |x - q| * y + q * |y - q| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hy0, abs_of_nonneg hq0]
    _ ≤ e * (q + e) + q * e := by gcongr
    _ = e * (2 * q + e) := by ring

end TauCeti
