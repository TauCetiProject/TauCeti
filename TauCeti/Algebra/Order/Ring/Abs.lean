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

If `x` and `y` are each within `e` of a nonnegative `q`, their product is within
`e (2q + e)` of `q²`: the quantitative form of continuity of multiplication used when a measure is
compared with its own square. Stated for any linearly ordered commutative ring.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `|x y - q²| ≤ e (2q + e)` when `x` and `y` are each within `e` of `q ≥ 0`; neither `x` nor
`y` need be nonnegative. -/
theorem abs_mul_sub_mul_self_le {x y q e : R} (hx : |x - q| ≤ e) (hy : |y - q| ≤ e)
    (hq0 : 0 ≤ q) :
    |x * y - q * q| ≤ e * (2 * q + e) := by
  have he : 0 ≤ e := (abs_nonneg _).trans hx
  have hx' := abs_le.1 hx
  have hy' := abs_le.1 hy
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg he he, mul_nonneg he hq0, hx'.1, hx'.2, hy'.1, hy'.2]

end TauCeti
