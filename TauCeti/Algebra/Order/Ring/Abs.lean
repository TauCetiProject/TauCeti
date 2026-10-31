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
compared with its own square. When `|b| ≤ 1` and `|c| ≤ 1`, the products `a c` and `b d` differ by
at most `|a - b| + |c - d|`. When `0 ≤ d ≤ 1`, replacing `b` by `c` inside `|a - d b|` costs at
most `|b - c|`. All are stated for any linearly ordered commutative ring.
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

/-- `|a c - b d| ≤ |a - b| + |c - d|` when `|b| ≤ 1` and `|c| ≤ 1`. -/
theorem abs_mul_sub_mul_le {a b c d : R} (hb : |b| ≤ 1) (hc : |c| ≤ 1) :
    |a * c - b * d| ≤ |a - b| + |c - d| :=
  calc |a * c - b * d| = |(a - b) * c + b * (c - d)| := by ring_nf
    _ ≤ |a - b| * |c| + |b| * |c - d| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ |a - b| * 1 + 1 * |c - d| := by gcongr
    _ = |a - b| + |c - d| := by ring

/-- Replacing `b` by `c` inside `|a - d * b|` costs at most `|b - c|` when `0 ≤ d ≤ 1`. -/
theorem abs_sub_mul_le_of_le_one {a b c d : R} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    |a - d * c| ≤ |a - d * b| + |b - c| :=
  calc |a - d * c| = |(a - d * b) + d * (b - c)| := by congr 1; ring
    _ ≤ |a - d * b| + |d * (b - c)| := abs_add_le _ _
    _ ≤ |a - d * b| + |b - c| := by
      rw [abs_mul, abs_of_nonneg hd₀]
      exact add_le_add_right (mul_le_of_le_one_left (abs_nonneg _) hd₁) _

end TauCeti
