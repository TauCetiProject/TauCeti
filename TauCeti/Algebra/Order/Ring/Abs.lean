/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.NoncommRing

/-!
# Absolute values of products in linearly ordered rings

If `x` and `y` are each within `e` of a nonnegative `q` with `q e ≤ e q` (for instance when `q`
and `e` commute), their product is within `e (2q + e)` of `q²`: the quantitative form of
continuity of multiplication used when a measure is compared with its own square. When
`|b| ≤ 1` and `|c| ≤ 1`, the products `a c` and `b d` differ by at most `|a - b| + |c - d|`. When
`|d| ≤ 1`, replacing `b` by `c` inside `|a - d b|` costs at most `|b - c|`. Finally, `|a| ≤ a b`
with `0 ≤ b` forces `0 ≤ a`.

Everything is stated for any linearly ordered ring, commutative or not.
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]

/-- An element `a` with `|a| ≤ a * b` for some `b ≥ 0` is nonnegative. -/
theorem nonneg_of_abs_le_mul {a b : R} (h : |a| ≤ a * b) (hb : 0 ≤ b) : 0 ≤ a := by
  by_contra! ha
  exact (abs_pos.2 ha.ne).not_ge (h.trans (mul_nonpos_of_nonpos_of_nonneg ha.le hb))

/-- `|x y - q²| ≤ e (2q + e)` when `x` and `y` are each within `e` of `q ≥ 0` and `q e ≤ e q`
(for instance when `q` and `e` commute); neither `x` nor `y` need be nonnegative. -/
theorem abs_mul_sub_mul_self_le {x y q e : R} (hx : |x - q| ≤ e) (hy : |y - q| ≤ e)
    (hq0 : 0 ≤ q) (hqe : q * e ≤ e * q) :
    |x * y - q * q| ≤ e * (2 * q + e) := by
  have he : 0 ≤ e := (abs_nonneg _).trans hx
  calc |x * y - q * q| = |(x - q) * (y - q) + ((x - q) * q + q * (y - q))| := by noncomm_ring
    _ ≤ |(x - q) * (y - q)| + (|(x - q) * q| + |q * (y - q)|) :=
      (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ = |x - q| * |y - q| + (|x - q| * q + q * |y - q|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hq0]
    _ ≤ e * e + (e * q + e * q) :=
      add_le_add (mul_le_mul hx hy (abs_nonneg _) he)
        (add_le_add (mul_le_mul_of_nonneg_right hx hq0)
          ((mul_le_mul_of_nonneg_left hy hq0).trans hqe))
    _ = e * (2 * q + e) := by rw [mul_add, two_mul, mul_add, add_comm]

/-- `|a c - b d| ≤ |a - b| + |c - d|` when `|b| ≤ 1` and `|c| ≤ 1`. -/
theorem abs_mul_sub_mul_le {a b c d : R} (hb : |b| ≤ 1) (hc : |c| ≤ 1) :
    |a * c - b * d| ≤ |a - b| + |c - d| :=
  calc |a * c - b * d| = |(a - b) * c + b * (c - d)| := by noncomm_ring
    _ ≤ |a - b| * |c| + |b| * |c - d| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ |a - b| + |c - d| :=
      add_le_add (mul_le_of_le_one_right (abs_nonneg _) hc)
        (mul_le_of_le_one_left (abs_nonneg _) hb)

/-- Replacing `b` by `c` inside `|a - d * b|` costs at most `|b - c|` when `|d| ≤ 1`. -/
theorem abs_sub_mul_le_of_abs_le_one {a b c d : R} (hd : |d| ≤ 1) :
    |a - d * c| ≤ |a - d * b| + |b - c| :=
  calc |a - d * c| = |(a - d * b) + d * (b - c)| := by congr 1; noncomm_ring
    _ ≤ |a - d * b| + |d * (b - c)| := abs_add_le _ _
    _ ≤ |a - d * b| + |b - c| := by
      rw [abs_mul]
      exact add_le_add_right (mul_le_of_le_one_left (abs_nonneg _) hd) _

end TauCeti
