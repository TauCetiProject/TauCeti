/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.GCongr

/-!
# A Cauchy bound for roots of monic quadratics

In a linearly ordered ring, a root `y` of `Y² + bY - c` satisfies `|y| < max |b| |c| + 1`: the
Cauchy bound for this quadratic. Over `ℤ` this bounds `|y|` by `max |b| |c|`, which makes searches
for integer solutions of equations quadratic in one coordinate finite.
-/

public section

namespace TauCeti

/-- The Cauchy bound for a root of `Y² + bY = c`: `|y| < max |b| |c| + 1`. -/
theorem abs_lt_max_add_one_of_sq_add_mul_eq {R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] {y b c : R} (h : y ^ 2 + b * y = c) :
    |y| < max |b| |c| + 1 := by
  have hle : |y| * |y| ≤ |b| * |y| + |c| :=
    calc |y| * |y| = |c - b * y| := by rw [← abs_mul, ← h, add_sub_cancel_right, sq]
      _ ≤ |c| + |b * y| := abs_sub _ _
      _ = |b| * |y| + |c| := by rw [abs_mul, add_comm]
  by_contra! hy
  refine hle.not_gt ?_
  calc |b| * |y| + |c| < |b| * |y| + (max |b| |c| + 1) := by
        gcongr; exact (le_max_right _ _).trans_lt (lt_add_one _)
    _ ≤ max |b| |c| * |y| + |y| :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg y)) hy
    _ = (max |b| |c| + 1) * |y| := by rw [add_mul, one_mul]
    _ ≤ |y| * |y| := mul_le_mul_of_nonneg_right hy (abs_nonneg y)

end TauCeti
