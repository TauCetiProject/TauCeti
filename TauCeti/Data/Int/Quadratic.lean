/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

/-!
# A bound for integer roots of monic quadratics

An integer satisfying `y² + by = c` has absolute value at most `|b| + |c| + 1`.
This bound makes searches for integer solutions of equations quadratic in one coordinate finite.
-/

public section

namespace TauCeti

/-- An integer root of `Y² + bY = c` is bounded by the absolute values of its coefficients. -/
theorem abs_le_of_quadratic_eq {y b c : ℤ} (h : y ^ 2 + b * y = c) :
    |y| ≤ |b| + |c| + 1 := by
  have hle : |y| ^ 2 ≤ |b| * |y| + |c| := by
    have h' : y ^ 2 = c - b * y := by nlinarith only [h]
    calc
      |y| ^ 2 = |y ^ 2| := by rw [abs_pow]
      _ = |c - b * y| := by rw [h']
      _ ≤ |c| + |b * y| := by simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le c (-(b * y)))
      _ = |b| * |y| + |c| := by rw [abs_mul]; omega
  by_contra hn
  have hlarge : |b| + |c| + 1 < |y| := lt_of_not_ge hn
  have hy_nonneg := abs_nonneg y
  have hb_nonneg := abs_nonneg b
  have hc_nonneg := abs_nonneg c
  have hprod₁ : 0 ≤ (|y| - |b| - |c| - 1) * |y| :=
    mul_nonneg (by omega) hy_nonneg
  have hprod₂ : 0 ≤ |c| * (|y| - 1) :=
    mul_nonneg hc_nonneg (by omega)
  have hpos : 0 < |y| := by omega
  nlinarith only [hle, hprod₁, hprod₂, hpos]

end TauCeti
