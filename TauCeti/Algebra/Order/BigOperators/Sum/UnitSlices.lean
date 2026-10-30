/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Defs

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith

/-!
# Slicing a number into unit pieces

For `0 ≤ a ≤ k`, the interval `[0, a)` is cut by the unit intervals `[l, l + 1)`, `l < k`, into
pieces of lengths `max (min 1 (a - l)) 0`, which add up to `a`. This is the length computation
behind constructions which assign to each of `k` unit offsets the part of `[0, a)` it meets, such
as the barycentric coordinates of the preimage of a point under the edgewise subdivision
homeomorphism.
-/

public section

namespace Finset

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- For `0 ≤ a ≤ k`, the lengths `max (min 1 (a - l)) 0` of the intersections of `[0, a)` with
the unit intervals `[l, l + 1)`, `l < k`, add up to `a`. -/
theorem sum_range_max_min_one_sub (k : ℕ) {a : R} (h₀ : 0 ≤ a) (h₁ : a ≤ k) :
    ∑ l ∈ range k, max (min 1 (a - l)) 0 = a := by
  induction k generalizing a with
  | zero => simp only [Nat.cast_zero] at h₁; simp; linarith
  | succ k ih =>
    rw [sum_range_succ']
    push_cast at h₁ ⊢
    rcases le_or_gt 1 a with ha | ha
    · have hk := ih (a := a - 1) (by linarith) (by linarith)
      rw [min_eq_left (by linarith), max_eq_left zero_le_one]
      simp only [sub_add_eq_sub_sub_swap, hk, sub_add_cancel]
    · rw [sum_eq_zero fun l _ => ?_, sub_zero, min_eq_right ha.le, max_eq_left h₀, zero_add]
      have : (0 : R) ≤ l := Nat.cast_nonneg l
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]

end Finset
