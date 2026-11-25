/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Positive roots in real closed fields

In a real closed field every positive element has a positive `n`-th root for every `n ≠ 0`.
This refines Mathlib's `IsRealClosed.exists_eq_pow_of_nonneg`, which provides some root.

## Main results

* `IsRealClosed.exists_pos_pow_eq_of_pos`: a positive element is the `n`-th power of a positive
  element.
-/

public section

namespace IsRealClosed

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- In a real closed field, a positive element is the `n`-th power of a positive element, for every
`n ≠ 0`. -/
theorem exists_pos_pow_eq_of_pos {x : R} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ∃ r, 0 < r ∧ r ^ n = x := by
  obtain ⟨r, rfl⟩ := exists_eq_pow_of_nonneg hx.le hn
  have hr : r ≠ 0 := by rintro rfl; simp [zero_pow hn] at hx
  exact ⟨|r|, abs_pos.2 hr, by rw [pow_abs, abs_of_pos hx]⟩

end IsRealClosed
