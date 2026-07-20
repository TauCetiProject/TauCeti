/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Field.Basic

/-!
# A nonzero element is not its own negation away from characteristic two

In a field where `2 ≠ 0`, a nonzero element `x` differs from `-x`: otherwise `2 x = 0` would
force `x = 0`. This is the elementary characteristic-`≠ 2` fact behind separating the two square
roots `±√d` of a nonzero radicand.

## Main result

* `TauCeti.ne_neg_of_ne_zero`: `x ≠ 0 → x ≠ -x` when `2 ≠ 0`.
-/

public section

namespace TauCeti

/-- In a field with `2 ≠ 0`, a nonzero element is not equal to its own negation. -/
theorem ne_neg_of_ne_zero {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) {x : L} (hx : x ≠ 0) :
    x ≠ -x := by
  intro h
  apply hx
  have hxx : x + x = 0 := by rw [← sub_neg_eq_add, ← h, sub_self]
  have h2x : (2 : L) * x = 0 := by rw [two_mul]; exact hxx
  exact (mul_eq_zero.mp h2x).resolve_left h2

end TauCeti
