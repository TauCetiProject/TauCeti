/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Order.Bounds.Defs
import Mathlib.Algebra.Order.Ring.Cast

/-!
# The least positive integer multiple

In a linearly ordered ring, the least positive integer multiple of a positive element `c` is `c`
itself. This reads off least periods from a description of all periods as the multiples `n c`,
`n ∈ ℤ`.
-/

public section

namespace TauCeti

/-- **The least positive integer multiple** of a positive element `c` of a linearly ordered ring
is `c`. -/
theorem isLeast_pos_int_mul {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {c : R}
    (hc : 0 < c) : IsLeast {x : R | 0 < x ∧ ∃ n : ℤ, x = n * c} c := by
  refine ⟨⟨hc, 1, by simp⟩, ?_⟩
  rintro x ⟨hx, n, rfl⟩
  have hn : (0 : R) < n := pos_of_mul_pos_left hx hc.le
  have hn' : (1 : R) ≤ n := by exact_mod_cast Int.cast_pos.1 hn
  simpa using mul_le_mul_of_nonneg_right hn' hc.le

end TauCeti
