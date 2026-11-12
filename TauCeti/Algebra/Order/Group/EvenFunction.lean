/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Algebra.Order.Group.Abs

/-!
# Odd functions on a linearly ordered group

Two odd functions on a linearly ordered additive group agree at `x` as soon as they agree at
`|x|` (when `0 < |x|`): an identity between odd functions reduces to positive arguments.
-/

public section

namespace Function

variable {α β : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  [AddCommGroup β] [HasUniqueDiv β]

/-- Odd functions agree at `x` if they agree at `|x|` whenever `0 < |x|`. -/
theorem Odd.eq_of_eq_abs {f g : α → β} (hf : f.Odd) (hg : g.Odd) {x : α}
    (h : 0 < |x| → f |x| = g |x|) : f x = g x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := h (abs_pos.mpr hx.ne)
    rwa [abs_of_neg hx, hf, hg, neg_inj] at h
  · rw [hf.map_zero, hg.map_zero]
  · simpa [abs_of_pos hx] using h (abs_pos.mpr hx.ne')

end Function
