/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Defs

/-!
# Clamping to a split interval

In a linearly ordered additive group, clamping `t` to the interval `[0, a + b]`, for `0 ≤ a` and
`0 ≤ b`, is the sum of clamping `t` to `[0, a]` and clamping the remaining time `t - a` to
`[0, b]`. This is how a constant-speed run along a segment of duration `a + b` splits into its
runs along the two pieces of durations `a` and `b`.

## Main results

* `TauCeti.max_zero_min_add`: `max 0 (min t (a + b)) = max 0 (min t a) + max 0 (min (t - a) b)`.
-/

public section

namespace TauCeti

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- Clamping `t` to `[0, a + b]` is the sum of clamping `t` to `[0, a]` and clamping the remaining
time `t - a` to `[0, b]`. -/
theorem max_zero_min_add {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) (t : α) :
    max 0 (min t (a + b)) = max 0 (min t a) + max 0 (min (t - a) b) := by
  rcases le_total t 0 with ht | ht
  · rw [max_eq_left (min_le_of_left_le ht), max_eq_left (min_le_of_left_le ht),
      max_eq_left (min_le_of_left_le (sub_nonpos.2 (ht.trans ha))), zero_add]
  rcases le_total t a with hta | hat
  · rw [min_eq_left (hta.trans (le_add_of_nonneg_right hb)), min_eq_left hta, max_eq_right ht,
      max_eq_left (min_le_of_left_le (sub_nonpos.2 hta)), add_zero]
  rw [min_eq_right hat, max_eq_right ha, max_eq_right (le_min ht (add_nonneg ha hb)),
    max_eq_right (le_min (sub_nonneg.2 hat) hb)]
  rcases le_total t (a + b) with htb | hbt
  · rw [min_eq_left htb, min_eq_left (sub_le_iff_le_add'.2 htb), add_sub_cancel]
  · rw [min_eq_right hbt, min_eq_right (le_sub_iff_add_le'.2 hbt)]

end TauCeti
