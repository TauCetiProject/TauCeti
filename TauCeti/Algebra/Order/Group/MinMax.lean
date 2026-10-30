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
  grind

end TauCeti
