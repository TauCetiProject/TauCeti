/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Abs

/-!
# Clamping in ordered additive groups

In a linearly ordered additive group, clamping to a symmetric interval is bounded by its
height and does not increase absolute value. Clamping `t` to `[0, a + b]`, for `0 ≤ a` and
`0 ≤ b`, is the sum of clamping `t` to `[0, a]` and clamping the remaining time `t - a` to
`[0, b]`. This is how a constant-speed run along a segment of duration `a + b` splits into its
runs along the two pieces of durations `a` and `b`.

## Main results

* `TauCeti.max_zero_min_add`: `max 0 (min t (a + b)) = max 0 (min t a) + max 0 (min (t - a) b)`.
* `TauCeti.abs_max_min_le`: the max-min clipping formula is bounded by `|M|` for any height `M`.
* `TauCeti.abs_max_min_le_abs`: clipping at a nonnegative height does not increase absolute value.
-/

public section

namespace TauCeti

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- Clamping `t` to `[0, a + b]` is the sum of clamping `t` to `[0, a]` and clamping the remaining
time `t - a` to `[0, b]`. -/
theorem max_zero_min_add {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) (t : α) :
    max 0 (min t (a + b)) = max 0 (min t a) + max 0 (min (t - a) b) := by
  grind

/-- The max-min clipping formula is bounded by the absolute value of its height,
including when the height is negative. -/
theorem abs_max_min_le (M x : α) : |max (-M) (min M x)| ≤ |M| := by
  rw [abs_le]
  constructor <;> grind [le_abs_self, neg_abs_le]

/-- Clipping to a symmetric interval does not increase absolute value. -/
theorem abs_max_min_le_abs {M : α} (hM : 0 ≤ M) (x : α) :
    |max (-M) (min M x)| ≤ |x| := by
  rw [abs_le]
  constructor <;> grind [le_abs_self, neg_abs_le]

end TauCeti
