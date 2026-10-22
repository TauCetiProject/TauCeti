/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Order.MinMax

/-!
# Rescaling a clamped time

In a linearly ordered semifield, the fraction `max 0 (min t d) / d` of a time interval of length
`d` elapsed at time `t`, rescaled by `d / D`, is the clamped time `max 0 (min t d)` measured in
units of `D`. This holds also for `d = 0`, where the clamped time vanishes. It is how a
constant-speed run along a piece `(d / D) • v` of a segment `v` of duration `D` is compared with
the run along `v`.

## Main results

* `TauCeti.max_zero_min_div_mul_div`: `max 0 (min t d) / d * (d / D) = max 0 (min t d) / D`.
-/

public section

namespace TauCeti

variable {α : Type*} [Semifield α] [LinearOrder α]

/-- The elapsed fraction `max 0 (min t d) / d` of a time interval of length `d`, rescaled by
`d / D`, is the clamped time `max 0 (min t d)` divided by `D`, also when `d = 0`. -/
theorem max_zero_min_div_mul_div (t d D : α) :
    max 0 (min t d) / d * (d / D) = max 0 (min t d) / D := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · rw [div_mul_div_comm, mul_comm (max 0 (min t d)) d, mul_div_mul_left _ _ hd]

end TauCeti
