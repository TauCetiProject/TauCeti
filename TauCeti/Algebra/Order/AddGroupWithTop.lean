/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AddGroupWithTop

/-!
# Translating lower bounds in `WithTop G`

For a linearly ordered additive commutative group `G`, translating an element `x : WithTop G`
by a finite `c : G` translates its finite lower bounds by the same amount. These are the
`WithTop` versions of `le_sub_iff_add_le` and `sub_le_sub_iff_right`, which do not apply
directly since `WithTop G` is not a group.

## Main results

* `WithTop.coe_le_add_coe_iff`: `k ≤ x + c ↔ k - c ≤ x`.
* `WithTop.coe_sub_le_sub_coe_iff`: `k - c ≤ x - c ↔ k ≤ x`.
-/

public section

namespace WithTop

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] {x : WithTop G}
  {k c : G}

/-- A finite lower bound `k` of `x + c` is a lower bound `k - c` of `x`. -/
theorem coe_le_add_coe_iff : (k : WithTop G) ≤ x + c ↔ ((k - c : G) : WithTop G) ≤ x := by
  rw [← add_le_add_iff_left_of_ne_top (a := (c : WithTop G)) coe_ne_top
    (b := ((k - c : G) : WithTop G)), ← coe_add, sub_add_cancel]

/-- Subtracting a finite `c` from both sides of a finite lower bound preserves it. -/
theorem coe_sub_le_sub_coe_iff : ((k - c : G) : WithTop G) ≤ x - c ↔ (k : WithTop G) ≤ x := by
  rw [LinearOrderedAddCommGroup.coe_sub,
    LinearOrderedAddCommGroupWithTop.sub_le_sub_iff_left_of_ne_top coe_ne_top]

end WithTop
