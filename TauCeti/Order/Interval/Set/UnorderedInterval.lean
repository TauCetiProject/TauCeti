/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Membership in an open unordered interval

In a linear order, a point lies in the open unordered interval `Set.uIoo a b` exactly when it
lies strictly between `a` and `b` in one of the two orders of the endpoints. This is the
open-interval form of Mathlib's `Set.mem_uIcc`.
-/

public section

namespace Set

variable {α : Type*} [LinearOrder α] {a b x : α}

/-- A point lies in the open unordered interval `uIoo a b` exactly when it lies strictly between
`a` and `b`, in either order. -/
theorem mem_uIoo : x ∈ uIoo a b ↔ a < x ∧ x < b ∨ b < x ∧ x < a := by
  simp [uIoo_eq_union]

end Set
