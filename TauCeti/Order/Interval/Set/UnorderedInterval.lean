/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Membership in an open unordered interval

In a linear order, a point lies in the open unordered interval `Set.uIoo a b` exactly when it
lies strictly between `a` and `b` in one of the two orders of the endpoints. This is the
open-interval form of Mathlib's `Set.mem_uIcc`. A function that maps the unordered interval
`uIcc a b` into a set still does so after reflecting the argument about the midpoint
(`Set.MapsTo.comp_const_sub_uIcc`).
-/

public section

namespace Set

variable {α : Type*} [LinearOrder α] {a b x : α}

/-- A point lies in the open unordered interval `uIoo a b` exactly when it lies strictly between
`a` and `b`, in either order. -/
theorem mem_uIoo : x ∈ uIoo a b ↔ a < x ∧ x < b ∨ b < x ∧ x < a := by
  simp [uIoo_eq_union]

/-- Reflecting the argument of a function about the midpoint of `uIcc a b` carries `uIcc b a`
to the set that `uIcc a b` was mapped into. -/
theorem MapsTo.comp_const_sub_uIcc {α β : Type*} [AddCommGroup α] [LinearOrder α]
    [IsOrderedAddMonoid α] {a b : α} {f : α → β} {s : Set β} (h : MapsTo f (uIcc a b) s) :
    MapsTo (fun t ↦ f (a + b - t)) (uIcc b a) s := fun t ht ↦ h (by
  have : t ∈ (fun x ↦ a + b - x) ⁻¹' uIcc a b := by
    simpa only [preimage_const_sub_uIcc, add_sub_cancel_left, add_sub_cancel_right] using ht
  exact this)

end Set
