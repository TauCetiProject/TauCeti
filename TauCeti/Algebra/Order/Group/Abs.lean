/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs

/-!
# Absolute differences of complementary quantities

The complement `d - a` of `a` with respect to `d` moves by exactly as much as `a` does. So
choosing, by a fixed condition, between a quantity and its complement does not change the
absolute difference of two such choices. For example, an edge density and a nonedge density
`1 - d(A, B)` change by the same amount when the pair of finsets changes.
-/

public section

namespace TauCeti

variable {α : Type*} [AddCommGroup α] [Lattice α]

/-- Choosing, by the same condition, between each of `a` and `b` and its complement with respect
to `d` does not change their absolute difference. -/
theorem abs_ite_sub_ite (c : Prop) [Decidable c] (a b d : α) :
    |(if c then a else d - a) - (if c then b else d - b)| = |a - b| := by
  split_ifs
  · rfl
  · rw [sub_sub_sub_cancel_left, abs_sub_comm]

end TauCeti
