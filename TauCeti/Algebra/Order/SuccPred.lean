/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.SuccPred

/-!
# Discretely ordered additive structures

In an order with `succ x = x + 1` (Mathlib's `SuccAddOrder`), the element `1` is positive as soon
as some element is. This covers a discretely ordered abelian group without assuming it nontrivial:
the trivial group has `1 = 0` and no positive element.
-/

public section

namespace Order

variable {α : Type*} [AddZeroClass α] [Preorder α] [One α] [SuccAddOrder α] {a : α}

/-- If `succ x = x + 1` and some element is positive, then `0 < 1`. -/
theorem zero_lt_one_of_pos (h : 0 < a) : (0 : α) < 1 := by
  simpa [succ_eq_add_one] using lt_succ_of_not_isMax (not_isMax_of_lt h)

end Order
