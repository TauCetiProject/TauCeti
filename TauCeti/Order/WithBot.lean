/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Claude
-/
module

public import Mathlib.Order.Directed
public import Mathlib.Order.WithBot

/-!
# Lower bounds by coercions in `WithTop`

In a downward directed order `α`, every element of `WithTop α` lies above the coercion of some
element of `α` below any given bound. This brings finitely many elements of `WithTop α` down to a
common coercion that is itself bounded, for instance a common exponent `m ≤ -1` below the orders
of several meromorphic functions.

## Main results

* `WithTop.exists_le_and_coe_le`: for `x : WithTop α` and `a : α` there is `b ≤ a` with `↑b ≤ x`.
-/

public section

namespace WithTop

variable {α : Type*} [Preorder α] [IsCodirectedOrder α]

/-- In a downward directed order, every `x : WithTop α` lies above the coercion of some element
below any given `a : α`. -/
theorem exists_le_and_coe_le (x : WithTop α) (a : α) : ∃ b : α, b ≤ a ∧ (b : WithTop α) ≤ x := by
  induction x with
  | top => exact ⟨a, le_rfl, le_top⟩
  | coe k =>
    obtain ⟨b, hbk, hba⟩ := exists_le_le k a
    exact ⟨b, hba, coe_le_coe.2 hbk⟩

end WithTop
