/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.SuccPred.Basic

/-!
# Basic facts about successor orders

In a successor order an element is strictly below its successor exactly when it is not maximal
(`Order.lt_succ_iff_not_isMax`). This file records the consequence that an element below some
other element is strictly below its successor (`TauCeti.Order.lt_succ_self_of_lt`). For instance,
in a discretely ordered abelian group the least positive element `succ 0` is positive as soon as
some element is.
-/

public section

namespace TauCeti.Order

open _root_.Order

/-- An element below some other element is not maximal, so it is below its successor. -/
theorem lt_succ_self_of_lt {α : Type*} [Preorder α] [SuccOrder α] {a b : α} (h : a < b) :
    a < succ a :=
  lt_succ_of_not_isMax (not_isMax_of_lt h)

end TauCeti.Order
