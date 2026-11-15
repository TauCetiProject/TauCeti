/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# One-sided characterizations of order-connected sets

In a preordered type, a subset `s` containing a lower bound `a` of all its elements (`a ∈ s` and
`s ⊆ Set.Ici a`) is order-connected (`Set.OrdConnected`) if and only if it is downward-closed above
`a`: whenever `a ≤ x ≤ y` and `y ∈ s`, we have `x ∈ s`. Dually, a subset containing an upper bound
`a` of all its elements is order-connected if and only if `y ≤ x ≤ a` and `y ∈ s` imply `x ∈ s`.

## Main results

* `Set.ordConnected_iff_of_subset_Ici` and `Set.ordConnected_iff_of_subset_Iic`: one-sided
  characterizations of `Set.OrdConnected` for subsets containing an extremum.
-/

public section

namespace Set

variable {α : Type*} [Preorder α]

/-- A subset containing a lower bound `a` of all its elements is order-connected if and only if
`a ≤ x ≤ y` and `y ∈ s` imply `x ∈ s`. -/
@[to_dual /-- A subset containing an upper bound `a` of all its elements is order-connected if and
only if `y ≤ x ≤ a` and `y ∈ s` imply `x ∈ s`. -/]
theorem ordConnected_iff_of_subset_Ici {a : α} {s : Set α} (ha : a ∈ s) (hs : s ⊆ Ici a) :
    s.OrdConnected ↔ ∀ ⦃x y : α⦄, a ≤ x → x ≤ y → y ∈ s → x ∈ s :=
  ⟨fun h _ _ hax hxy hy ↦ h.out' ha hy ⟨hax, hxy⟩,
    fun h ↦ ⟨fun _ hx _ hy _ hz ↦ h ((hs hx).trans hz.1) hz.2 hy⟩⟩

end Set
