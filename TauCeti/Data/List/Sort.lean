/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain

/-!
# Weakly increasing lists under appending an entry

A weakly increasing list stays weakly increasing after appending an entry exactly when its last
entry, if any, is at most the new one.
-/

public section

namespace List

variable {α : Type*} [Preorder α]

/-- A list followed by one more entry is weakly increasing exactly when the list is, and its last
entry, if any, is at most the new entry. -/
theorem sortedLE_append_singleton {l : List α} {a : α} :
    (l ++ [a]).SortedLE ↔ l.SortedLE ∧ ∀ b ∈ l.getLast?, b ≤ a := by
  rw [sortedLE_iff_isChain, sortedLE_iff_isChain, isChain_append]
  cases l.getLast? <;> simp

end List
