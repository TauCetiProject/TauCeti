/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Vector.Defs

/-!
# Vectors whose underlying list is a cons

A vector of length `n + 1` has underlying list `a :: l` exactly when its head is `a` and the
underlying list of its tail is `l` (`List.Vector.toList_eq_cons_iff`).
-/

public section

namespace List.Vector

variable {α : Type*} {n : ℕ}

/-- The underlying list of a nonempty vector is `a :: l` iff its head is `a` and its tail has
underlying list `l`. -/
theorem toList_eq_cons_iff {v : List.Vector α (n + 1)} {a : α} {l : List α} :
    v.toList = a :: l ↔ v.head = a ∧ v.tail.toList = l := by
  conv_lhs => rw [← cons_head_tail v, toList_cons]
  exact List.cons_eq_cons

end List.Vector
