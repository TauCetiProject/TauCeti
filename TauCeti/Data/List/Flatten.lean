/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction

/-!
# Endpoints of flattened lists of nonempty lists

The first and last entries of the flattening `L.flatten` of a list of nonempty lists are the first
entry of its first list and the last entry of its last list.
-/

public section

namespace List

variable {α : Type*}

/-- The first element of a flattened list of nonempty lists is the first element of its first
list. -/
theorem head?_flatten_of_ne_nil {L : List (List α)} (hne : ∀ l ∈ L, l ≠ []) :
    L.flatten.head? = L.head?.bind List.head? := by
  cases L with
  | nil => rfl
  | cons l L =>
    rw [List.flatten_cons, List.head?_append_of_ne_nil _ (hne l List.mem_cons_self)]
    rfl

/-- The last element of a flattened list of nonempty lists is the last element of its last list. -/
theorem getLast?_flatten_of_ne_nil {L : List (List α)} (hne : ∀ l ∈ L, l ≠ []) :
    L.flatten.getLast? = L.getLast?.bind List.getLast? := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L l _ =>
    rw [List.flatten_append, List.flatten_singleton,
      List.getLast?_append_of_ne_nil _ (hne l (by simp)), List.getLast?_concat]
    rfl

end List
