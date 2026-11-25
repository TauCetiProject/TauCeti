/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Basic

/-!
# Combining consecutive entries of a list closed up by an end point

For a list `l`, an entry `b` and a function `f`, the list `List.zipWith f (l.tail ++ [b]) l`
combines each entry of `l` with the entry that follows it, and the last entry of `l` with `b`.
With `f` the subtraction this is the list of the gaps between consecutive entries of `l`,
closed up by the end point `b`.

`List.apply_getLast_mem_zipWith_tail_append_singleton` says that the combination
`f b (l.getLast hl)` of the last entry of a nonempty list `l` with `b` is an entry of this list.
-/

public section

namespace List

variable {α β : Type*}

/-- In the list `zipWith f (l.tail ++ [b]) l`, which combines each entry of `l` with the next one
and the last entry of `l` with `b`, the combination `f b (l.getLast hl)` does occur. -/
theorem apply_getLast_mem_zipWith_tail_append_singleton (f : α → α → β) (b : α) {l : List α}
    (hl : l ≠ []) : f b (l.getLast hl) ∈ zipWith f (l.tail ++ [b]) l := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons c l =>
      have h := ih (cons_ne_nil c l)
      simp only [tail_cons, cons_append, zipWith_cons_cons, mem_cons, getLast_cons_cons] at h ⊢
      exact Or.inr h

end List
