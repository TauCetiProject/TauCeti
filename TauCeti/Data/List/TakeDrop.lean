/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TakeDrop

/-!
# Splitting a suffix of a list at a later position

For `m ≤ n`, the suffix `l.drop m` splits at the position `n` of `l` into the window
`(l.take n).drop m` of the entries `m, …, n - 1` and the suffix `l.drop n`. This is
`List.drop_take_append_drop` with the window written as a suffix of a prefix.
-/

public section

namespace List

variable {α : Type*}

/-- For `m ≤ n`, the suffix `l.drop m` is the window `(l.take n).drop m` followed by the suffix
`l.drop n`. -/
theorem drop_take_append_drop_of_le (l : List α) {m n : ℕ} (h : m ≤ n) :
    (l.take n).drop m ++ l.drop n = l.drop m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [drop_take]

end List
