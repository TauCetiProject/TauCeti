/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TakeDrop

/-!
# List `take`/`drop` windowing and prefix-mapping length

This file provides reusable `List.take`/`List.drop` helpers:

* `List.drop_take_append_drop_of_le`: for `m ≤ n`, the suffix `l.drop m` splits at `n` into the
  window `(l.take n).drop m` and the suffix `l.drop n`.
* `List.length_map_take_append_drop`: mapping over `l.take d` while preserving `l.drop d` keeps
  the length `l.length`.
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

/-- Mapping over the prefix `l.take d` while keeping the remaining suffix `l.drop d` preserves
the length of `l`. -/
theorem length_map_take_append_drop (f : α → α) (d : ℕ) (l : List α) :
    ((l.take d).map f ++ l.drop d).length = l.length := by
  simp
  omega

end List
