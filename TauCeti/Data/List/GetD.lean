/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.GetD

/-!
# Entries of a row read with a default

A list of lists, read with `List.getD` and the empty list as default, has every entry of each of
its rows among the entries of its flattening.
-/

public section

namespace List

variable {α : Type*}

/-- An entry of row `i` of a list of rows is an entry of the list. Rows beyond the last one are
read as empty. -/
theorem mem_flatten_of_mem_getD {rows : List (List α)} {i : ℕ} {x : α}
    (hx : x ∈ rows.getD i []) : x ∈ rows.flatten := by
  rw [getD_eq_getElem?_getD] at hx
  cases hi : rows[i]? with
  | none => simp [hi] at hx
  | some row => exact mem_flatten.mpr ⟨row, mem_of_getElem? hi, by simpa [hi] using hx⟩

end List
