/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Basic

/-!
# The row of an entry in a list of rows

The index of the first row containing an entry, `rows.findIdx? (fun row => a ∈ row)`, does not
change when every entry is relabelled by an injective map.
-/

public section

namespace List

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Relabelling the entries of a list of rows by an injective map does not move the row in which
an entry first appears. -/
theorem findIdx?_mem_map_map {f : α → β} (hf : Function.Injective f) (rows : List (List α))
    (a : α) :
    (rows.map (map f)).findIdx? (fun row => f a ∈ row) = rows.findIdx? (fun row => a ∈ row) := by
  rw [findIdx?_map]
  congr 1
  funext row
  simp [mem_map_of_injective hf]

end List
