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
change when every entry is relabelled by an injective map. Similarly, the first occurrence index
of a member of a list is preserved by a map that is injective on the list.
-/

public section

namespace List

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A map that is injective on a list preserves the first occurrence index of each member. -/
theorem idxOf_map_eq_of_injectiveOn (w : List α) (f : α → β)
    (hf : ∀ ⦃x y⦄, x ∈ w → y ∈ w → f x = f y → x = y) {x : α} (hx : x ∈ w) :
    (w.map f).idxOf (f x) = w.idxOf x := by
  induction w with
  | nil => simp at hx
  | cons a w ih =>
    by_cases hxa : x = a
    · subst x
      simp
    · have hfa : f x ≠ f a := fun h => hxa (hf hx (by simp) h)
      have hx' : x ∈ w := (List.mem_cons.mp hx).resolve_left hxa
      have hf' : ∀ ⦃x y⦄, x ∈ w → y ∈ w → f x = f y → x = y := by
        intro x y hx' hy' hxy
        exact hf (by simp [hx']) (by simp [hy']) hxy
      rw [List.map_cons, List.idxOf_cons_ne _ (Ne.symm hxa),
        List.idxOf_cons_ne _ (Ne.symm hfa)]
      exact congrArg Nat.succ (ih hf' hx')

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
