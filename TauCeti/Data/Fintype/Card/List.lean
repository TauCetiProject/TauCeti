/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Card

/-!
# Length of a duplicate-free list covering a finite type

A duplicate-free list containing every element of a finite type has length equal to the
cardinality of that type (`List.Nodup.length_eq_card`), matching Mathlib's
`List.Nodup.length_le_card`.
-/

public section

namespace List.Nodup

/-- A duplicate-free list containing every element of a finite type has length equal to
`Fintype.card α`. -/
theorem length_eq_card {α : Type*} [Fintype α] {l : List α} (hl : l.Nodup) (hall : ∀ a, a ∈ l) :
    l.length = Fintype.card α := by
  classical
  rw [← List.toFinset_card_of_nodup hl,
    Finset.eq_univ_iff_forall.mpr fun a => List.mem_toFinset.mpr (hall a), Finset.card_univ]

end List.Nodup
