/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Projection to a closed interval away from its endpoints

The projection `Set.projIcc a b h` of a linear order onto `[a, b]` sends every point outside
`[a, b]` to an endpoint. So a point whose projection lies in the open interval `(a, b)` is its own
projection (`Set.eq_of_coe_projIcc_eq`).
-/

public section

namespace Set

variable {α : Type*} [LinearOrder α] {a b s t : α} {h : a ≤ b}

/-- A point whose projection to `[a, b]` is a point `s` of the open interval `(a, b)` is `s`. -/
theorem eq_of_coe_projIcc_eq (hst : (projIcc a b h t : α) = s) (hs : s ∈ Ioo a b) : t = s := by
  have ht : t ∈ Icc a b := by
    refine ⟨not_lt.1 fun ht ↦ hs.1.ne ?_, not_lt.1 fun ht ↦ hs.2.ne' ?_⟩
    · rwa [projIcc_of_le_left _ ht.le] at hst
    · rwa [projIcc_of_right_le _ ht.le] at hst
  rwa [projIcc_of_mem _ ht] at hst

end Set
