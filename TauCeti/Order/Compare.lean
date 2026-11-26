/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Compare

/-!
# Comparisons determined by `≤`

Two pairs of points of linear orders compare in the same way under `cmp` as soon as `≤` agrees on
them in both directions: `TauCeti.cmp_eq_cmp_of_le_iff_le`. This is the converse of Mathlib's
`le_iff_le_of_cmp_eq_cmp`.
-/

public section

namespace TauCeti

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- Two pairs of points of linear orders compare in the same way when `≤` agrees in both
directions; the converse of `le_iff_le_of_cmp_eq_cmp`. -/
theorem cmp_eq_cmp_of_le_iff_le {x y : α} {x' y' : β} (h₁ : x ≤ y ↔ x' ≤ y')
    (h₂ : y ≤ x ↔ y' ≤ x') : cmp x y = cmp x' y' := by
  cases h : cmp x' y' <;> grind [cmp_eq_lt_iff, cmp_eq_eq_iff, cmp_eq_gt_iff]

end TauCeti
