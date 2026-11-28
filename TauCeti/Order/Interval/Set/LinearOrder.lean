/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.Basic

/-!
# Interval set identities in a linear order

This file collects set-difference identities for intervals in a linear order, extending
`Mathlib.Order.Interval.Set.LinearOrder`.

* `Set.Ioc_sdiff_Ioc_left` and `Set.Ioc_sdiff_Ioc_of_le`: subtracting `Ioc c a` from `Ioc c b`
  leaves `Ioc (max c a) b`, and `Ioc a b` when `c ≤ a`.
-/

public section

namespace Set

/-- Subtracting an initial half-open interval `Ioc c a` from `Ioc c b` shifts the left endpoint
to `max c a`. -/
theorem Ioc_sdiff_Ioc_left {α : Type*} [LinearOrder α] (c a b : α) :
    Ioc c b \ Ioc c a = Ioc (max c a) b := by
  ext x
  simp only [mem_sdiff, mem_Ioc, not_and, not_le]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨max_lt h1.1 (h2 h1.1), h1.2⟩,
    fun ⟨h1, h2⟩ ↦ ⟨⟨(le_max_left c a).trans_lt h1, h2⟩,
      fun _ ↦ (le_max_right c a).trans_lt h1⟩⟩

/-- Subtracting a sub-interval `Ioc c a` from `Ioc c b` when `c ≤ a` leaves `Ioc a b`. -/
theorem Ioc_sdiff_Ioc_of_le {α : Type*} [LinearOrder α] {c a b : α} (hca : c ≤ a) :
    Ioc c b \ Ioc c a = Ioc a b := by
  rw [Ioc_sdiff_Ioc_left, max_eq_right hca]

end Set
