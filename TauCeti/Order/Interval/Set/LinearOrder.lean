/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Interval set identities in a linear order

This file collects set-difference identities for intervals in a linear order, extending
`Mathlib.Order.Interval.Set.LinearOrder`.

* `Set.Ioc_sdiff_Ioc_of_le`: subtracting `Ioc c a` from `Ioc c b` when `c ≤ a` leaves `Ioc a b`.
-/

public section

namespace Set

/-- Subtracting a sub-interval `Ioc c a` from `Ioc c b` when `c ≤ a` leaves `Ioc a b`. -/
theorem Ioc_sdiff_Ioc_of_le {α : Type*} [LinearOrder α] {c a b : α} (hca : c ≤ a) :
    Ioc c b \ Ioc c a = Ioc a b := by
  rw [← sdiff_inter_self_eq_sdiff, Ioc_inter_Ioc, max_self, min_comm, ← Ioc_inter_Iic,
    inter_comm, sdiff_inter_self_eq_sdiff, Ioc_sdiff_Iic, max_eq_right hca]

end Set
