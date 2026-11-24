/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Set difference of intervals in a linear order

Removing a nested open interval `(c, d)` from `[a, b]` leaves the union `[a, c] ∪ [d, b]`
(`Set.Icc_sdiff_Ioo`).

## Main results

* `Set.Icc_sdiff_Ioo`: for `a ≤ c ≤ d ≤ b`, `Icc a b \ Ioo c d = Icc a c ∪ Icc d b`.
-/

public section

namespace Set

/-- Removing the open subinterval `(c, d)` from `[a, b]` when `a ≤ c ≤ d ≤ b` leaves
`[a, c] ∪ [d, b]`. -/
theorem Icc_sdiff_Ioo {α : Type*} [LinearOrder α] {a b c d : α}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    Icc a b \ Ioo c d = Icc a c ∪ Icc d b := by
  rw [sdiff_eq, ← Ioi_inter_Iio, compl_inter, compl_Ioi, compl_Iio,
    inter_comm, union_inter_distrib_right, ← Ici_inter_Iic]
  rw [← inter_assoc, inter_comm (Iic c), inter_assoc, Iic_inter_Iic, min_eq_left (hcd.trans hdb),
    Ici_inter_Iic]
  rw [← inter_assoc, Ici_inter_Ici, sup_eq_left.mpr (hac.trans hcd), Ici_inter_Iic]

end Set
