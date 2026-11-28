/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.Basic

/-!
# Intersections of sets with nested rays

Intersecting `I ∩ Ioi c` with `Ioi x` when `c ≤ x` reduces to `I ∩ Ioi x`, and dually for `Iio`.

## Main results

* `Set.inter_Ioi_inter_Ioi_of_le`: `(I ∩ Ioi c) ∩ Ioi x = I ∩ Ioi x` for `c ≤ x`.
* `Set.inter_Iio_inter_Iio_of_le`: `(I ∩ Iio d) ∩ Iio x = I ∩ Iio x` for `x ≤ d`.
-/

public section

namespace Set

/-- Intersecting `I ∩ Ioi c` with `Ioi x` when `c ≤ x` simplifies to `I ∩ Ioi x`. -/
theorem inter_Ioi_inter_Ioi_of_le {α : Type*} [Preorder α] {I : Set α} {c x : α}
    (hcx : c ≤ x) : (I ∩ Ioi c) ∩ Ioi x = I ∩ Ioi x := by
  rw [inter_assoc, inter_eq_right.2 (Ioi_subset_Ioi hcx)]

/-- Intersecting `I ∩ Iio d` with `Iio x` when `x ≤ d` simplifies to `I ∩ Iio x`. -/
theorem inter_Iio_inter_Iio_of_le {α : Type*} [Preorder α] {I : Set α} {x d : α}
    (hxd : x ≤ d) : (I ∩ Iio d) ∩ Iio x = I ∩ Iio x := by
  rw [inter_assoc, inter_eq_right.2 (Iio_subset_Iio hxd)]

end Set
