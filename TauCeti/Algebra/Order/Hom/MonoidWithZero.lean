/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Hom.MonoidWithZero

/-!
# Ordered groups with a zero adjoined: `OrderMonoidIso.withZero` and `unitsWithZero`

Mathlib's `OrderMonoidIso.withZero` identifies order isomorphisms of two ordered groups with order
isomorphisms of those groups with a zero adjoined. This file records that its inverse is
compatible with composition, the analogue of `Equiv.optionCongr_trans`.

Mathlib's `OrderMonoidIso.unitsWithZero` identifies the units of `WithZero α` with `α`. This file
records that coercing its value back into `WithZero α` recovers the unit, so a statement phrased
through `OrderMonoidIso.unitsWithZero` can be rewritten to one about the plain unit coercion.

## Main results

* `OrderMonoidIso.withZero_symm_trans`: the inverse of `OrderMonoidIso.withZero` sends a composite
  to the composite of the images.
* `OrderMonoidIso.coe_unitsWithZero_apply`: `OrderMonoidIso.unitsWithZero u`, coerced into
  `WithZero α`, is the unit `u` itself.
-/

public section

namespace OrderMonoidIso

variable {G H K : Type*} [Group G] [PartialOrder G] [Group H] [PartialOrder H]
  [Group K] [PartialOrder K]

/-- The inverse of `OrderMonoidIso.withZero` is compatible with composition. -/
@[simp]
theorem withZero_symm_trans (A : WithZero G ≃*o WithZero H) (B : WithZero H ≃*o WithZero K) :
    (withZero.symm A).trans (withZero.symm B) = withZero.symm (A.trans B) := by
  ext x
  simp [withZero]

/-- Coercing the image of a unit `u` of `WithZero α` under `OrderMonoidIso.unitsWithZero` back
into `WithZero α` recovers `u`. -/
@[simp]
theorem coe_unitsWithZero_apply {α : Type*} [Group α] [Preorder α] (u : (WithZero α)ˣ) :
    ((unitsWithZero u : α) : WithZero α) = u :=
  WithZero.coe_unitsWithZeroEquiv_eq_units_val u

end OrderMonoidIso
