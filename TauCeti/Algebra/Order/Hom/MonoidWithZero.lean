/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Hom.MonoidWithZero

/-!
# Composition and `OrderMonoidIso.withZero`

Mathlib's `OrderMonoidIso.withZero` identifies order isomorphisms of two ordered groups with order
isomorphisms of those groups with a zero adjoined. This file records that its inverse is
compatible with composition, the analogue of `Equiv.optionCongr_trans`.

## Main results

* `OrderMonoidIso.withZero_symm_trans`: the inverse of `OrderMonoidIso.withZero` sends a composite
  to the composite of the images.
-/

public section

namespace OrderMonoidIso

variable {G H K : Type*} [Group G] [PartialOrder G] [Group H] [PartialOrder H]
  [Group K] [PartialOrder K]

/-- The inverse of `OrderMonoidIso.withZero` is compatible with composition. -/
theorem withZero_symm_trans (A : WithZero G ≃*o WithZero H) (B : WithZero H ≃*o WithZero K) :
    (withZero.symm A).trans (withZero.symm B) = withZero.symm (A.trans B) := by
  ext x
  simp [withZero]

end OrderMonoidIso
