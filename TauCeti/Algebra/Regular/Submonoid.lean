/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Algebra.GroupWithZero.Regular

/-!
# The submonoid of regular elements

The multiplicatively cancellable elements of a monoid form a submonoid. In a monoid with
zero-cancellative multiplication, these are exactly the nonzero elements.
-/

public section

namespace TauCeti

/-- The multiplicatively regular elements of a monoid. -/
def regularElements (R : Type*) [Monoid R] : Submonoid R where
  carrier := {r | IsRegular r}
  one_mem' := isRegular_one
  mul_mem' ha hb := ha.mul hb

variable {R : Type*} [Monoid R]

/-- Membership in the submonoid of regular elements is regularity. -/
@[simp]
theorem mem_regularElements {r : R} : r ∈ regularElements R ↔ IsRegular r := (Iff.rfl)

/-- In a monoid with zero-cancellative multiplication, regular elements are exactly the nonzero
ones. -/
theorem mem_regularElements_iff_ne_zero {R : Type*} [MonoidWithZero R] [IsCancelMulZero R]
    [Nontrivial R] {r : R} : r ∈ regularElements R ↔ r ≠ 0 := isRegular_iff_ne_zero

end TauCeti
