/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Classes of elements of a group with zero in the abelianization of its units

For a group with zero `G₀`, `TauCeti.abelianizationClass` sends `0` to `0` and a nonzero element to
the class of the corresponding unit in the abelianization of `G₀ˣ`, with a zero adjoined. It is a
monoid with zero homomorphism `G₀ →*₀ WithZero (Group.Abelianization G₀ˣ)`; for a division ring it
is the Dieudonné determinant of a `1 × 1` matrix.
-/

public section

noncomputable section

namespace TauCeti

variable (G₀ : Type*) [GroupWithZero G₀]

open Classical in
/-- The class of an element of a group with zero `G₀` in the abelianization of its unit group,
with a zero adjoined: `0` goes to `0`, and a unit `u` to its abelianization class. This is the
Dieudonné determinant of a `1 × 1` matrix. -/
def abelianizationClass : G₀ →*₀ WithZero (Group.Abelianization G₀ˣ) :=
  (WithZero.map' Group.Abelianization.of).comp (WithZero.withZeroUnitsEquiv (G := G₀)).symm

variable {G₀}

/-- `abelianizationClass` sends a unit to its abelianization class. -/
@[simp]
theorem abelianizationClass_units (u : G₀ˣ) :
    abelianizationClass G₀ u = Group.Abelianization.of u := by
  classical
  simp [abelianizationClass]

/-- `abelianizationClass` sends a nonzero element `a` to the abelianization class of the unit
`Units.mk0 a h`. -/
theorem abelianizationClass_of_ne_zero {a : G₀} (h : a ≠ 0) :
    abelianizationClass G₀ a = Group.Abelianization.of (Units.mk0 a h) :=
  abelianizationClass_units (Units.mk0 a h)

end TauCeti
