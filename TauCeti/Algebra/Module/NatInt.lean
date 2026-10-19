/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Ring.Units

/-!
# Integer unit signs acting on modules

The sign action of an integer unit agrees with the action of its image in the scalar ring.
This lets integer signs in the scalar ring, such as powers of `-1`, combine with integer unit
actions.
-/

public section

namespace TauCeti

/-- Acting by the image of an integer unit in the scalar ring and then by a second integer unit
is the action of their product as integer units. -/
theorem intCast_smul_units_smul {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (u' u : ℤˣ) (v : V) : ((u' : ℤ) : R) • u • v = (u' * u) • v := by
  rw [mul_smul, Units.smul_def u', ← Int.cast_smul_eq_zsmul R]

end TauCeti
