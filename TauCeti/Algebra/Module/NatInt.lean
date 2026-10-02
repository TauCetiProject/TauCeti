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
This lets powers of `-1` in the scalar ring combine with integer unit actions.
-/

public section

namespace TauCeti

/-- Acting by `(-1) ^ m` in the scalar ring and then by an integer unit is the action of
their product as integer units. -/
theorem neg_one_pow_smul_units_smul {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (m : ℕ) (u : ℤˣ) (v : V) : (-1 : R) ^ m • u • v = ((-1) ^ m * u) • v := by
  rw [mul_smul, Units.smul_def ((-1) ^ m), ← Int.cast_smul_eq_zsmul R]
  simp

end TauCeti
