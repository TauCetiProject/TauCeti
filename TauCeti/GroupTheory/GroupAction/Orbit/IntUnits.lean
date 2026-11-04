/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Orbits of the sign action of `ℤˣ`

Every additive group `G` carries the action of the two-element group `ℤˣ = {1, -1}` through
integer multiples, so `-1` acts by negation. Its orbits are the sets `{x, -x}`, and the orbit
quotient `MulAction.orbitRel.Quotient ℤˣ G` is the quotient of `G` by negation: the target of
maps such as the `x`-coordinate on the points of an elliptic curve, which identify a point with
its negative and nothing else.

## Main results

* `MulAction.orbitRel_intUnits_iff`: two elements of an additive group lie in the same
  `ℤˣ`-orbit exactly when they are equal or negatives of each other.
-/

public section

namespace MulAction

/-- **The orbits of `ℤˣ` on an additive group are the sets `{x, -x}`.** -/
theorem orbitRel_intUnits_iff {G : Type*} [AddGroup G] {x y : G} :
    orbitRel ℤˣ G x y ↔ x = y ∨ x = -y := by
  rw [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨u, rfl⟩
    obtain rfl | rfl := Int.units_eq_one_or u <;> simp [Units.smul_def]
  · rintro (rfl | rfl)
    · exact ⟨1, one_smul _ _⟩
    · exact ⟨-1, by simp [Units.smul_def]⟩

end MulAction
