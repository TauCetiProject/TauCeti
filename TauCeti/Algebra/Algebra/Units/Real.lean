/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.Subring.Units

/-!
# Positive real scalar units of a real algebra

The image of the positive real units under the algebra map is a subgroup of the units of any
real algebra. Its members are precisely the units represented by positive real scalars.

## Main definitions and results

* `Units.posRealSubgroup`: positive real scalar units of a real algebra.
* `Units.mem_posRealSubgroup_iff_exists_algebraMap_eq`: membership represented by a positive
  real scalar.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition, Birkhäuser (1996), §VI.4,
  Example, pp.311–312, for positive real diagonal factors.
* Mathlib, `Units.posSubgroup` and `Units.map`.
-/

public noncomputable section

namespace Units

variable (A : Type*) [Semiring A] [Algebra ℝ A]

/-- The subgroup of units of a real algebra that are positive real scalars. -/
def posRealSubgroup : Subgroup Aˣ :=
  (Units.posSubgroup ℝ).map (Units.map (algebraMap ℝ A).toMonoidHom)

variable {A}

/-- A unit is a positive real scalar exactly when it is represented by a positive real number. -/
theorem mem_posRealSubgroup_iff_exists_algebraMap_eq {z : Aˣ} :
    z ∈ posRealSubgroup A ↔ ∃ r : ℝ, 0 < r ∧ algebraMap ℝ A r = (z : A) := by
  rw [posRealSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, (Units.mem_posSubgroup _).mp hu, rfl⟩
  · rintro ⟨r, hr, hz⟩
    exact ⟨Units.mk0 r (ne_of_gt hr), (Units.mem_posSubgroup _).mpr hr, Units.ext hz⟩

end Units
