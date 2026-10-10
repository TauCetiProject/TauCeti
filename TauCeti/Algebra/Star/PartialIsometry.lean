/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary

/-!
# Partial isometries in a star monoid

An element `u` of a star monoid is a *partial isometry* when `u * star u * u = u`. For bounded
operators on a Hilbert space these are the operators that are isometric on the orthogonal
complement of their kernel; the algebraic form makes sense in any star monoid, and in particular
in every C⋆-algebra.

The defining equation says that `star u * u` acts as a unit on the right of `u`, so `star u * u`
and `u * star u` are star projections (the *initial* and *final* projections of `u`). Star
projections, isometries (`star u * u = 1`), coisometries (`u * star u = 1`) and unitaries are
partial isometries, and the class is closed under `star`.

## Main declarations

* `TauCeti.IsPartialIsometry u`: the predicate `u * star u * u = u`.
* `TauCeti.IsPartialIsometry.star`: the adjoint of a partial isometry is a partial isometry.
* `TauCeti.IsPartialIsometry.isStarProjection_star_mul_self`,
  `TauCeti.IsPartialIsometry.isStarProjection_mul_star_self`: the initial and final projections
  `star u * u` and `u * star u` are star projections.
* `IsStarProjection.isPartialIsometry`, `TauCeti.isPartialIsometry_of_star_mul_self_eq_one`,
  `TauCeti.isPartialIsometry_of_mem_unitary`: star projections, isometries and unitaries are
  partial isometries.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), the section on
  the polar decomposition.
-/

public section

namespace TauCeti

variable {R : Type*}

section Monoid

variable [Monoid R] [StarMul R] {u : R}

/-- An element `u` of a star monoid is a *partial isometry* when `u * star u * u = u`. -/
def IsPartialIsometry (u : R) : Prop :=
  u * star u * u = u

theorem isPartialIsometry_iff : IsPartialIsometry u ↔ u * star u * u = u :=
  Iff.rfl

/-- The defining equation of a partial isometry. -/
theorem IsPartialIsometry.mul_star_mul_self (hu : IsPartialIsometry u) : u * star u * u = u :=
  hu

/-- The adjoint of a partial isometry is a partial isometry. -/
protected theorem IsPartialIsometry.star (hu : IsPartialIsometry u) :
    IsPartialIsometry (star u) := by
  rw [isPartialIsometry_iff, star_star]
  simpa [mul_assoc] using congr_arg star hu

@[simp]
theorem isPartialIsometry_star_iff : IsPartialIsometry (star u) ↔ IsPartialIsometry u :=
  ⟨fun hu ↦ star_star u ▸ hu.star, IsPartialIsometry.star⟩

/-- The adjoint of a partial isometry `u` is also a right partial inverse:
`star u * u * star u = star u`. -/
theorem IsPartialIsometry.star_mul_self_mul_star (hu : IsPartialIsometry u) :
    star u * u * star u = star u := by
  simpa using hu.star.mul_star_mul_self

/-- The *initial projection* `star u * u` of a partial isometry `u` is a star projection. -/
theorem IsPartialIsometry.isStarProjection_star_mul_self (hu : IsPartialIsometry u) :
    IsStarProjection (star u * u) where
  isIdempotentElem := by
    rw [IsIdempotentElem, mul_assoc, ← mul_assoc u, hu.mul_star_mul_self]
  isSelfAdjoint := .star_mul_self u

/-- The *final projection* `u * star u` of a partial isometry `u` is a star projection. -/
theorem IsPartialIsometry.isStarProjection_mul_star_self (hu : IsPartialIsometry u) :
    IsStarProjection (u * star u) := by
  simpa using hu.star.isStarProjection_star_mul_self

@[simp]
theorem isPartialIsometry_one : IsPartialIsometry (1 : R) := by
  simp [isPartialIsometry_iff]

/-- An isometry, an element with `star u * u = 1`, is a partial isometry. -/
theorem isPartialIsometry_of_star_mul_self_eq_one (h : star u * u = 1) : IsPartialIsometry u := by
  rw [isPartialIsometry_iff, mul_assoc, h, mul_one]

/-- A coisometry, an element with `u * star u = 1`, is a partial isometry. -/
theorem isPartialIsometry_of_mul_star_self_eq_one (h : u * star u = 1) : IsPartialIsometry u := by
  rw [isPartialIsometry_iff, h, one_mul]

/-- A unitary element is a partial isometry. -/
theorem isPartialIsometry_of_mem_unitary (hu : u ∈ unitary R) : IsPartialIsometry u :=
  isPartialIsometry_of_star_mul_self_eq_one (Unitary.star_mul_self_of_mem hu)

end Monoid

@[simp]
theorem isPartialIsometry_zero [MonoidWithZero R] [StarMul R] : IsPartialIsometry (0 : R) := by
  simp [isPartialIsometry_iff]

end TauCeti

/-- A star projection is a partial isometry. -/
theorem IsStarProjection.isPartialIsometry {R : Type*} [Monoid R] [StarMul R] {p : R}
    (hp : IsStarProjection p) : TauCeti.IsPartialIsometry p := by
  rw [TauCeti.isPartialIsometry_iff, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq,
    hp.isIdempotentElem.eq]
