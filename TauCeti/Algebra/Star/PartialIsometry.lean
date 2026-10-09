/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary

/-!
# Partial isometries in star monoids

An element `u` of a star monoid is a *partial isometry* when `u * star u * u = u`. In the star
monoid of bounded operators on a Hilbert space these are exactly the operators that are isometric
on the orthogonal complement of their kernel; the polar decomposition `T = U |T|` writes every
bounded operator as such a partial isometry times a positive operator.

This file develops the purely algebraic part of the theory. The predicate is closed under `star`,
and for a partial isometry `u` both `star u * u` (the *initial projection*) and `u * star u` (the
*final projection*) are star projections. Unitary elements, and more generally isometries
(`star u * u = 1`) and co-isometries (`u * star u = 1`), are partial isometries, as are star
projections.

## Main definitions

* `IsPartialIsometry u`: the identity `u * star u * u = u`.

## Main statements

* `isPartialIsometry_star_iff`: `star u` is a partial isometry if and only if `u` is.
* `IsPartialIsometry.isStarProjection_star_mul_self`,
  `IsPartialIsometry.isStarProjection_mul_star_self`: the initial and final projections of a
  partial isometry are star projections.
* `IsPartialIsometry.of_star_mul_self_eq_one`, `IsPartialIsometry.of_mem_unitary`: isometries
  and unitary elements are partial isometries.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Graduate Texts in Mathematics 96,
  Springer (1990): partial isometries and the polar decomposition.
-/

public section

namespace TauCeti

variable {R : Type*}

/-- An element `u` of a star monoid is a *partial isometry* when `u * star u * u = u`.

For bounded operators on Hilbert spaces this says that `u` is isometric on the orthogonal
complement of its kernel. -/
@[mk_iff]
structure IsPartialIsometry [Mul R] [Star R] (u : R) : Prop where
  /-- The defining identity of a partial isometry. -/
  mul_star_mul_self : u * star u * u = u

namespace IsPartialIsometry

section Semigroup

variable [Semigroup R] [StarMul R] {u : R}

/-- The adjoint form of the defining identity: `star u * u * star u = star u`. -/
theorem star_mul_self_mul_star (hu : IsPartialIsometry u) : star u * u * star u = star u := by
  simpa [mul_assoc] using congr(star $(hu.mul_star_mul_self))

/-- The star of a partial isometry is a partial isometry. -/
protected theorem star (hu : IsPartialIsometry u) : IsPartialIsometry (star u) :=
  ⟨by rw [star_star]; exact hu.star_mul_self_mul_star⟩

/-- The initial projection `star u * u` of a partial isometry is idempotent. -/
theorem isIdempotentElem_star_mul_self (hu : IsPartialIsometry u) :
    IsIdempotentElem (star u * u) := by
  rw [IsIdempotentElem, mul_assoc, ← mul_assoc u, hu.mul_star_mul_self]

/-- The final projection `u * star u` of a partial isometry is idempotent. -/
theorem isIdempotentElem_mul_star_self (hu : IsPartialIsometry u) :
    IsIdempotentElem (u * star u) := by
  simpa using hu.star.isIdempotentElem_star_mul_self

/-- The initial projection `star u * u` of a partial isometry is a star projection. -/
theorem isStarProjection_star_mul_self (hu : IsPartialIsometry u) :
    IsStarProjection (star u * u) :=
  ⟨hu.isIdempotentElem_star_mul_self, .star_mul_self u⟩

/-- The final projection `u * star u` of a partial isometry is a star projection. -/
theorem isStarProjection_mul_star_self (hu : IsPartialIsometry u) :
    IsStarProjection (u * star u) :=
  ⟨hu.isIdempotentElem_mul_star_self, .mul_star_self u⟩

end Semigroup

section Monoid

variable [Monoid R] [StarMul R] {u : R}

/-- An isometry, that is an element with `star u * u = 1`, is a partial isometry. -/
theorem of_star_mul_self_eq_one (h : star u * u = 1) : IsPartialIsometry u :=
  ⟨by rw [mul_assoc, h, mul_one]⟩

/-- A co-isometry, that is an element with `u * star u = 1`, is a partial isometry. -/
theorem of_mul_star_self_eq_one (h : u * star u = 1) : IsPartialIsometry u :=
  ⟨by rw [h, one_mul]⟩

/-- A unitary element is a partial isometry. -/
theorem of_mem_unitary (hu : u ∈ unitary R) : IsPartialIsometry u :=
  of_star_mul_self_eq_one (Unitary.star_mul_self_of_mem hu)

variable (R) in
/-- The identity is a partial isometry. -/
@[simp]
protected theorem one : IsPartialIsometry (1 : R) :=
  of_star_mul_self_eq_one (by simp)

end Monoid

/-- The image of a partial isometry under a multiplicative map preserving `star` is a partial
isometry. -/
protected theorem map [Mul R] [Star R] {S F : Type*} [Mul S] [Star S] [FunLike F R S]
    [StarHomClass F R S] [MulHomClass F R S] {u : R} (hu : IsPartialIsometry u) (f : F) :
    IsPartialIsometry (f u) :=
  ⟨by rw [← map_star, ← map_mul, ← map_mul, hu.mul_star_mul_self]⟩

variable (R) in
/-- Zero is a partial isometry. -/
@[simp]
protected theorem zero [MulZeroClass R] [Star R] : IsPartialIsometry (0 : R) :=
  ⟨by rw [mul_zero]⟩

end IsPartialIsometry

/-- An element is a partial isometry if and only if its star is. -/
@[simp]
theorem isPartialIsometry_star_iff [Semigroup R] [StarMul R] {u : R} :
    IsPartialIsometry (star u) ↔ IsPartialIsometry u :=
  ⟨fun h ↦ by simpa using h.star, .star⟩

/-- A star projection is a partial isometry. -/
theorem _root_.IsStarProjection.isPartialIsometry [Mul R] [Star R] {p : R}
    (hp : IsStarProjection p) : IsPartialIsometry p :=
  ⟨by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq, hp.isIdempotentElem.eq]⟩

end TauCeti
