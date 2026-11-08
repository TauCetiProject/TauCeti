/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary

/-!
# Partial isometries in a star semigroup

An element `u` of a star semigroup is a *partial isometry* when `u * star u * u = u`. For a bounded
operator on a Hilbert space this is the usual notion: `star u * u` is then the orthogonal
projection onto the initial space of `u`, and `u` is isometric there and zero on its orthogonal
complement. The Hilbert-space characterizations are in
`TauCeti/Analysis/InnerProductSpace/PartialIsometry.lean`; this file records the purely algebraic
part of the theory.

## Main definitions

* `TauCeti.IsPartialIsometry u`: the element `u` satisfies `u * star u * u = u`. The predicate
  only needs a multiplication and a star operation; the structural results below hold in any
  star semigroup, so in particular in non-unital star rings such as non-unital C⋆-algebras.

## Main statements

* `TauCeti.IsPartialIsometry.star`: the adjoint of a partial isometry is a partial isometry.
* `TauCeti.IsPartialIsometry.isStarProjection_star_mul_self`: the initial projection
  `star u * u` of a partial isometry is a star projection; `isStarProjection_mul_star_self` is the
  corresponding statement for the final projection `u * star u`.
* `TauCeti.IsPartialIsometry.of_star_mul_self_eq_one`, `TauCeti.IsPartialIsometry.of_mem_unitary`,
  `IsStarProjection.isPartialIsometry`: isometries, unitaries and star projections are partial
  isometries.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), the treatment of
  partial isometries and the polar decomposition.
-/

public section

namespace TauCeti

variable {R : Type*}

section Mul

variable [Mul R] [Star R] {u : R}

/-- An element `u` of a type with a multiplication and a star operation is a
**partial isometry** when `u * star u * u = u`. -/
def IsPartialIsometry (u : R) : Prop :=
  u * star u * u = u

/-- Unfold the definition of a partial isometry. -/
theorem isPartialIsometry_iff : IsPartialIsometry u ↔ u * star u * u = u :=
  Iff.rfl

/-- The defining equation `u * star u * u = u` of a partial isometry. -/
theorem IsPartialIsometry.mul_star_mul_self (hu : IsPartialIsometry u) : u * star u * u = u :=
  hu

end Mul

section Semigroup

variable [Semigroup R] [StarMul R] {u : R}

namespace IsPartialIsometry

/-- The adjoint of a partial isometry is a partial isometry. -/
protected theorem star (hu : IsPartialIsometry u) : IsPartialIsometry (star u) := by
  rw [isPartialIsometry_iff, star_star]
  simpa only [star_mul, star_star, mul_assoc] using congrArg star hu.mul_star_mul_self

/-- The initial projection `star u * u` of a partial isometry is a star projection. -/
theorem isStarProjection_star_mul_self (hu : IsPartialIsometry u) :
    IsStarProjection (star u * u) where
  isIdempotentElem := by
    rw [IsIdempotentElem, mul_assoc, ← mul_assoc u, hu.mul_star_mul_self]
  isSelfAdjoint := IsSelfAdjoint.star_mul_self u

/-- The final projection `u * star u` of a partial isometry is a star projection. -/
theorem isStarProjection_mul_star_self (hu : IsPartialIsometry u) :
    IsStarProjection (u * star u) := by
  simpa only [star_star] using hu.star.isStarProjection_star_mul_self

end IsPartialIsometry

/-- An element is a partial isometry iff its adjoint is. -/
@[simp]
theorem isPartialIsometry_star_iff : IsPartialIsometry (star u) ↔ IsPartialIsometry u :=
  ⟨fun h => by simpa only [star_star] using h.star, IsPartialIsometry.star⟩

end Semigroup

namespace IsPartialIsometry

/-- An isometry, that is an element with `star u * u = 1`, is a partial isometry. -/
theorem of_star_mul_self_eq_one [Monoid R] [Star R] {u : R} (h : star u * u = 1) :
    IsPartialIsometry u := by
  rw [isPartialIsometry_iff, mul_assoc, h, mul_one]

/-- A coisometry, that is an element with `u * star u = 1`, is a partial isometry. -/
theorem of_mul_star_self_eq_one [MulOneClass R] [Star R] {u : R} (h : u * star u = 1) :
    IsPartialIsometry u := by
  rw [isPartialIsometry_iff, h, one_mul]

/-- A unitary element is a partial isometry. -/
theorem of_mem_unitary [Monoid R] [StarMul R] {u : R} (hu : u ∈ unitary R) :
    IsPartialIsometry u :=
  of_star_mul_self_eq_one (Unitary.star_mul_self_of_mem hu)

end IsPartialIsometry

/-- The identity is a partial isometry. -/
protected theorem IsPartialIsometry.one [MulOneClass R] [StarMul R] :
    IsPartialIsometry (1 : R) := by
  rw [isPartialIsometry_iff, star_one, mul_one, mul_one]

/-- Zero is a partial isometry. -/
protected theorem IsPartialIsometry.zero [MulZeroClass R] [Star R] :
    IsPartialIsometry (0 : R) := by
  rw [isPartialIsometry_iff, mul_zero]

end TauCeti

/-- A star projection is a partial isometry. -/
theorem IsStarProjection.isPartialIsometry {R : Type*} [Mul R] [Star R] {p : R}
    (hp : IsStarProjection p) : TauCeti.IsPartialIsometry p := by
  rw [TauCeti.isPartialIsometry_iff, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq,
    hp.isIdempotentElem.eq]
