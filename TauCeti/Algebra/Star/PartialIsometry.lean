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
* `TauCeti.IsPartialIsometry.of_isIdempotentElem_star_mul_self`,
  `TauCeti.isPartialIsometry_iff_isStarProjection_star_mul_self` (and `mul_star_self` twins):
  proper-star characterizations via idempotency / projection of `star u * u` and `u * star u`.
* `TauCeti.IsPartialIsometry.of_star_mul_self_eq_one`, `TauCeti.IsPartialIsometry.of_mem_unitary`,
  `IsStarProjection.isPartialIsometry`,
  `IsStarProjection.star_mul_self_mul_of_star_mul_self_mul_eq`,
  `TauCeti.IsPartialIsometry.mul_of_star_mul_self_mul_eq_of_isStarProjection` (with isometry and
  `unitary` corollaries): isometries, unitaries, projections, and `u * p` are partial isometries.

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

section ProperStar
variable [NonUnitalRing R] [StarRing R] [IsProperStar R] {u : R}
/-- In a star ring with proper star, `u` is a partial isometry if `star u * u` is idempotent. -/
theorem IsPartialIsometry.of_isIdempotentElem_star_mul_self (h : IsIdempotentElem (star u * u)) :
    IsPartialIsometry u := by
  rw [isPartialIsometry_iff, ← sub_eq_zero, ← star_mul_self_eq_zero]
  have h1 : star (u * star u * u) = star u * u * star u := by
    rw [star_mul, star_mul, star_star, mul_assoc]
  have h4 : star u * (u * star u * u) = star u * u := by simpa only [mul_assoc] using h.eq
  have h2 : (star u * u * star u) * (u * star u * u) = star u * u := by rw [mul_assoc, h4, h.eq]
  have h3 : (star u * u * star u) * u = star u * u := by rw [mul_assoc, h.eq]
  rw [star_sub, h1, sub_mul, mul_sub, mul_sub, h2, h3, h4, sub_self]
/-- In a star ring with proper star, `u` is a partial isometry if `u * star u` is idempotent. -/
theorem IsPartialIsometry.of_isIdempotentElem_mul_star_self (h : IsIdempotentElem (u * star u)) :
    IsPartialIsometry u := by
  simpa only [star_star] using
    (of_isIdempotentElem_star_mul_self (u := star u) (by rwa [star_star])).star
/-- In a star ring with proper star, `u` is a partial isometry iff `star u * u` is idempotent. -/
theorem isPartialIsometry_iff_isIdempotentElem_star_mul_self :
    IsPartialIsometry u ↔ IsIdempotentElem (star u * u) :=
  ⟨fun h => h.isStarProjection_star_mul_self.isIdempotentElem, .of_isIdempotentElem_star_mul_self⟩
/-- In a star ring with proper star, `u` is a partial isometry iff `u * star u` is idempotent. -/
theorem isPartialIsometry_iff_isIdempotentElem_mul_star_self :
    IsPartialIsometry u ↔ IsIdempotentElem (u * star u) :=
  ⟨fun h => h.isStarProjection_mul_star_self.isIdempotentElem, .of_isIdempotentElem_mul_star_self⟩
/-- In a proper-star ring, `u` is a partial isometry iff `star u * u` is a star projection. -/
theorem isPartialIsometry_iff_isStarProjection_star_mul_self :
    IsPartialIsometry u ↔ IsStarProjection (star u * u) :=
  ⟨IsPartialIsometry.isStarProjection_star_mul_self,
    fun h => .of_isIdempotentElem_star_mul_self h.isIdempotentElem⟩
/-- In a proper-star ring, `u` is a partial isometry iff `u * star u` is a star projection. -/
theorem isPartialIsometry_iff_isStarProjection_mul_star_self :
    IsPartialIsometry u ↔ IsStarProjection (u * star u) := by
  rw [← isPartialIsometry_star_iff, isPartialIsometry_iff_isStarProjection_star_mul_self, star_star]
end ProperStar

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

/-- For a star projection `p`, `(a * p) * star (a * p) = a * p * star a`. -/
theorem IsStarProjection.mul_star_self_mul {R : Type*} [Semigroup R] [StarMul R] {p : R}
    (hp : IsStarProjection p) (a : R) : (a * p) * star (a * p) = a * p * star a := by
  rw [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc p, hp.isIdempotentElem.eq,
    mul_assoc]
section
variable {R : Type*} [Semigroup R] [StarMul R] {p u : R}
/-- If `star u * u` acts as the identity on the range of a star projection `p`, then
`star (u * p) * (u * p) = p`. -/
theorem IsStarProjection.star_mul_self_mul_of_star_mul_self_mul_eq (hp : IsStarProjection p)
    (hu : star u * u * p = p) : star (u * p) * (u * p) = p := by
  rw [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc (star u), hu,
    hp.isIdempotentElem.eq]
/-- If `star u * u` acts as the identity on the range of a star projection `p`, then `u * p` is a
partial isometry. -/
theorem TauCeti.IsPartialIsometry.mul_of_star_mul_self_mul_eq_of_isStarProjection
    (hu : star u * u * p = p) (hp : IsStarProjection p) : TauCeti.IsPartialIsometry (u * p) := by
  rw [TauCeti.isPartialIsometry_iff, mul_assoc,
    hp.star_mul_self_mul_of_star_mul_self_mul_eq hu, mul_assoc, hp.isIdempotentElem.eq]
end
section
variable {R : Type*} [Monoid R] [StarMul R] {p u : R}
/-- For an isometry `u` (`star u * u = 1`) and a star projection `p`, `(u * p)⋆ * (u * p) = p`. -/
theorem IsStarProjection.star_mul_self_mul_of_star_mul_self_eq_one (hp : IsStarProjection p)
    (hu : star u * u = 1) : star (u * p) * (u * p) = p :=
  hp.star_mul_self_mul_of_star_mul_self_mul_eq (by rw [hu, one_mul])
/-- For a unitary `u` and a star projection `p`, the initial projection of `u * p` is `p`. -/
theorem IsStarProjection.star_mul_self_unitary_mul (hp : IsStarProjection p) (u : unitary R) :
    star ((u : R) * p) * ((u : R) * p) = p :=
  hp.star_mul_self_mul_of_star_mul_self_eq_one (Unitary.coe_star_mul_self u)
/-- Left-multiplying a star projection `p` by an isometry `u` yields a partial isometry. -/
theorem TauCeti.IsPartialIsometry.mul_of_star_mul_self_eq_one_of_isStarProjection
    (hu : star u * u = 1) (hp : IsStarProjection p) : TauCeti.IsPartialIsometry (u * p) :=
  mul_of_star_mul_self_mul_eq_of_isStarProjection (by rw [hu, one_mul]) hp
/-- Left-multiplying a star projection `p` by a unitary `u` gives a partial isometry. -/
theorem Unitary.isPartialIsometry_mul_of_isStarProjection (u : unitary R)
    (hp : IsStarProjection p) : TauCeti.IsPartialIsometry ((u : R) * p) :=
  TauCeti.IsPartialIsometry.mul_of_star_mul_self_eq_one_of_isStarProjection
    (Unitary.coe_star_mul_self u) hp
end
