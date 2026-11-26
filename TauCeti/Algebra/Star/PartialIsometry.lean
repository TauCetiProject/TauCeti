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
* `TauCeti.IsPartialIsometry.star_mul_eq_zero`: partial isometries with orthogonal final
  projections satisfy `star u₁ * u₂ = 0`.
* `TauCeti.isPartialIsometry_iff_isStarProjection_star_mul_self`: in a ring with a proper star,
  conversely, `u` is a partial isometry once `star u * u` is a star projection;
  `isPartialIsometry_iff_isStarProjection_mul_star_self` is the version for `u * star u`.
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

section SemigroupWithZero

variable [SemigroupWithZero R] [StarMul R] {u₁ u₂ : R}

/-- Two partial isometries with orthogonal final projections (`(u₁ * star u₁) * (u₂ * star u₂) = 0`)
satisfy `star u₁ * u₂ = 0`. -/
theorem IsPartialIsometry.star_mul_eq_zero (hu₁ : IsPartialIsometry u₁)
    (hu₂ : IsPartialIsometry u₂) (h : (u₁ * star u₁) * (u₂ * star u₂) = 0) :
    star u₁ * u₂ = 0 := by
  calc star u₁ * u₂
    _ = star (u₁ * star u₁ * u₁) * (u₂ * star u₂ * u₂) := by
      rw [hu₁.mul_star_mul_self, hu₂.mul_star_mul_self]
    _ = star u₁ * ((u₁ * star u₁) * (u₂ * star u₂)) * u₂ := by
      simp only [star_mul, star_star, mul_assoc]
    _ = 0 := by rw [h, mul_zero, zero_mul]

end SemigroupWithZero

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

/-- In a ring with a proper star, `w` is a partial isometry if and only if `star w * w` is a
star projection. -/
theorem isPartialIsometry_iff_isStarProjection_star_mul_self [NonUnitalRing R] [StarRing R]
    [IsProperStar R] {w : R} : IsPartialIsometry w ↔ IsStarProjection (star w * w) := by
  refine ⟨IsPartialIsometry.isStarProjection_star_mul_self, fun hw ↦ ?_⟩
  have h : star w * w * star w * w = star w * w := by
    simpa only [← mul_assoc] using hw.isIdempotentElem.eq
  -- With `s = star w * w`, the product `star (w - w * s) * (w - w * s)` is
  -- `s - s * s - s * s + s * s * s`, which vanishes since `s * s = s`.
  have key : star (w - w * (star w * w)) * (w - w * (star w * w)) = 0 := by
    simp only [star_sub, star_mul, star_star, sub_mul, mul_sub, mul_assoc]
    simp only [← mul_assoc, h]
    abel
  rw [star_mul_self_eq_zero, sub_eq_zero] at key
  rw [isPartialIsometry_iff, mul_assoc, ← key]

/-- In a ring with a proper star, `w` is a partial isometry if and only if `w * star w` is a
star projection. -/
theorem isPartialIsometry_iff_isStarProjection_mul_star_self [NonUnitalRing R] [StarRing R]
    [IsProperStar R] {w : R} : IsPartialIsometry w ↔ IsStarProjection (w * star w) := by
  simpa only [isPartialIsometry_star_iff, star_star] using
    isPartialIsometry_iff_isStarProjection_star_mul_self (w := star w)

end TauCeti

/-- A star projection is a partial isometry. -/
theorem IsStarProjection.isPartialIsometry {R : Type*} [Mul R] [Star R] {p : R}
    (hp : IsStarProjection p) : TauCeti.IsPartialIsometry p := by
  rw [TauCeti.isPartialIsometry_iff, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq,
    hp.isIdempotentElem.eq]
