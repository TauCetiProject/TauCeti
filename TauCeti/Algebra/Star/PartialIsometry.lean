/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Projection
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
  `TauCeti.isPartialIsometry_iff_isStarProjection_star_mul_self`: in a ring with a proper star,
  conversely, `u` is a partial isometry once `star u * u` is idempotent (equivalently, a star
  projection); `isPartialIsometry_iff_isStarProjection_mul_star_self` is the version for
  `u * star u`.
* `TauCeti.IsPartialIsometry.of_star_mul_self_eq`: in a ring with a proper star, `u` is a partial
  isometry once `star u * u` equals a star projection.
* `TauCeti.IsPartialIsometry.mul_eq_self_of_mul_star_self_le`: a partial isometry `u` is fixed by
  left multiplication by any star projection `p ≥ u * star u`;
  `mul_eq_self_of_star_mul_self_le` is the version for right multiplication and `star u * u`.
* `TauCeti.IsPartialIsometry.mul_mul_eq_self_of_le`: a partial isometry whose initial and final
  projections lie below a star projection `q` lies in the corner `q R q`.
* `TauCeti.IsPartialIsometry.star_mul_eq_zero_iff`: two partial isometries `v`, `w` have
  orthogonal final projections exactly when `star v * w = 0`.
* `TauCeti.IsPartialIsometry.of_star_mul_self_eq_one`, `TauCeti.IsPartialIsometry.of_mem_unitary`,
  `IsStarProjection.isPartialIsometry`: isometries, unitaries and star projections are partial
  isometries.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), the treatment of
  partial isometries and the polar decomposition.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), Proposition 4.6.2.
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

/-- The defining equation of a partial isometry, reassociated: `u * (star u * u) = u`. -/
theorem mul_star_mul_self_assoc (hu : IsPartialIsometry u) : u * (star u * u) = u := by
  rw [← mul_assoc, hu.mul_star_mul_self]

/-- If `p` fixes the final projection of a partial isometry `u` from the left, then it fixes `u`:
`p * (u * star u) = u * star u` implies `p * u = u`. -/
theorem mul_eq_self_of_mul_mul_star_self_eq (hu : IsPartialIsometry u) {p : R}
    (hp : p * (u * star u) = u * star u) : p * u = u := by
  rw [← hu.mul_star_mul_self, ← mul_assoc, hp]

/-- If `p` fixes the initial projection of a partial isometry `u` from the right, then it fixes
`u`: `star u * u * p = star u * u` implies `u * p = u`. -/
theorem mul_eq_self_of_star_mul_self_mul_eq (hu : IsPartialIsometry u) {p : R}
    (hp : star u * u * p = star u * u) : u * p = u := by
  rw [← hu.mul_star_mul_self_assoc, mul_assoc, hp]

end IsPartialIsometry

/-- An element is a partial isometry iff its adjoint is. -/
@[simp]
theorem isPartialIsometry_star_iff : IsPartialIsometry (star u) ↔ IsPartialIsometry u :=
  ⟨fun h => by simpa only [star_star] using h.star, IsPartialIsometry.star⟩

end Semigroup

/-- Two partial isometries `v`, `w` have orthogonal final projections,
`(v * star v) * (w * star w) = 0`, if and only if `star v * w = 0`. -/
theorem IsPartialIsometry.star_mul_eq_zero_iff [SemigroupWithZero R] [StarMul R] {v w : R}
    (hv : IsPartialIsometry v) (hw : IsPartialIsometry w) :
    star v * w = 0 ↔ v * star v * (w * star w) = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · calc v * star v * (w * star w) = v * (star v * w) * star w := by simp only [mul_assoc]
      _ = 0 := by rw [h, mul_zero, zero_mul]
  · have hv' : star v * v * star v = star v := by
      simpa only [star_star] using hv.star.mul_star_mul_self
    calc star v * w = star v * v * star v * (w * star w * w) := by
          rw [hv', hw.mul_star_mul_self]
      _ = star v * (v * star v * (w * star w)) * w := by simp only [mul_assoc]
      _ = 0 := by rw [h, mul_zero, zero_mul]

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

section ProperStar

variable [NonUnitalRing R] [StarRing R] [IsProperStar R] {u : R}

/-- In a ring with proper star, `u` is a partial isometry as soon as `star u * u` is idempotent. -/
theorem IsPartialIsometry.of_isIdempotentElem_star_mul_self
    (h : IsIdempotentElem (star u * u)) : IsPartialIsometry u := by
  have hux : star u * (u * star u * u - u) = 0 := by
    rw [mul_sub, ← mul_assoc, ← mul_assoc, mul_assoc (star u * u), h.eq, sub_self]
  have hxx : star (u * star u * u - u) * (u * star u * u - u) = 0 := by
    rw [star_sub, star_mul, star_mul, star_star, ← mul_assoc (star u) u (star u), sub_mul,
      mul_assoc (star u * u) (star u), hux, mul_zero, sub_zero]
  exact sub_eq_zero.mp (star_mul_self_eq_zero.mp hxx)

/-- In a ring with proper star, `u` is a partial isometry iff `star u * u` is idempotent. -/
theorem isPartialIsometry_iff_isIdempotentElem_star_mul_self :
    IsPartialIsometry u ↔ IsIdempotentElem (star u * u) :=
  ⟨fun h ↦ h.isStarProjection_star_mul_self.isIdempotentElem, .of_isIdempotentElem_star_mul_self⟩

end ProperStar

/-- In a ring with a proper star, `w` is a partial isometry if and only if `star w * w` is a
star projection. -/
theorem isPartialIsometry_iff_isStarProjection_star_mul_self [NonUnitalRing R] [StarRing R]
    [IsProperStar R] {w : R} : IsPartialIsometry w ↔ IsStarProjection (star w * w) :=
  ⟨IsPartialIsometry.isStarProjection_star_mul_self,
    fun hw ↦ .of_isIdempotentElem_star_mul_self hw.isIdempotentElem⟩

/-- In a ring with a proper star, `w` is a partial isometry if and only if `w * star w` is a
star projection. -/
theorem isPartialIsometry_iff_isStarProjection_mul_star_self [NonUnitalRing R] [StarRing R]
    [IsProperStar R] {w : R} : IsPartialIsometry w ↔ IsStarProjection (w * star w) := by
  simpa only [isPartialIsometry_star_iff, star_star] using
    isPartialIsometry_iff_isStarProjection_star_mul_self (w := star w)

/-- In a ring with a proper star, if `star u * u = p` for a star projection `p`, then `u` is a
partial isometry. -/
theorem IsPartialIsometry.of_star_mul_self_eq [NonUnitalRing R] [StarRing R] [IsProperStar R]
    {u p : R} (hp : IsStarProjection p) (h : star u * u = p) : IsPartialIsometry u :=
  isPartialIsometry_iff_isStarProjection_star_mul_self.mpr (h ▸ hp)

/-- In a star-ordered ring with a proper star, a partial isometry `u` is fixed by left
multiplication by any star projection `p` above its final projection: `u * star u ≤ p` implies
`p * u = u`. -/
theorem IsPartialIsometry.mul_eq_self_of_mul_star_self_le [NonUnitalRing R] [StarRing R]
    [PartialOrder R] [StarOrderedRing R] [IsProperStar R] {u p : R} (hu : IsPartialIsometry u)
    (hp : IsStarProjection p) (h : u * star u ≤ p) : p * u = u :=
  hu.mul_eq_self_of_mul_mul_star_self_eq
    ((hu.isStarProjection_mul_star_self.le_iff_mul_eq_right hp).mp h)

/-- In a star-ordered ring with a proper star, a partial isometry `u` is fixed by right
multiplication by any star projection `p` above its initial projection: `star u * u ≤ p` implies
`u * p = u`. -/
theorem IsPartialIsometry.mul_eq_self_of_star_mul_self_le [NonUnitalRing R] [StarRing R]
    [PartialOrder R] [StarOrderedRing R] [IsProperStar R] {u p : R} (hu : IsPartialIsometry u)
    (hp : IsStarProjection p) (h : star u * u ≤ p) : u * p = u :=
  hu.mul_eq_self_of_star_mul_self_mul_eq
    ((hu.isStarProjection_star_mul_self.le_iff_mul_eq_left hp).mp h)

/-- In a star-ordered ring with a proper star, a partial isometry `u` whose initial and final
projections lie below a star projection `q` lies in the corner `q R q`: `q * u * q = u`. -/
theorem IsPartialIsometry.mul_mul_eq_self_of_le [NonUnitalRing R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] [IsProperStar R] {u q : R} (hu : IsPartialIsometry u)
    (hq : IsStarProjection q) (h₁ : star u * u ≤ q) (h₂ : u * star u ≤ q) : q * u * q = u := by
  rw [hu.mul_eq_self_of_mul_star_self_le hq h₂, hu.mul_eq_self_of_star_mul_self_le hq h₁]

end TauCeti

/-- A star projection is a partial isometry. -/
theorem IsStarProjection.isPartialIsometry {R : Type*} [Mul R] [Star R] {p : R}
    (hp : IsStarProjection p) : TauCeti.IsPartialIsometry p := by
  rw [TauCeti.isPartialIsometry_iff, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq,
    hp.isIdempotentElem.eq]
