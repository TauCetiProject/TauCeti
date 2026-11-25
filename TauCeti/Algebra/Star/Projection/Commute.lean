/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection

/-!
# Commuting star projections

Two star projections `p` and `q` in a ring with a proper star (for instance a C⋆-algebra) commute
as soon as `p * q * p = q * p * q`: the commutator `x = p * q - q * p` then satisfies
`star x * x = 0`. This is the degenerate case `τ = 0` of the relation
`p * q * p - τ • p = q * p * q - τ • q` between projections.

In a semigroup, an element `s` commuting with an idempotent `p` gives the element `s * p` of the
corner `p * R * p`. If moreover `s` is self-adjoint and `p` is a star projection, then
`star (s * p) * (s * p) = s * s * p`. In a C⋆-algebra this is how the square root of a positive
element of the corner of `p` produces a factorization `a = star g * g` with `g` in the corner.
-/

public section

section Semigroup

variable {R : Type*} [Semigroup R] {p s : R}

/-- If `s` commutes with an idempotent `p`, then `s * p` lies in the corner `p * R * p`. -/
theorem IsIdempotentElem.mul_mul_mul_of_commute (hp : IsIdempotentElem p) (hsp : Commute s p) :
    p * (s * p) * p = s * p := by
  simp only [mul_assoc, hsp.symm.left_comm, hp.eq]

/-- If a self-adjoint `s` commutes with a star projection `p`, then
`star (s * p) * (s * p) = s * s * p`. -/
theorem IsStarProjection.star_mul_self_eq_of_commute [StarMul R] (hp : IsStarProjection p)
    (hs : IsSelfAdjoint s) (hsp : Commute s p) : star (s * p) * (s * p) = s * s * p := by
  simp only [star_mul, hp.isSelfAdjoint.star_eq, hs.star_eq, mul_assoc, hsp.symm.left_comm,
    hp.isIdempotentElem.eq]

end Semigroup

namespace IsStarProjection

variable {R : Type*} [NonUnitalRing R] [StarRing R] [IsProperStar R] {p q : R}

/-- Two star projections `p` and `q` in a ring with a proper star satisfying
`p * q * p = q * p * q` commute. -/
theorem commute_of_mul_mul_eq (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : p * q * p = q * p * q) : Commute p q := by
  have hpqpq : p * q * p * q = q * p * q := by rw [h, mul_assoc (q * p), hq.isIdempotentElem.eq]
  have hqpqp : q * p * q * p = p * q * p := by rw [← h, mul_assoc (p * q), hp.isIdempotentElem.eq]
  have hqppq : q * p * p * q = q * p * q := by rw [mul_assoc q p p, hp.isIdempotentElem.eq]
  have hpqqp : p * q * q * p = p * q * p := by rw [mul_assoc p q q, hq.isIdempotentElem.eq]
  have hx : star (p * q - q * p) * (p * q - q * p) = 0 := by
    simp only [star_sub, star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, sub_mul,
      mul_sub, ← mul_assoc, hqppq, hqpqp, hpqpq, hpqqp, sub_self]
  exact sub_eq_zero.mp (star_mul_self_eq_zero.mp hx)

end IsStarProjection
