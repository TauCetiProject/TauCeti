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
-/

public section

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
