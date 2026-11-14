/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.NoncommRing

/-!
# The range projection of an idempotent: algebraic identities

The self-adjoint element `1 - (e - star e)²` commutes with an idempotent `e`.
When it is invertible, it gives a projection with the same range as `e` by multiplying
its inverse by `e * star e`. The analytic construction is in
`TauCeti.Analysis.CStarAlgebra.Idempotent`.

The identities follow the idempotent-to-projection construction in Blackadar,
*K-Theory for Operator Algebras*, second edition, Proposition 4.6.2.
-/

public section

namespace TauCeti

variable {A : Type*} [Ring A] [StarRing A]

/-- The denominator in the formula for the range projection of an idempotent. -/
def idempotentProjectionDenom (e : A) : A := 1 - (e - star e) ^ 2

/-- The denominator is one plus an element of the form `x * star x`. -/
theorem idempotentProjectionDenom_eq (e : A) :
    idempotentProjectionDenom e = 1 + (e - star e) * star (e - star e) := by
  simp only [idempotentProjectionDenom, star_sub, star_star, pow_two]
  noncomm_ring

/-- The denominator is self-adjoint, even without idempotence. -/
theorem isSelfAdjoint_idempotentProjectionDenom (e : A) :
    IsSelfAdjoint (idempotentProjectionDenom e) := by
  rw [idempotentProjectionDenom_eq]
  exact (IsSelfAdjoint.one A).add (IsSelfAdjoint.mul_star_self _)

end TauCeti

namespace IsIdempotentElem

open TauCeti

variable {A : Type*} [Ring A] [StarRing A] {e : A}

/-- Multiplying the denominator on the left by its idempotent. -/
theorem mul_idempotentProjectionDenom (he : IsIdempotentElem e) :
    e * idempotentProjectionDenom e = e * star e * e := by
  have hes : star e * star e = star e := by simpa only [star_mul] using congrArg star he.eq
  simp only [idempotentProjectionDenom, pow_two, mul_sub, sub_mul, mul_one,
    ← mul_assoc, he.eq, hes]
  noncomm_ring

/-- Multiplying the denominator on the right by its idempotent. -/
theorem idempotentProjectionDenom_mul (he : IsIdempotentElem e) :
    idempotentProjectionDenom e * e = e * star e * e := by
  have hes : star e * star e = star e := by simpa only [star_mul] using congrArg star he.eq
  dsimp [idempotentProjectionDenom]
  noncomm_ring [he.eq, hes]

/-- An idempotent commutes with the denominator of its range projection. -/
theorem commute_idempotentProjectionDenom (he : IsIdempotentElem e) :
    Commute e (idempotentProjectionDenom e) := by
  exact he.mul_idempotentProjectionDenom.trans he.idempotentProjectionDenom_mul.symm

end IsIdempotentElem
