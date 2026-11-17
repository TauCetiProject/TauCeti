/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import TauCeti.Algebra.Star.SelfAdjoint
import Mathlib.Tactic.NoncommRing

/-!
# The range projection of an idempotent: algebraic identities

The self-adjoint element `1 - (e - star e)²` commutes with an idempotent `e`.
When it is invertible, it gives a projection with the same range as `e` by multiplying
its inverse by `e * star e`. The invertibility and continuity in C⋆-algebras are in
`TauCeti.Analysis.CStarAlgebra.Idempotent`.

The identities follow the idempotent-to-projection construction in Blackadar,
*K-Theory for Operator Algebras*, second edition, Proposition 4.6.2.
-/

public section

namespace TauCeti

variable {A : Type*} [Ring A] [StarRing A]

/-- The denominator in the formula for the range projection of an idempotent. -/
def idempotentProjectionDenom (e : A) : A := 1 - (e - star e) ^ 2

/-- The explicit formula for the denominator. -/
theorem idempotentProjectionDenom_def (e : A) :
    idempotentProjectionDenom e = 1 - (e - star e) ^ 2 := (rfl)

/-- Unital star ring homomorphisms preserve the denominator. -/
@[simp]
theorem map_idempotentProjectionDenom {B F : Type*} [Ring B] [StarRing B]
    [FunLike F A B] [RingHomClass F A B] [StarHomClass F A B] (f : F) (e : A) :
    f (idempotentProjectionDenom e) = idempotentProjectionDenom (f e) := by
  simp only [idempotentProjectionDenom, map_sub, map_one, map_pow, map_star]

/-- Taking the adjoint of the input leaves the denominator unchanged. -/
@[simp]
theorem idempotentProjectionDenom_star (e : A) :
    idempotentProjectionDenom (star e) = idempotentProjectionDenom e := by
  simp only [idempotentProjectionDenom, star_star, pow_two]
  noncomm_ring

/-- The denominator is one plus an element of the form `x * star x`. -/
theorem idempotentProjectionDenom_eq (e : A) :
    idempotentProjectionDenom e = 1 + (e - star e) * star (e - star e) := by
  simp only [idempotentProjectionDenom, star_sub, star_star, pow_two]
  noncomm_ring

/-- The denominator is self-adjoint, even without idempotence. -/
@[simp]
theorem isSelfAdjoint_idempotentProjectionDenom (e : A) :
    IsSelfAdjoint (idempotentProjectionDenom e) := by
  rw [idempotentProjectionDenom_eq]
  exact (IsSelfAdjoint.one A).add (IsSelfAdjoint.mul_star_self _)

/-- The adjoint of the denominator is itself. -/
@[simp]
theorem star_idempotentProjectionDenom (e : A) :
    star (idempotentProjectionDenom e) = idempotentProjectionDenom e :=
  (isSelfAdjoint_idempotentProjectionDenom e).star_eq

/-- The range projection formula for an idempotent. Here `Ring.inverse` is the inverse on units,
not a choice of a generalized inverse for a noninvertible element. -/
noncomputable def idempotentRangeProjection (e : A) : A :=
  e * star e * Ring.inverse (idempotentProjectionDenom e)

/-- The explicit formula for the range projection of an idempotent. -/
theorem idempotentRangeProjection_def (e : A) :
    idempotentRangeProjection e = e * star e * Ring.inverse (idempotentProjectionDenom e) :=
  (rfl)

/-- Unital star ring homomorphisms preserve the range projection formula when its denominator
is a unit. -/
theorem map_idempotentRangeProjection_of_isUnit {B F : Type*} [Ring B] [StarRing B]
    [FunLike F A B] [RingHomClass F A B] [StarHomClass F A B] (f : F) (e : A)
    (hu : IsUnit (idempotentProjectionDenom e)) :
    f (idempotentRangeProjection e) = idempotentRangeProjection (f e) := by
  simp only [idempotentRangeProjection, map_mul, map_star, hu.map_ringInverse f,
    map_idempotentProjectionDenom]

end TauCeti

/-- A self-adjoint element has denominator one. -/
@[simp]
theorem IsSelfAdjoint.idempotentProjectionDenom_eq {A : Type*} [Ring A] [StarRing A]
    {e : A} (he : IsSelfAdjoint e) : TauCeti.idempotentProjectionDenom e = 1 := by
  simp only [TauCeti.idempotentProjectionDenom_def, he.star_eq, sub_self, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]

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

private theorem commute_inverse_denom (he : IsIdempotentElem e)
    (hu : IsUnit (idempotentProjectionDenom e)) :
    Commute e (Ring.inverse (idempotentProjectionDenom e)) := by
  obtain ⟨u, hu⟩ := hu
  rw [← hu, Ring.inverse_unit]
  exact (hu.symm ▸ he.commute_idempotentProjectionDenom).units_inv_right

/-- The idempotent acts as the identity on the range of its range projection. -/
@[simp]
theorem mul_idempotentRangeProjection (he : IsIdempotentElem e) :
    e * idempotentRangeProjection e = idempotentRangeProjection e := by
  simp only [idempotentRangeProjection_def, ← mul_assoc, he.eq]

/-- With invertible denominator, the range projection acts as the identity on the idempotent. -/
theorem idempotentRangeProjection_mul_of_isUnit (he : IsIdempotentElem e)
    (hu : IsUnit (idempotentProjectionDenom e)) : idempotentRangeProjection e * e = e := by
  calc
    idempotentRangeProjection e * e =
        (e * star e * e) * Ring.inverse (idempotentProjectionDenom e) := by
      simp only [idempotentRangeProjection_def, mul_assoc, (he.commute_inverse_denom hu).eq]
    _ = e * (idempotentProjectionDenom e *
        Ring.inverse (idempotentProjectionDenom e)) := by
      rw [← he.mul_idempotentProjectionDenom, mul_assoc]
    _ = e := by rw [Ring.mul_inverse_cancel _ hu, mul_one]

/-- With invertible denominator, the range projection formula is a self-adjoint idempotent. -/
theorem isStarProjection_idempotentRangeProjection_of_isUnit (he : IsIdempotentElem e)
    (hu : IsUnit (idempotentProjectionDenom e)) :
    IsStarProjection (idempotentRangeProjection e) := by
  have hb := (isSelfAdjoint_idempotentProjectionDenom e).ringInverse
  have hbe : Commute (Ring.inverse (idempotentProjectionDenom e)) (star e) := by
    simpa only [Commute, SemiconjBy, star_mul, hb.star_eq] using
      congrArg star (he.commute_inverse_denom hu).eq
  have hp : IsSelfAdjoint (idempotentRangeProjection e) := by
    rw [idempotentRangeProjection_def]
    exact (IsSelfAdjoint.commute_iff (IsSelfAdjoint.mul_star_self e) hb).mp
      ((he.commute_inverse_denom hu).mul_left hbe.symm)
  refine ⟨?_, hp⟩
  calc
    idempotentRangeProjection e * idempotentRangeProjection e =
        idempotentRangeProjection e * (e * idempotentRangeProjection e) := by
      rw [he.mul_idempotentRangeProjection]
    _ = idempotentRangeProjection e := by
      rw [← mul_assoc, he.idempotentRangeProjection_mul_of_isUnit hu,
        he.mul_idempotentRangeProjection]

/-- The range projection is characterized by being a star projection with the two
multiplication identities. -/
theorem idempotentRangeProjection_eq_iff_of_isUnit (he : IsIdempotentElem e)
    (hu : IsUnit (idempotentProjectionDenom e)) {p : A} :
    idempotentRangeProjection e = p ↔ IsStarProjection p ∧ e * p = p ∧ p * e = e := by
  have hp := he.isStarProjection_idempotentRangeProjection_of_isUnit hu
  constructor
  · rintro rfl
    exact ⟨hp, he.mul_idempotentRangeProjection, he.idempotentRangeProjection_mul_of_isUnit hu⟩
  · intro h
    exact hp.isSelfAdjoint.eq_of_mul_eq_right h.1.isSelfAdjoint
      he.mul_idempotentRangeProjection (he.idempotentRangeProjection_mul_of_isUnit hu) h.2.1 h.2.2

/-- Every idempotent with invertible denominator has a unique star projection satisfying
the two multiplication identities. -/
theorem existsUnique_isStarProjection_mul_eq_right_of_isUnit (he : IsIdempotentElem e)
    (hu : IsUnit (idempotentProjectionDenom e)) :
    ∃! p : A, IsStarProjection p ∧ e * p = p ∧ p * e = e := by
  exact ⟨idempotentRangeProjection e, (he.idempotentRangeProjection_eq_iff_of_isUnit hu).mp rfl,
    fun _ hp ↦ ((he.idempotentRangeProjection_eq_iff_of_isUnit hu).mpr hp).symm⟩

end IsIdempotentElem

/-- Taking the range projection fixes star projections, in any star ring. -/
@[simp]
theorem IsStarProjection.idempotentRangeProjection_eq {A : Type*} [Ring A] [StarRing A]
    {p : A} (hp : IsStarProjection p) : TauCeti.idempotentRangeProjection p = p := by
  simp only [TauCeti.idempotentRangeProjection_def, hp.isSelfAdjoint.star_eq,
    hp.isSelfAdjoint.idempotentProjectionDenom_eq, Ring.inverse_one, mul_one,
    hp.isIdempotentElem.eq]
