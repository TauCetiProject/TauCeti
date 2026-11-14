/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import TauCeti.Algebra.Star.Projection.Idempotent
public import TauCeti.Algebra.Star.SelfAdjoint

/-!
# Idempotents and their range projections

Every idempotent `e` in a unital C⋆-algebra has a unique star projection `p` satisfying
`e * p = p` and `p * e = e`. Thus `e` and `p` generate the same principal right ideal.
The projection is `e * star e * (1 - (e - star e)²)⁻¹`. Moreover, conjugation by the unit
`1 + e - p`, with inverse `1 - e + p`, takes `e` to `p`.

Applied to matrix algebras this converts idempotent representatives of projective modules
into projection representatives, without changing their range modules.

## References

* Blackadar, *K-Theory for Operator Algebras*, second edition, Proposition 4.6.2.
-/

public section

open scoped CStarAlgebra

namespace TauCeti

variable {A : Type*} [CStarAlgebra A]

/-- The range projection formula for an idempotent. Here `Ring.inverse` is the inverse on units,
not a choice of a generalized inverse for a noninvertible element. -/
noncomputable def idempotentRangeProjection (e : A) : A :=
  e * star e * Ring.inverse (idempotentProjectionDenom e)

/-- The explicit formula for the range projection of an idempotent. -/
theorem idempotentRangeProjection_def (e : A) :
    idempotentRangeProjection e = e * star e * Ring.inverse (idempotentProjectionDenom e) :=
  (rfl)

/-- The denominator in the range projection formula is invertible. -/
theorem isUnit_idempotentProjectionDenom (e : A) : IsUnit (idempotentProjectionDenom e) := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  apply CStarAlgebra.isUnit_of_le (1 : A)
  rw [idempotentProjectionDenom_eq]
  exact le_add_of_nonneg_right (mul_star_self_nonneg _)

end TauCeti

namespace IsIdempotentElem

open TauCeti

variable {A : Type*} [CStarAlgebra A] {e : A}

private theorem commute_inverse_denom (he : IsIdempotentElem e) :
    Commute e (Ring.inverse (idempotentProjectionDenom e)) := by
  obtain ⟨u, hu⟩ := isUnit_idempotentProjectionDenom e
  rw [← hu, Ring.inverse_unit]
  exact (hu.symm ▸ he.commute_idempotentProjectionDenom).units_inv_right

/-- The idempotent acts as the identity on the range of its range projection. -/
@[simp]
theorem mul_idempotentRangeProjection (he : IsIdempotentElem e) :
    e * idempotentRangeProjection e = idempotentRangeProjection e := by
  simp only [idempotentRangeProjection, ← mul_assoc, he.eq]

/-- The range projection acts as the identity on the range of the idempotent. -/
@[simp]
theorem idempotentRangeProjection_mul (he : IsIdempotentElem e) :
    idempotentRangeProjection e * e = e := by
  calc
    idempotentRangeProjection e * e =
        (e * Star.star e * e) * Ring.inverse (idempotentProjectionDenom e) := by
      simp only [idempotentRangeProjection, mul_assoc, he.commute_inverse_denom.eq]
    _ = e * (idempotentProjectionDenom e *
        Ring.inverse (idempotentProjectionDenom e)) := by
      rw [← he.mul_idempotentProjectionDenom, mul_assoc]
    _ = e := by rw [Ring.mul_inverse_cancel _ (isUnit_idempotentProjectionDenom e), mul_one]

/-- The range projection formula is a self-adjoint idempotent. -/
theorem isStarProjection_idempotentRangeProjection (he : IsIdempotentElem e) :
    IsStarProjection (idempotentRangeProjection e) := by
  have hb := (isSelfAdjoint_idempotentProjectionDenom e).ringInverse
  have hbe : Commute (Ring.inverse (idempotentProjectionDenom e)) (Star.star e) := by
    simpa only [Commute, SemiconjBy, star_mul, hb.star_eq] using
      congrArg Star.star he.commute_inverse_denom.eq
  have hp : IsSelfAdjoint (idempotentRangeProjection e) := by
    exact (IsSelfAdjoint.commute_iff (IsSelfAdjoint.mul_star_self e) hb).mp
      (he.commute_inverse_denom.mul_left hbe.symm)
  refine ⟨?_, hp⟩
  calc
    idempotentRangeProjection e * idempotentRangeProjection e =
        idempotentRangeProjection e * (e * idempotentRangeProjection e) := by
      rw [he.mul_idempotentRangeProjection]
    _ = idempotentRangeProjection e := by
      rw [← mul_assoc, he.idempotentRangeProjection_mul, he.mul_idempotentRangeProjection]

/-- Every idempotent has a unique star projection generating the same principal right ideal. -/
theorem existsUnique_isStarProjection_same_range (he : IsIdempotentElem e) :
    ∃! p : A, IsStarProjection p ∧ e * p = p ∧ p * e = e := by
  refine ⟨idempotentRangeProjection e, ⟨he.isStarProjection_idempotentRangeProjection,
    he.mul_idempotentRangeProjection, he.idempotentRangeProjection_mul⟩, ?_⟩
  intro p hp
  exact hp.1.isSelfAdjoint.eq_of_same_range
    he.isStarProjection_idempotentRangeProjection.isSelfAdjoint
    hp.2.1 hp.2.2 he.mul_idempotentRangeProjection he.idempotentRangeProjection_mul

/-- An idempotent is similar to its range projection by a unit with value `1 + e - p` and
inverse `1 - e + p`. In particular this similarity does not change its projective module. -/
theorem exists_unit_conj_eq_idempotentRangeProjection (he : IsIdempotentElem e) :
    ∃ u : Aˣ, (u : A) = 1 + e - idempotentRangeProjection e ∧
      (↑u⁻¹ : A) = 1 - e + idempotentRangeProjection e ∧
      (u : A) * e * ↑u⁻¹ = idempotentRangeProjection e := by
  have hep := he.mul_idempotentRangeProjection
  have hpe := he.idempotentRangeProjection_mul
  have hpp := he.isStarProjection_idempotentRangeProjection.isIdempotentElem.eq
  let u : Aˣ :=
    { val := 1 + e - idempotentRangeProjection e
      inv := 1 - e + idempotentRangeProjection e
      val_inv := by noncomm_ring [he.eq, hep, hpe, hpp]
      inv_val := by noncomm_ring [he.eq, hep, hpe, hpp] }
  refine ⟨u, rfl, rfl, ?_⟩
  -- The two coercions here are the value and inverse fields of the explicitly constructed unit.
  dsimp [u]
  noncomm_ring [he.eq, hep, hpe, hpp]

end IsIdempotentElem

namespace IsStarProjection

open TauCeti

variable {A : Type*} [CStarAlgebra A] {p : A}

/-- Taking the range projection fixes star projections. -/
@[simp]
theorem idempotentRangeProjection_eq (hp : IsStarProjection p) :
    idempotentRangeProjection p = p := by
  have hq := hp.isIdempotentElem.isStarProjection_idempotentRangeProjection
  exact hq.isSelfAdjoint.eq_of_same_range hp.isSelfAdjoint
    hp.isIdempotentElem.mul_idempotentRangeProjection
    hp.isIdempotentElem.idempotentRangeProjection_mul
    hp.isIdempotentElem.eq hp.isIdempotentElem.eq

end IsStarProjection
