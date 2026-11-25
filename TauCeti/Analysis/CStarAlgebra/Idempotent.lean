/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import TauCeti.Algebra.Star.Projection.Idempotent
public import TauCeti.Algebra.Ring.Idempotent.Units
public import TauCeti.Algebra.Star.SelfAdjoint

/-!
# Idempotents and their range projections

Every idempotent `e` in a unital C⋆-algebra has a unique star projection `p` satisfying
`e * p = p` and `p * e = e`. Thus `e` and `p` generate the same principal right ideal.
The projection is `e * star e * (1 - (e - star e)²)⁻¹`, and depends continuously and naturally
on `e`. The unit `TauCeti.idempotentConjUnit e p` conjugates `e` to `p`; its value is
`1 + e - p`, with inverse `1 - e + p`, so every idempotent is similar to its range projection
(`IsIdempotentElem.isConj_idempotentRangeProjection`). This is how idempotents are replaced by
projections before using constructions, such as unitary splittings, that make sense only for
self-adjoint idempotents.

Applied to matrix algebras this converts idempotent representatives of projective modules
into projection representatives, without changing their range modules.

## References

* Blackadar, *K-Theory for Operator Algebras*, second edition, Proposition 4.6.2.
* I. Kaplansky, *Rings of Operators*, W. A. Benjamin (1968).
-/

public section

open scoped CStarAlgebra

namespace TauCeti

variable {A : Type*} [CStarAlgebra A]

/-- The denominator in the range projection formula is invertible. -/
@[simp]
theorem isUnit_idempotentProjectionDenom (e : A) : IsUnit (idempotentProjectionDenom e) := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  apply CStarAlgebra.isUnit_of_le (1 : A)
  rw [idempotentProjectionDenom_eq]
  exact le_add_of_nonneg_right (mul_star_self_nonneg _)

/-- Unital star ring homomorphisms out of a C⋆-algebra preserve its range projection formula. -/
@[simp]
theorem map_idempotentRangeProjection {B F : Type*} [Ring B] [StarRing B]
    [FunLike F A B] [RingHomClass F A B] [StarHomClass F A B] (f : F) (e : A) :
    f (idempotentRangeProjection e) = idempotentRangeProjection (f e) :=
  map_idempotentRangeProjection_of_isUnit f e (isUnit_idempotentProjectionDenom e)

/-- The range projection formula is norm-continuous, even away from idempotents. -/
@[fun_prop]
theorem continuous_idempotentRangeProjection : Continuous (idempotentRangeProjection : A → A) := by
  have hd : Continuous (idempotentProjectionDenom : A → A) := by
    -- Eta-expand to rewrite with the public formula without exposing the definition's body.
    change Continuous (fun e : A ↦ idempotentProjectionDenom e)
    simp_rw [idempotentProjectionDenom_def]
    fun_prop
  have hi : Continuous (fun e : A ↦ Ring.inverse (idempotentProjectionDenom e)) := by
    refine continuous_iff_continuousAt.mpr fun e ↦ ?_
    obtain ⟨u, hu⟩ := isUnit_idempotentProjectionDenom e
    exact (hu ▸ NormedRing.inverse_continuousAt u).comp hd.continuousAt
  -- Eta-expand again so the public formula rewrites under the continuity predicate.
  change Continuous (fun e : A ↦ idempotentRangeProjection e)
  simp_rw [idempotentRangeProjection_def]
  exact (continuous_id.mul continuous_star).mul hi

end TauCeti

namespace IsIdempotentElem

open TauCeti

variable {A : Type*} [CStarAlgebra A] {e : A}

/-- The range projection acts as the identity on the range of the idempotent. -/
@[simp]
theorem idempotentRangeProjection_mul (he : IsIdempotentElem e) :
    idempotentRangeProjection e * e = e :=
  he.idempotentRangeProjection_mul_of_isUnit (isUnit_idempotentProjectionDenom e)

/-- The range projection formula is a self-adjoint idempotent. -/
@[simp]
theorem isStarProjection_idempotentRangeProjection (he : IsIdempotentElem e) :
    IsStarProjection (idempotentRangeProjection e) :=
  he.isStarProjection_idempotentRangeProjection_of_isUnit (isUnit_idempotentProjectionDenom e)

/-- The adjoint of the range projection is itself. -/
@[simp]
theorem star_idempotentRangeProjection (he : IsIdempotentElem e) :
    Star.star (idempotentRangeProjection e) = idempotentRangeProjection e :=
  he.isStarProjection_idempotentRangeProjection.isSelfAdjoint.star_eq

/-- The range projection is characterized by being a star projection with the two
multiplication identities. -/
theorem idempotentRangeProjection_eq_iff (he : IsIdempotentElem e) {p : A} :
    idempotentRangeProjection e = p ↔ IsStarProjection p ∧ e * p = p ∧ p * e = e :=
  he.idempotentRangeProjection_eq_iff_of_isUnit (isUnit_idempotentProjectionDenom e)

/-- Every idempotent has a unique star projection generating the same principal right ideal. -/
theorem existsUnique_isStarProjection_mul_eq_right (he : IsIdempotentElem e) :
    ∃! p : A, IsStarProjection p ∧ e * p = p ∧ p * e = e :=
  he.existsUnique_isStarProjection_mul_eq_right_of_isUnit (isUnit_idempotentProjectionDenom e)

/-- The range projection of an idempotent `e` is the only self-adjoint element `q` with
`e * q = q` and `q * e = e`; idempotence of `q` is not assumed. -/
theorem eq_idempotentRangeProjection_iff (he : IsIdempotentElem e) {q : A}
    (hq : IsSelfAdjoint q) :
    q = idempotentRangeProjection e ↔ e * q = q ∧ q * e = e := by
  refine ⟨fun h ↦ h ▸ ⟨he.mul_idempotentRangeProjection, he.idempotentRangeProjection_mul⟩,
    fun ⟨heq, hqe⟩ ↦ ?_⟩
  exact hq.eq_of_mul_eq_right he.isStarProjection_idempotentRangeProjection.isSelfAdjoint
    heq hqe he.mul_idempotentRangeProjection he.idempotentRangeProjection_mul

/-- Every idempotent of a unital C⋆-algebra is similar to its range projection. -/
theorem isConj_idempotentRangeProjection (he : IsIdempotentElem e) :
    IsConj (idempotentRangeProjection e) e :=
  isConj_of_mul_eq he.mul_idempotentRangeProjection he.idempotentRangeProjection_mul

end IsIdempotentElem
