/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import TauCeti.Algebra.Ring.Idempotent.Basic

/-!
# The range projection of an idempotent in a C*-algebra

An idempotent `e` of a unital C*-algebra need not be self-adjoint, but there is exactly one star
projection `p` with the same range, in the sense that `e * p = p` and `p * e = e`. Kaplansky's
formula gives it explicitly: with `x = e - star e`, the element `z = 1 + star x * x` is invertible,
commutes with `e`, and

`p = e * star e * z⁻¹`.

Idempotents with the same range are similar (`TauCeti.isConj_of_mul_eq`), so every
idempotent is similar to a star projection. This is how idempotents are replaced by projections
before using constructions, such as unitary splittings, that make sense only for self-adjoint
idempotents.

## Main declarations

* `TauCeti.rangeStarProjection e`: Kaplansky's formula `e * star e * Ring.inverse z`.
* `IsIdempotentElem.isStarProjection_rangeStarProjection`: for an idempotent `e` it is a star
  projection, and `IsIdempotentElem.mul_rangeStarProjection` and
  `IsIdempotentElem.rangeStarProjection_mul` say that it has the range of `e`.
* `IsIdempotentElem.eq_rangeStarProjection_iff`: it is the only star projection with these
  properties.
* `IsIdempotentElem.isConj_rangeStarProjection`: every idempotent is similar to its range
  projection.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Proposition 4.6.2.
* I. Kaplansky, *Rings of Operators*, W. A. Benjamin (1968).
-/

public section

noncomputable section

namespace TauCeti

variable {A : Type*}

/-- Kaplansky's **range projection** of an idempotent `e`: with `x = e - star e`, it is
`e * star e * (1 + star x * x)⁻¹`. For an idempotent of a unital C*-algebra this is the unique
star projection with the range of `e` (`IsIdempotentElem.eq_rangeStarProjection_iff`); for other
elements it carries no meaning. -/
def rangeStarProjection [Ring A] [StarRing A] (e : A) : A :=
  e * star e * Ring.inverse (1 + star (e - star e) * (e - star e))

section StarRing

variable [Ring A] [StarRing A] {e : A}

/-- For an idempotent `e` and `x = e - star e`, left multiplication by `e` turns
`1 + star x * x` into `e * star e * e`. -/
private theorem mul_one_add_star_mul_self (he : IsIdempotentElem e) :
    e * (1 + star (e - star e) * (e - star e)) = e * star e * e := by
  have h : star e * star e = star e := by rw [← star_mul, he.eq]
  simp only [star_sub, star_star, mul_add, mul_one, sub_mul, mul_sub, ← mul_assoc, he.eq, h]
  abel

/-- For an idempotent `e` and `x = e - star e`, right multiplication by `e` turns
`1 + star x * x` into `e * star e * e`. -/
private theorem one_add_star_mul_self_mul (he : IsIdempotentElem e) :
    (1 + star (e - star e) * (e - star e)) * e = e * star e * e := by
  have h : star e * star e = star e := by rw [← star_mul, he.eq]
  simp only [star_sub, star_star, add_mul, one_mul, sub_mul, mul_sub, mul_assoc, he.eq, h]
  abel

/-- The range projection `p` of an idempotent `e` lies in the range of `e`: `e * p = p`. -/
@[simp] theorem _root_.IsIdempotentElem.mul_rangeStarProjection (he : IsIdempotentElem e) :
    e * rangeStarProjection e = rangeStarProjection e := by
  rw [rangeStarProjection, ← mul_assoc, ← mul_assoc, he.eq]

/-- A star projection is its own range projection. -/
@[simp] theorem _root_.IsStarProjection.rangeStarProjection_eq {p : A} (hp : IsStarProjection p) :
    rangeStarProjection p = p := by
  rw [rangeStarProjection, hp.isSelfAdjoint.star_eq, sub_self, mul_zero, add_zero,
    Ring.inverse_one, mul_one, hp.isIdempotentElem.eq]

end StarRing

variable [CStarAlgebra A] {e : A}

/-- In a unital C*-algebra, `1 + star x * x` is invertible, since it is at least `1`. -/
theorem isUnit_one_add_star_mul_self (x : A) : IsUnit (1 + star x * x) := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  exact CStarAlgebra.isUnit_of_le 1 (le_add_of_nonneg_right (star_mul_self_nonneg x))

/-- The defining properties of the range projection, proved together from the invertibility of
`z = 1 + star x * x` and the commutation of `z` with `e` and `star e`. -/
private theorem rangeStarProjection_spec (he : IsIdempotentElem e) :
    IsStarProjection (rangeStarProjection e) ∧ rangeStarProjection e * e = e := by
  obtain ⟨z, hz⟩ := isUnit_one_add_star_mul_self (e - star e)
  have hez : e * z = e * star e * e := by rw [hz, mul_one_add_star_mul_self he]
  have hze : Commute e z := by
    rw [Commute, SemiconjBy, hez, hz, one_add_star_mul_self_mul he]
  have hzs : star z = z := Units.ext <| by
    rw [Units.coe_star, hz]
    exact ((IsSelfAdjoint.one A).add (.star_mul_self _)).star_eq
  have hzse : Commute (star e) z := by simpa [← Units.coe_star, hzs] using hze.star_star
  -- With `f = e * star e` and `w = z⁻¹`, the range projection is `f * w`, and `f * f = f * z`.
  have hfw : Commute (e * star e) ↑z⁻¹ := (hze.mul_left hzse).units_inv_right
  have hff : e * star e * (e * star e) = e * star e * z := by
    rw [← mul_assoc, ← hez, mul_assoc, ← hzse.eq, ← mul_assoc]
  have hp : rangeStarProjection e = e * star e * ↑z⁻¹ := by
    rw [rangeStarProjection, ← hz, Ring.inverse_unit]
  rw [hp]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [IsIdempotentElem, hfw.symm.mul_mul_mul_comm, hff, mul_assoc, ← mul_assoc (z : A),
      Units.mul_inv, one_mul]
  · rw [IsSelfAdjoint, star_mul, ← Units.coe_star_inv, hzs, star_mul, star_star]
    exact hfw.eq.symm
  · rw [mul_assoc, ← hze.units_inv_right.eq, ← mul_assoc, ← hez, mul_assoc, Units.mul_inv,
      mul_one]

end TauCeti

namespace IsIdempotentElem

open TauCeti

variable {A : Type*} [CStarAlgebra A] {e q : A}

/-- The range projection of an idempotent of a unital C*-algebra is a star projection. -/
theorem isStarProjection_rangeStarProjection (he : IsIdempotentElem e) :
    IsStarProjection (rangeStarProjection e) :=
  (rangeStarProjection_spec he).1

/-- The range of an idempotent `e` lies in that of its range projection `p`: `p * e = e`. -/
@[simp] theorem rangeStarProjection_mul (he : IsIdempotentElem e) :
    rangeStarProjection e * e = e :=
  (rangeStarProjection_spec he).2

/-- The range projection of an idempotent `e` is the only self-adjoint element `q` with
`e * q = q` and `q * e = e`. -/
theorem eq_rangeStarProjection_iff (he : IsIdempotentElem e) (hq : IsSelfAdjoint q) :
    q = rangeStarProjection e ↔ e * q = q ∧ q * e = e := by
  refine ⟨fun h => h ▸ ⟨he.mul_rangeStarProjection, he.rangeStarProjection_mul⟩, ?_⟩
  rintro ⟨heq, hqe⟩
  have hpq : rangeStarProjection e * q = q := by
    rw [← heq, ← mul_assoc, he.rangeStarProjection_mul]
  have hqp : q * rangeStarProjection e = rangeStarProjection e := by
    rw [← he.mul_rangeStarProjection, ← mul_assoc, hqe]
  have := congrArg Star.star hpq
  rwa [star_mul, hq.star_eq, he.isStarProjection_rangeStarProjection.isSelfAdjoint.star_eq, hqp,
    eq_comm] at this

/-- Every idempotent of a unital C*-algebra is similar to its range projection. -/
theorem isConj_rangeStarProjection (he : IsIdempotentElem e) :
    IsConj (rangeStarProjection e) e :=
  isConj_of_mul_eq he.mul_rangeStarProjection he.rangeStarProjection_mul

end IsIdempotentElem
