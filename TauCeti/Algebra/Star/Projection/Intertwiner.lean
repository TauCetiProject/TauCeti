/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.NoncommRing

/-!
# Kato's intertwiner for pairs of idempotents and star projections

For idempotents `p, q` in a ring `R`, `projectionIntertwiner p q = q * p + (1 - q) * (1 - p)`
satisfies `q * z = q * p = z * p`, `projectionIntertwiner q p * z = z * projectionIntertwiner q p =
1 - (p - q) ^ 2`, and commutes with `1 - (p - q) ^ 2`. For star projections, `star z` swaps `p, q`.

## Main definitions

* `TauCeti.projectionIntertwiner p q`: `q * p + (1 - q) * (1 - p)`.

## Main statements

* `IsIdempotentElem.mul_projectionIntertwiner_eq_projectionIntertwiner_mul`,
  `IsIdempotentElem.projectionIntertwiner_swap_mul_self`,
  `IsIdempotentElem.projectionIntertwiner_mul_swap`.
* `IsStarProjection.star_projectionIntertwiner_mul_self`,
  `IsStarProjection.projectionIntertwiner_mul_star_self`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1966), Chapter I, §4.6.
* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.4.3.2.
-/

public section

namespace TauCeti

variable {R S : Type*} [Ring R] [Ring S]

/-- **Kato's intertwiner** `q * p + (1 - q) * (1 - p)` for two idempotents `p` and `q` in a ring. -/
def projectionIntertwiner (p q : R) : R := q * p + (1 - q) * (1 - p)

/-- Unfold `TauCeti.projectionIntertwiner`. -/
theorem projectionIntertwiner_def (p q : R) :
    projectionIntertwiner p q = q * p + (1 - q) * (1 - p) := (rfl)

/-- Expanded form `1 - p - q + 2 • (q * p)` of `TauCeti.projectionIntertwiner`. -/
theorem projectionIntertwiner_eq_one_sub_add (p q : R) :
    projectionIntertwiner p q = 1 - p - q + 2 • (q * p) := by
  rw [projectionIntertwiner_def]; noncomm_ring

/-- Kato's intertwiner of `0` with `0` is `1`. -/
@[simp] theorem projectionIntertwiner_zero_zero : projectionIntertwiner (0 : R) 0 = 1 := by
  simp [projectionIntertwiner_def]

/-- Kato's intertwiner of `1` with `1` is `1`. -/
@[simp] theorem projectionIntertwiner_one_one : projectionIntertwiner (1 : R) 1 = 1 := by
  simp [projectionIntertwiner_def]

/-- Passing to `1 - p` and `1 - q` leaves `TauCeti.projectionIntertwiner` unchanged. -/
@[simp] theorem projectionIntertwiner_one_sub (p q : R) :
    projectionIntertwiner (1 - p) (1 - q) = projectionIntertwiner p q := by
  rw [projectionIntertwiner_def, projectionIntertwiner_def]; noncomm_ring

/-- Any unital ring homomorphism preserves `TauCeti.projectionIntertwiner`. -/
theorem map_projectionIntertwiner {F : Type*} [FunLike F R S] [RingHomClass F R S]
    (φ : F) (p q : R) : φ (projectionIntertwiner p q) = projectionIntertwiner (φ p) (φ q) := by
  simp [projectionIntertwiner_def]

/-- Taking the star of `TauCeti.projectionIntertwiner p q` for self-adjoint `p, q` swaps `p, q`. -/
theorem star_projectionIntertwiner [StarRing R] {p q : R}
    (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) :
    star (projectionIntertwiner p q) = projectionIntertwiner q p := by
  simp [projectionIntertwiner_def, hp.star_eq, hq.star_eq]

end TauCeti

namespace IsIdempotentElem

open TauCeti

variable {R : Type*} [Ring R] {p q : R}

/-- The intertwiner of an idempotent with itself is `1`. -/
theorem projectionIntertwiner_self (hp : IsIdempotentElem p) : projectionIntertwiner p p = 1 := by
  rw [projectionIntertwiner_def]; noncomm_ring [hp.eq]

/-- Right-multiplying `projectionIntertwiner p q` by an idempotent `p` retains `q * p`. -/
theorem projectionIntertwiner_mul (hp : IsIdempotentElem p) (q : R) :
    projectionIntertwiner p q * p = q * p := by
  rw [projectionIntertwiner_def]; noncomm_ring [hp.eq]

/-- Left-multiplying `projectionIntertwiner p q` by an idempotent `q` retains `q * p`. -/
theorem mul_projectionIntertwiner (hq : IsIdempotentElem q) (p : R) :
    q * projectionIntertwiner p q = q * p := by
  rw [projectionIntertwiner_def]; noncomm_ring [hq.eq, hq.mul_self_mul]

/-- **Kato's intertwining relation** `q * projectionIntertwiner p q = projectionIntertwiner p q * p`
for two idempotents `p` and `q`. -/
theorem mul_projectionIntertwiner_eq_projectionIntertwiner_mul
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    q * projectionIntertwiner p q = projectionIntertwiner p q * p := by
  rw [hq.mul_projectionIntertwiner, hp.projectionIntertwiner_mul]

/-- `projectionIntertwiner q p * projectionIntertwiner p q = 1 - (p - q) ^ 2`. -/
theorem projectionIntertwiner_swap_mul_self (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    projectionIntertwiner q p * projectionIntertwiner p q = 1 - (p - q) ^ 2 := by
  rw [projectionIntertwiner_def, projectionIntertwiner_def]
  noncomm_ring [hp.eq, hq.eq, hp.mul_self_mul, hq.mul_self_mul]

/-- `projectionIntertwiner p q * projectionIntertwiner q p = 1 - (p - q) ^ 2`. -/
theorem projectionIntertwiner_mul_swap (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    projectionIntertwiner p q * projectionIntertwiner q p = 1 - (p - q) ^ 2 := by
  rw [hq.projectionIntertwiner_swap_mul_self hp]; noncomm_ring

/-- Symmetrizing `projectionIntertwiner p q` gives `2 • (1 - (p - q) ^ 2)`. -/
theorem projectionIntertwiner_add_swap (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    projectionIntertwiner p q + projectionIntertwiner q p = 2 • (1 - (p - q) ^ 2) := by
  rw [projectionIntertwiner_def, projectionIntertwiner_def]; noncomm_ring [hp.eq, hq.eq]

/-- For two idempotents `p` and `q`, `p` commutes with `(p - q) ^ 2`. -/
theorem commute_sub_sq (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    Commute p ((p - q) ^ 2) := by
  rw [Commute, SemiconjBy]; noncomm_ring [hp.eq, hq.eq, hp.mul_self_mul]

/-- For two idempotents `p` and `q`, `p` commutes with `1 - (p - q) ^ 2`. -/
theorem commute_one_sub_sub_sq (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    Commute p (1 - (p - q) ^ 2) :=
  (Commute.one_right p).sub_right (hp.commute_sub_sq hq)

/-- For two idempotents `p` and `q`, `projectionIntertwiner p q` commutes with `1 - (p - q) ^ 2`. -/
theorem commute_projectionIntertwiner_one_sub_sub_sq
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    Commute (projectionIntertwiner p q) (1 - (p - q) ^ 2) := by
  rw [Commute, SemiconjBy, projectionIntertwiner_def]
  noncomm_ring [hp.eq, hq.eq, hp.mul_self_mul, hq.mul_self_mul]

end IsIdempotentElem

namespace IsStarProjection

open TauCeti

variable {R : Type*} [Ring R] [StarRing R] {p q : R}

/-- For star projections `p, q`, `star z * z = 1 - (p - q) ^ 2`. -/
theorem star_projectionIntertwiner_mul_self (hp : IsStarProjection p) (hq : IsStarProjection q) :
    star (projectionIntertwiner p q) * projectionIntertwiner p q = 1 - (p - q) ^ 2 := by
  rw [star_projectionIntertwiner hp.isSelfAdjoint hq.isSelfAdjoint,
    hp.isIdempotentElem.projectionIntertwiner_swap_mul_self hq.isIdempotentElem]

/-- For star projections `p, q`, `z * star z = 1 - (p - q) ^ 2`. -/
theorem projectionIntertwiner_mul_star_self (hp : IsStarProjection p) (hq : IsStarProjection q) :
    projectionIntertwiner p q * star (projectionIntertwiner p q) = 1 - (p - q) ^ 2 := by
  rw [star_projectionIntertwiner hp.isSelfAdjoint hq.isSelfAdjoint,
    hp.isIdempotentElem.projectionIntertwiner_mul_swap hq.isIdempotentElem]

/-- For star projections `p, q`, `z + star z = 2 • (1 - (p - q) ^ 2)`. -/
theorem projectionIntertwiner_add_star (hp : IsStarProjection p) (hq : IsStarProjection q) :
    projectionIntertwiner p q + star (projectionIntertwiner p q) = 2 • (1 - (p - q) ^ 2) := by
  rw [star_projectionIntertwiner hp.isSelfAdjoint hq.isSelfAdjoint,
    hp.isIdempotentElem.projectionIntertwiner_add_swap hq.isIdempotentElem]

end IsStarProjection
