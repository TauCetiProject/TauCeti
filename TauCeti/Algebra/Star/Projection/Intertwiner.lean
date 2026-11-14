/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.NoncommRing

/-!
# Kato's intertwiner for pairs of idempotents and star projections

To compare or transport invariants between two nearby idempotents or projections `p, q` in a ring
`R` (for instance in perturbation theory of spectral projections or in operator K-theory), one needs
an explicit algebraic element that intertwines `p` with `q` and reduces to `1` when `p = q`. Kato's
intertwiner `projectionIntertwiner p q = q * p + (1 - q) * (1 - p)` sends the range of `p` to `q`
and the complementary range of `1 - p` to `1 - q`: for idempotents `p, q`, it satisfies
`q * projectionIntertwiner p q = q * p = projectionIntertwiner p q * p`, its products with
`projectionIntertwiner q p` on both sides equal `1 - (p - q) ^ 2`, and it commutes with
`1 - (p - q) ^ 2`. Consequently, in any Banach or C⋆-algebra `projectionIntertwiner p q` becomes
invertible—and in a C⋆-algebra polar-normalizable to a conjugating unitary—as soon as `‖p - q‖ < 1`.

## Main definitions

* `TauCeti.projectionIntertwiner p q`: Kato's intertwiner `q * p + (1 - q) * (1 - p)`.

## Main statements

* `IsIdempotentElem.mul_projectionIntertwiner_eq_projectionIntertwiner_mul`,
  `IsIdempotentElem.projectionIntertwiner_swap_mul_self`,
  `IsIdempotentElem.projectionIntertwiner_mul_swap`.
* `IsStarProjection.star_projectionIntertwiner_mul_self`,
  `IsStarProjection.projectionIntertwiner_mul_star_self`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1966), Chapter I, §4.6.
* B. Blackadar, *Operator Algebras*, Springer (2006), Section II.3.3.
-/

public section

namespace TauCeti

variable {R S : Type*} [Ring R] [Ring S]

/-- **Kato's intertwiner** `q * p + (1 - q) * (1 - p)` for two elements `p` and `q` in a ring. -/
def projectionIntertwiner (p q : R) : R := q * p + (1 - q) * (1 - p)

/-- Unfold `TauCeti.projectionIntertwiner`. -/
theorem projectionIntertwiner_def (p q : R) :
    projectionIntertwiner p q = q * p + (1 - q) * (1 - p) := (rfl)

/-- Expanded form `1 - p - q + 2 • (q * p)` of `TauCeti.projectionIntertwiner`. -/
theorem projectionIntertwiner_eq_one_sub_add (p q : R) :
    projectionIntertwiner p q = 1 - p - q + 2 • (q * p) := by
  rw [projectionIntertwiner_def]; noncomm_ring

/-- Kato's intertwiner with `0` on the left is `1 - q`. -/
@[simp] theorem projectionIntertwiner_zero_left (q : R) :
    projectionIntertwiner 0 q = 1 - q := by
  simp [projectionIntertwiner_def]

/-- Kato's intertwiner with `0` on the right is `1 - p`. -/
@[simp] theorem projectionIntertwiner_zero_right (p : R) :
    projectionIntertwiner p 0 = 1 - p := by
  simp [projectionIntertwiner_def]

/-- Kato's intertwiner with `1` on the left is `q`. -/
@[simp] theorem projectionIntertwiner_one_left (q : R) :
    projectionIntertwiner 1 q = q := by
  simp [projectionIntertwiner_def]

/-- Kato's intertwiner with `1` on the right is `p`. -/
@[simp] theorem projectionIntertwiner_one_right (p : R) :
    projectionIntertwiner p 1 = p := by
  simp [projectionIntertwiner_def]

/-- Passing to `1 - p` and `1 - q` leaves `TauCeti.projectionIntertwiner` unchanged. -/
@[simp] theorem projectionIntertwiner_one_sub (p q : R) :
    projectionIntertwiner (1 - p) (1 - q) = projectionIntertwiner p q := by
  rw [projectionIntertwiner_def, projectionIntertwiner_def]; noncomm_ring

/-- `TauCeti.projectionIntertwiner p q` lies in any unital subring containing `p` and `q`. -/
theorem projectionIntertwiner_mem {T : Type*} [SetLike T R] [SubringClass T R] {s : T} {p q : R}
    (hp : p ∈ s) (hq : q ∈ s) : projectionIntertwiner p q ∈ s := by
  rw [projectionIntertwiner_def]
  exact add_mem (mul_mem hq hp) (mul_mem (sub_mem (one_mem s) hq) (sub_mem (one_mem s) hp))

/-- Any unital ring homomorphism preserves `TauCeti.projectionIntertwiner`. -/
theorem map_projectionIntertwiner {F : Type*} [FunLike F R S] [RingHomClass F R S]
    (φ : F) (p q : R) : φ (projectionIntertwiner p q) = projectionIntertwiner (φ p) (φ q) := by
  simp [projectionIntertwiner_def]

/-- Taking the star of `TauCeti.projectionIntertwiner p q` swaps and stars the arguments. -/
@[simp] theorem star_projectionIntertwiner [StarRing R] (p q : R) :
    star (projectionIntertwiner p q) = projectionIntertwiner (star q) (star p) := by
  simp [projectionIntertwiner_def]

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

/-- For star projections `p, q`,
`star (projectionIntertwiner p q) * projectionIntertwiner p q = 1 - (p - q) ^ 2`. -/
theorem star_projectionIntertwiner_mul_self (hp : IsStarProjection p) (hq : IsStarProjection q) :
    star (projectionIntertwiner p q) * projectionIntertwiner p q = 1 - (p - q) ^ 2 := by
  rw [star_projectionIntertwiner, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
    hp.isIdempotentElem.projectionIntertwiner_swap_mul_self hq.isIdempotentElem]

/-- For star projections `p, q`,
`projectionIntertwiner p q * star (projectionIntertwiner p q) = 1 - (p - q) ^ 2`. -/
theorem projectionIntertwiner_mul_star_self (hp : IsStarProjection p) (hq : IsStarProjection q) :
    projectionIntertwiner p q * star (projectionIntertwiner p q) = 1 - (p - q) ^ 2 := by
  rw [star_projectionIntertwiner, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
    hp.isIdempotentElem.projectionIntertwiner_mul_swap hq.isIdempotentElem]

/-- For star projections `p, q`,
`projectionIntertwiner p q + star (projectionIntertwiner p q) = 2 • (1 - (p - q) ^ 2)`. -/
theorem projectionIntertwiner_add_star (hp : IsStarProjection p) (hq : IsStarProjection q) :
    projectionIntertwiner p q + star (projectionIntertwiner p q) = 2 • (1 - (p - q) ^ 2) := by
  rw [star_projectionIntertwiner, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
    hp.isIdempotentElem.projectionIntertwiner_add_swap hq.isIdempotentElem]

end IsStarProjection
