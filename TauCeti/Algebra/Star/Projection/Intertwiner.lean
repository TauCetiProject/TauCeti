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

To compare nearby idempotents or projections `p, q` in perturbation theory and operator K-theory,
Kato's intertwiner `projectionIntertwiner p q = q * p + (1 - q) * (1 - p)` maps the range of `p`
to `q` and `1 - p` to `1 - q`, equals `1` when `p = q`, satisfies
`projectionIntertwiner q p * projectionIntertwiner p q = 1 - (p - q) ^ 2` (and symmetrically), and
commutes with `1 - (p - q) ^ 2`.

## Main results

* `TauCeti.projectionIntertwiner`, `IsIdempotentElem.projectionIntertwiner_swap_mul_self`,
  `IsIdempotentElem.mul_projectionIntertwiner_eq_projectionIntertwiner_mul`,
  `IsStarProjection.star_projectionIntertwiner_mul_self`.

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
/-- Kato's intertwiner with `0` on the left is `1 - q`. -/
@[simp] theorem projectionIntertwiner_zero_left (q : R) :
    projectionIntertwiner 0 q = 1 - q := by simp [projectionIntertwiner_def]
/-- Kato's intertwiner with `0` on the right is `1 - p`. -/
@[simp] theorem projectionIntertwiner_zero_right (p : R) :
    projectionIntertwiner p 0 = 1 - p := by simp [projectionIntertwiner_def]
/-- Kato's intertwiner with `1` on the left is `q`. -/
@[simp] theorem projectionIntertwiner_one_left (q : R) :
    projectionIntertwiner 1 q = q := by simp [projectionIntertwiner_def]
/-- Kato's intertwiner with `1` on the right is `p`. -/
@[simp] theorem projectionIntertwiner_one_right (p : R) :
    projectionIntertwiner p 1 = p := by simp [projectionIntertwiner_def]
/-- Passing to `1 - p` and `1 - q` leaves `TauCeti.projectionIntertwiner` unchanged. -/
@[simp] theorem projectionIntertwiner_one_sub (p q : R) :
    projectionIntertwiner (1 - p) (1 - q) = projectionIntertwiner p q := by
  simp only [projectionIntertwiner_def]; noncomm_ring
/-- `TauCeti.projectionIntertwiner p q` lies in any unital subring containing `p` and `q`. -/
theorem projectionIntertwiner_mem {T : Type*} [SetLike T R] [SubringClass T R] {s : T} {p q : R}
    (hp : p ∈ s) (hq : q ∈ s) : projectionIntertwiner p q ∈ s :=
  add_mem (mul_mem hq hp) (mul_mem (sub_mem (one_mem s) hq) (sub_mem (one_mem s) hp))
/-- Any unital ring homomorphism preserves `TauCeti.projectionIntertwiner`. -/
theorem map_projectionIntertwiner {F : Type*} [FunLike F R S] [RingHomClass F R S] (φ : F)
    (p q : R) : φ (projectionIntertwiner p q) = projectionIntertwiner (φ p) (φ q) := by
  simp [projectionIntertwiner_def]
/-- Taking the star of `TauCeti.projectionIntertwiner p q` swaps and stars the arguments. -/
@[simp] theorem star_projectionIntertwiner [StarRing R] (p q : R) :
    star (projectionIntertwiner p q) = projectionIntertwiner (star q) (star p) := by
  simp [projectionIntertwiner_def]
end TauCeti

open TauCeti

namespace IsIdempotentElem
variable {R : Type*} [Ring R] {p q : R}
/-- The intertwiner of an idempotent with itself is `1`. -/
@[simp] theorem projectionIntertwiner_self (hp : IsIdempotentElem p) :
    projectionIntertwiner p p = 1 := by
  rw [projectionIntertwiner_def]; noncomm_ring [hp.eq]
/-- Right-multiplying `projectionIntertwiner p q` by an idempotent `p` retains `q * p`. -/
theorem projectionIntertwiner_mul (hp : IsIdempotentElem p) (q : R) :
    projectionIntertwiner p q * p = q * p := by rw [projectionIntertwiner_def]; noncomm_ring [hp.eq]
/-- Left-multiplying `projectionIntertwiner p q` by an idempotent `q` retains `q * p`. -/
theorem mul_projectionIntertwiner (hq : IsIdempotentElem q) (p : R) :
    q * projectionIntertwiner p q = q * p := by
  rw [projectionIntertwiner_def]; noncomm_ring [hq.eq, hq.mul_self_mul]
/-- **Kato's intertwining relation**: `q * z = z * p` for `z = projectionIntertwiner p q`. -/
theorem mul_projectionIntertwiner_eq_projectionIntertwiner_mul (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) : q * projectionIntertwiner p q = projectionIntertwiner p q * p := by
  rw [hq.mul_projectionIntertwiner, hp.projectionIntertwiner_mul]
/-- `projectionIntertwiner q p * projectionIntertwiner p q = 1 - (p - q) ^ 2`. -/
theorem projectionIntertwiner_swap_mul_self (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    projectionIntertwiner q p * projectionIntertwiner p q = 1 - (p - q) ^ 2 := by
  unfold projectionIntertwiner; noncomm_ring [hp.eq, hq.eq, hp.mul_self_mul, hq.mul_self_mul]
/-- `projectionIntertwiner p q * projectionIntertwiner q p = 1 - (p - q) ^ 2`. -/
theorem projectionIntertwiner_mul_swap (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    projectionIntertwiner p q * projectionIntertwiner q p = 1 - (p - q) ^ 2 := by
  rw [hq.projectionIntertwiner_swap_mul_self hp]; noncomm_ring
/-- Symmetrizing `projectionIntertwiner p q` gives `2 • (1 - (p - q) ^ 2)`. -/
theorem projectionIntertwiner_add_swap (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    projectionIntertwiner p q + projectionIntertwiner q p = 2 • (1 - (p - q) ^ 2) := by
  simp only [projectionIntertwiner_def]; noncomm_ring [hp.eq, hq.eq]
/-- For idempotents `p, q`, `projectionIntertwiner p q` commutes with `1 - (p - q) ^ 2`. -/
theorem commute_projectionIntertwiner_one_sub_sub_sq (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) : Commute (projectionIntertwiner p q) (1 - (p - q) ^ 2) := by
  rw [Commute, SemiconjBy, projectionIntertwiner_def]
  noncomm_ring [hp.eq, hq.eq, hp.mul_self_mul, hq.mul_self_mul]
end IsIdempotentElem

namespace IsStarProjection
variable {R : Type*} [Ring R] [StarRing R] {p q : R}
/-- `star (projectionIntertwiner p q) * projectionIntertwiner p q = 1 - (p - q) ^ 2`. -/
theorem star_projectionIntertwiner_mul_self (hp : IsStarProjection p) (hq : IsStarProjection q) :
    star (projectionIntertwiner p q) * projectionIntertwiner p q = 1 - (p - q) ^ 2 := by
  simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using
    hp.isIdempotentElem.projectionIntertwiner_swap_mul_self hq.isIdempotentElem
/-- `projectionIntertwiner p q * star (projectionIntertwiner p q) = 1 - (p - q) ^ 2`. -/
theorem projectionIntertwiner_mul_star_self (hp : IsStarProjection p) (hq : IsStarProjection q) :
    projectionIntertwiner p q * star (projectionIntertwiner p q) = 1 - (p - q) ^ 2 := by
  simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using
    hp.isIdempotentElem.projectionIntertwiner_mul_swap hq.isIdempotentElem
/-- `projectionIntertwiner p q + star (projectionIntertwiner p q) = 2 • (1 - (p - q) ^ 2)`. -/
theorem projectionIntertwiner_add_star (hp : IsStarProjection p) (hq : IsStarProjection q) :
    projectionIntertwiner p q + star (projectionIntertwiner p q) = 2 • (1 - (p - q) ^ 2) := by
  simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using
    hp.isIdempotentElem.projectionIntertwiner_add_swap hq.isIdempotentElem
end IsStarProjection
