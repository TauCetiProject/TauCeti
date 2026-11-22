/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import TauCeti.Algebra.Ring.Idempotent.Pair
import Mathlib.Tactic.NoncommRing

/-!
# Pairs of star projections

Let `p` and `q` be star projections in a star ring. The element `z = q * p + (1 - q) * (1 - p)`
intertwines them, `z * p = q * z` (`IsIdempotentElem.intertwiner_mul`), and satisfies

`star z * z = z * star z = 1 - (p - q) ^ 2` and `z + star z = 2 * (1 - (p - q) ^ 2)`,

where `(p - q) ^ 2` commutes with `p` and `q` (`IsIdempotentElem.commute_sub_sq_left`). In a
C⋆-algebra these identities show that `z` is invertible when `‖p - q‖ < 1`, and that the unitary
part `z * (1 - (p - q) ^ 2) ^ (-1 / 2)` of its polar decomposition conjugates `p` to `q`
(`IsStarProjection.exists_mem_unitary_mul_mul_star_eq_of_norm_sub_lt_one`).

## References

* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), Section 2.2.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer, Chapter I, §4.6.
-/

public section

namespace IsStarProjection

variable {R : Type*} [Ring R] [StarRing R] {p q : R}

/-- The star of the intertwiner `q * p + (1 - q) * (1 - p)` is the intertwiner
`p * q + (1 - p) * (1 - q)` in the opposite direction. -/
theorem star_intertwiner (hp : IsStarProjection p) (hq : IsStarProjection q) :
    star (q * p + (1 - q) * (1 - p)) = p * q + (1 - p) * (1 - q) := by
  simp [star_sub, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]

/-- For the intertwiner `z = q * p + (1 - q) * (1 - p)`, `star z * z = 1 - (p - q) ^ 2`. -/
theorem star_intertwiner_mul_intertwiner (hp : IsStarProjection p) (hq : IsStarProjection q) :
    star (q * p + (1 - q) * (1 - p)) * (q * p + (1 - q) * (1 - p)) = 1 - (p - q) ^ 2 := by
  have hq₁ := hq.isIdempotentElem.one_sub
  -- The compressions `p * q * p` and `(1 - p) * (1 - q) * (1 - p)` in terms of `(p - q) ^ 2`.
  have h₁ : p * q * p = p - p * (p - q) ^ 2 := by
    rw [hp.isIdempotentElem.mul_sub_sq hq.isIdempotentElem, sub_sub_cancel]
  have h₂ : (1 - p) * (1 - q) * (1 - p) = (1 - p) - (1 - p) * (p - q) ^ 2 := by
    rw [show p - q = -((1 - p) - (1 - q)) by abel, neg_sq,
      hp.isIdempotentElem.one_sub.mul_sub_sq hq₁, sub_sub_cancel]
  have hpq : p * q * (q * p) = p * q * p := by
    rw [← mul_assoc, mul_assoc p, hq.isIdempotentElem.eq]
  have hpq₁ : (1 - p) * (1 - q) * ((1 - q) * (1 - p)) = (1 - p) * (1 - q) * (1 - p) := by
    rw [← mul_assoc, mul_assoc (1 - p), hq₁.eq]
  have hc₁ : p * q * ((1 - q) * (1 - p)) = 0 := by
    rw [mul_assoc, ← mul_assoc q, hq.mul_one_sub_self, zero_mul, mul_zero]
  have hc₂ : (1 - p) * (1 - q) * (q * p) = 0 := by
    rw [mul_assoc, ← mul_assoc (1 - q), hq.one_sub_mul_self, zero_mul, mul_zero]
  rw [hp.star_intertwiner hq, add_mul, mul_add, mul_add, hpq, hpq₁, hc₁, hc₂, add_zero, zero_add,
    h₁, h₂]
  noncomm_ring

/-- For the intertwiner `z = q * p + (1 - q) * (1 - p)`, `z * star z = 1 - (p - q) ^ 2`. -/
theorem intertwiner_mul_star_intertwiner (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (q * p + (1 - q) * (1 - p)) * star (q * p + (1 - q) * (1 - p)) = 1 - (p - q) ^ 2 := by
  have h := hq.star_intertwiner_mul_intertwiner hp
  rw [hq.star_intertwiner hp, ← neg_sub p q, neg_sq] at h
  rw [hp.star_intertwiner hq]
  exact h

/-- For the intertwiner `z = q * p + (1 - q) * (1 - p)`, `z + star z = 2 * (1 - (p - q) ^ 2)`. -/
theorem intertwiner_add_star_intertwiner (hp : IsStarProjection p) (hq : IsStarProjection q) :
    q * p + (1 - q) * (1 - p) + star (q * p + (1 - q) * (1 - p)) = 2 * (1 - (p - q) ^ 2) := by
  rw [hp.star_intertwiner hq, hp.isIdempotentElem.sub_sq hq.isIdempotentElem]
  noncomm_ring

end IsStarProjection
