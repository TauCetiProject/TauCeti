/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Idempotent

/-!
# Idempotents

An injective multiplicative map reflects idempotents (`IsIdempotentElem.map_iff`).

If `b * a = 1` in a monoid, then `a * e * b` is idempotent whenever `e` is. In particular,
conjugating an idempotent by a unit gives an idempotent, as does conjugating by a one-sided
inverse pair such as `1 + N` and `1 - N` for a square-zero element `N` of a ring.

In a semigroup, an element `s` commuting with an idempotent `p` gives the element `s * p` of the
corner `p * M * p` (`IsIdempotentElem.mul_mul_mul_of_commute`).
-/

public section

namespace IsIdempotentElem

section Semigroup

variable {M : Type*} [Semigroup M] {p s : M}

/-- If `s` commutes with an idempotent `p`, then `s * p` lies in the corner `p * M * p`. -/
theorem mul_mul_mul_of_commute (hp : IsIdempotentElem p) (hsp : Commute s p) :
    p * (s * p) * p = s * p := by
  simp only [mul_assoc, hsp.symm.left_comm, hp.eq]

end Semigroup

variable {M : Type*} [Monoid M] {e a b : M}

/-- If `b * a = 1`, then `a * e * b` is idempotent whenever `e` is. -/
theorem mul_mul_of_mul_eq_one (he : IsIdempotentElem e) (h : b * a = 1) :
    IsIdempotentElem (a * e * b) := by
  calc a * e * b * (a * e * b) = a * e * (b * a) * e * b := by simp only [mul_assoc]
    _ = a * e * b := by rw [h, mul_one, he.mul_mul_self]

/-- Idempotency is reflected by an injective multiplicative map. -/
theorem map_iff {M N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] {f : F}
    (hf : Function.Injective f) {e : M} : IsIdempotentElem (f e) ↔ IsIdempotentElem e :=
  ⟨fun h ↦ hf (by rw [map_mul]; exact h.eq), fun h ↦ h.map f⟩

end IsIdempotentElem
