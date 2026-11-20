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
In a semigroup, if `e * p = p` and `p * e = e`, then `e` and `p` are idempotent
(`IsIdempotentElem.of_mul_eq_right`, applied in either order).

If `b * a = 1` in a monoid, then `a * e * b` is idempotent whenever `e` is. In particular,
conjugating an idempotent by a unit gives an idempotent, as does conjugating by a one-sided
inverse pair such as `1 + N` and `1 - N` for a square-zero element `N` of a ring.
-/

public section

namespace IsIdempotentElem

/-- If `e * p = p` and `p * e = e` in a semigroup, then `e` is idempotent. -/
theorem of_mul_eq_right {S : Type*} [Semigroup S] {e p : S}
    (hep : e * p = p) (hpe : p * e = e) : IsIdempotentElem e := by
  calc
    e * e = e * (p * e) := by rw [hpe]
    _ = e := by rw [← mul_assoc, hep, hpe]

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
