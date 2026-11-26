/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.NoncommRing

/-!
# Pairs of idempotents

Let `p` and `q` be idempotents in a ring. The square `(p - q) ^ 2 = p - p * q - q * p + q` of their
difference commutes with both `p` and `q`, and their intertwiner
`TauCeti.intertwiner p q = q * p + (1 - q) * (1 - p)` carries `p` to `q`:
`intertwiner p q * p = q * intertwiner p q`. For star projections the polar decomposition of the
intertwiner conjugates `p` to `q` when `‖p - q‖ < 1`; see `TauCeti.Algebra.Star.Projection.Pair`.

## Main definitions

* `TauCeti.intertwiner p q`: the element `q * p + (1 - q) * (1 - p)`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, Chapter I, §4.6.
-/

public section

namespace TauCeti

/-- The intertwiner `q * p + (1 - q) * (1 - p)` of two elements `p` and `q` of a ring. When `p` and
`q` are idempotents it carries `p` to `q`, `intertwiner p q * p = q * intertwiner p q`
(`IsIdempotentElem.intertwiner_mul`). -/
def intertwiner {R : Type*} [Ring R] (p q : R) : R :=
  q * p + (1 - q) * (1 - p)

/-- The defining formula of the intertwiner. -/
theorem intertwiner_def {R : Type*} [Ring R] (p q : R) :
    intertwiner p q = q * p + (1 - q) * (1 - p) :=
  (rfl)

end TauCeti

open TauCeti

namespace IsIdempotentElem

variable {R : Type*} [Ring R] {p q : R}

/-- The square of the difference of two idempotents is `p - p * q - q * p + q`. -/
theorem sub_sq (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    (p - q) ^ 2 = p - p * q - q * p + q := by
  rw [sq, mul_sub, sub_mul, sub_mul, hp.eq, hq.eq]
  abel

/-- Left multiplication of `(p - q) ^ 2` by the idempotent `p` gives `p - p * q * p`. -/
theorem mul_sub_sq (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    p * (p - q) ^ 2 = p - p * q * p := by
  rw [hp.sub_sq hq, mul_add, mul_sub, mul_sub, hp.eq, ← mul_assoc, ← mul_assoc, hp.eq]
  abel

/-- Right multiplication of `(p - q) ^ 2` by the idempotent `p` gives `p - p * q * p`. -/
theorem sub_sq_mul (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    (p - q) ^ 2 * p = p - p * q * p := by
  rw [hp.sub_sq hq, add_mul, sub_mul, sub_mul, hp.eq, mul_assoc, mul_assoc, hp.eq]
  noncomm_ring

/-- The square of the difference of two idempotents commutes with the first. -/
theorem commute_sub_sq_left (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    Commute p ((p - q) ^ 2) :=
  (hp.mul_sub_sq hq).trans (hp.sub_sq_mul hq).symm

/-- The square of the difference of two idempotents commutes with the second. -/
theorem commute_sub_sq_right (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    Commute q ((p - q) ^ 2) := by
  rw [← neg_sub, neg_sq]
  exact hq.commute_sub_sq_left hp

/-- The intertwiner of an idempotent with itself is `1`. -/
@[simp]
theorem intertwiner_self (hp : IsIdempotentElem p) : intertwiner p p = 1 := by
  rw [intertwiner_def, hp.eq, hp.one_sub.eq, add_sub_cancel]

/-- The intertwiner of an idempotent with itself is invertible. -/
theorem isUnit_intertwiner_self (hp : IsIdempotentElem p) : IsUnit (intertwiner p p) :=
  hp.intertwiner_self ▸ isUnit_one

/-- **Intertwining.** The intertwiner `q * p + (1 - q) * (1 - p)` carries the idempotent `p` to the
idempotent `q`. -/
theorem intertwiner_mul (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    intertwiner p q * p = q * intertwiner p q := by
  rw [intertwiner_def, add_mul, mul_add, mul_assoc, hp.eq, mul_assoc, hp.one_sub_mul_self,
    ← mul_assoc, hq.eq, ← mul_assoc, hq.mul_one_sub_self, mul_zero, zero_mul]

end IsIdempotentElem
