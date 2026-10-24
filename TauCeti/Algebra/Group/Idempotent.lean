/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Idempotent

/-!
# Conjugating idempotents

If `b * a = 1` in a monoid, then `a * e * b` is idempotent whenever `e` is. In particular,
conjugating an idempotent by a unit gives an idempotent, as does conjugating by a one-sided
inverse pair such as `1 + N` and `1 - N` for a square-zero element `N` of a ring.
-/

public section

namespace IsIdempotentElem

variable {M : Type*} [Monoid M] {e a b : M}

/-- If `b * a = 1`, then `a * e * b` is idempotent whenever `e` is. -/
theorem mul_mul_of_mul_eq_one (he : IsIdempotentElem e) (h : b * a = 1) :
    IsIdempotentElem (a * e * b) := by
  calc a * e * b * (a * e * b) = a * e * (b * a) * e * b := by simp only [mul_assoc]
    _ = a * e * b := by rw [h, mul_one, he.mul_mul_self]

end IsIdempotentElem
