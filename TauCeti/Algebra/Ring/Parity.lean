/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Parity

/-!
# Odd powers of a negated element

This file records the identity `1 - (-x)^{2n+1} = 1 + x^{2n+1}` in a ring, which turns a product
of factors `1 - (-q)^{2n+1}` into a product of factors `1 + q^{2n+1}`.
-/

public section

namespace TauCeti

/-- `1 - (-x)^{2n+1} = 1 + x^{2n+1}`. -/
theorem one_sub_neg_pow_odd {R : Type*} [Ring R] (x : R) (n : ℕ) :
    1 - (-x) ^ (2 * n + 1) = 1 + x ^ (2 * n + 1) := by
  rw [Odd.neg_pow (by simp), sub_neg_eq_add]

end TauCeti

end
