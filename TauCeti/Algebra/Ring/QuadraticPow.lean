/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Basic

/-!
# Powers of a root of a quadratic relation

An element satisfying `a * a = c * a + 1` satisfies the corresponding recurrence on powers.
This gives the coefficient identities used for weighted eigenvectors of operators satisfying
quadratic relations, without requiring commutativity or subtraction.
-/

public section

namespace TauCeti

/-- Multiplying a quadratic relation by a power gives the recurrence on successive powers. -/
theorem mul_pow_succ_add_pow_of_mul_self_eq {R : Type*} [Semiring R] {a c : R}
    (ha : a * a = c * a + 1) (k : ℕ) :
    c * a ^ (k + 1) + a ^ k = a * a ^ (k + 1) := by
  calc
    c * a ^ (k + 1) + a ^ k = (c * a + 1) * a ^ k := by
      rw [add_mul, one_mul, mul_assoc, pow_succ']
    _ = a * a ^ (k + 1) := by rw [← ha, mul_assoc, ← pow_succ']

end TauCeti
