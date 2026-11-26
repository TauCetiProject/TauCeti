/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Algebra.Ring.Prod

/-!
# Lemmas about the product ring `R × R`

Over a ring with invertible `2`, the half-sum and half-difference of a pair
have sum and difference equal to that pair (`Prod.invOf_two_mul_add_sub`).
A ring endomorphism of `R × R` acting as the swap `(a, b) ↦ (b, a)` is an involution
(`RingHomInvPair.of_forall_eq_swap`).
-/

public section

namespace Prod

variable {R : Type*} [Ring R] [Invertible (2 : R)]

/-- The pair `(⅟2 (x + y), ⅟2 (x - y))` is sent back to `(x, y)` by `(a, b) ↦ (a + b, a - b)`. -/
theorem invOf_two_mul_add_sub (z : R × R) :
    (⅟(2 : R) * (z.1 + z.2) + ⅟(2 : R) * (z.1 - z.2),
      ⅟(2 : R) * (z.1 + z.2) - ⅟(2 : R) * (z.1 - z.2)) = z := by
  ext <;> simp [← mul_add, ← mul_sub, ← two_mul]

end Prod

/-- A ring endomorphism of `R × R` acting as the swap `(a, b) ↦ (b, a)` is an involution. -/
theorem RingHomInvPair.of_forall_eq_swap {R : Type*} [Semiring R] {σ : R × R →+* R × R}
    (hσ : ∀ x, σ x = x.swap) : RingHomInvPair σ σ :=
  ⟨RingHom.ext fun x ↦ by simp [hσ], RingHom.ext fun x ↦ by simp [hσ]⟩
