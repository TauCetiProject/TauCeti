/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Cast.Commute

/-!
# Binomial coefficients and inverse factorials

The factorial quotient formula for a binomial coefficient gives identities between products of
inverse factorials in a characteristic-zero division semiring. These are the scalar identities
used in the multiplication and binomial formulas for divided powers.

In any ring, `Nat.cast_choose_mul_sub` casts the recurrence `Nat.choose_succ_right_eq` with the
subtraction `n - k` taken in the ring.
-/

public section

namespace Nat

/-- The binomial identity `(n choose k) (n - k) = (k + 1) (n choose (k + 1))` in a ring, for
`k ≤ n`. -/
theorem cast_choose_mul_sub {R : Type*} [Ring R] {n k : ℕ} (h : k ≤ n) :
    (n.choose k : R) * ((n : R) - k) = ((k : R) + 1) * (n.choose (k + 1) : R) := by
  rw [← Nat.cast_sub h, ← Nat.cast_mul, ← Nat.choose_succ_right_eq, Nat.cast_mul, Nat.cast_succ]
  exact (Nat.cast_commute _ _).eq

section DivisionSemiring

variable {K : Type*} [DivisionSemiring K] [CharZero K]

/-- A product of inverse factorials is the binomial coefficient times the inverse factorial
of the sum. -/
theorem inv_factorial_mul_inv_factorial (m n : ℕ) :
    (m.factorial : K)⁻¹ * (n.factorial : K)⁻¹ =
      (Nat.choose (m + n) m : K) * ((m + n).factorial : K)⁻¹ := by
  rw [Nat.cast_add_choose K, div_eq_mul_inv,
    (Nat.cast_commute (m + n).factorial _).eq,
    mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), ← mul_inv_rev]
  exact congrArg Inv.inv (Nat.cast_commute n.factorial (m.factorial : K)).eq

/-- Multiplying an inverse factorial by a binomial coefficient splits it into the inverse
factorials of the two complementary indices. -/
theorem inv_factorial_mul_choose (n i j : ℕ) (hij : i + j = n) :
    (n.factorial : K)⁻¹ * Nat.choose n i =
      (i.factorial : K)⁻¹ * (j.factorial : K)⁻¹ := by
  subst n
  rw [(Nat.commute_cast _ (Nat.choose (i + j) i)).eq]
  exact (inv_factorial_mul_inv_factorial i j).symm

end DivisionSemiring

end Nat
