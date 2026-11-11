/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.Ring

/-!
# Binomial coefficients and inverse factorials

The factorial quotient formula for a binomial coefficient gives identities between products of
inverse factorials in a characteristic-zero division semiring. These are the scalar identities
used in the multiplication and binomial formulas for divided powers.

In any ring, `Nat.cast_choose_mul_sub` casts the recurrence `Nat.choose_succ_right_eq` with the
subtraction `n - k` taken in the ring.

In a characteristic-zero division semiring, `Nat.cast_choose_add_one_div_cast_choose` and
`Nat.cast_choose_add_two_div_cast_choose` give the ratios of binomial coefficients obtained by
raising both indices by one or by two.
-/

public section

namespace Nat

/-- The binomial identity `(n choose k) (n - k) = (k + 1) (n choose (k + 1))` in a ring. When
`n < k` both sides vanish. -/
theorem cast_choose_mul_sub {R : Type*} [Ring R] (n k : ℕ) :
    (n.choose k : R) * ((n : R) - k) = ((k : R) + 1) * (n.choose (k + 1) : R) := by
  rcases le_or_gt k n with h | h
  · rw [← Nat.cast_sub h, ← Nat.cast_mul, ← Nat.choose_succ_right_eq, Nat.cast_mul,
      Nat.cast_succ]
    exact (Nat.cast_commute _ _).eq
  · simp [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (h.trans (Nat.lt_succ_self k))]

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

/-- The binomial ratio `C(n + 1, k + 1) / C(n, k) = (n + 1) / (k + 1)` for `k ≤ n`. -/
theorem cast_choose_add_one_div_cast_choose {n k : ℕ} (hk : k ≤ n) :
    ((n + 1).choose (k + 1) : K) / (n.choose k : K) = ((n : K) + 1) / ((k : K) + 1) := by
  rw [(Nat.cast_commute _ _).div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hk))
    (Nat.cast_add_one_ne_zero k)]
  exact_mod_cast (Nat.add_one_mul_choose_eq n k).symm

/-- The binomial ratio `C(n + 2, k + 2) / C(n, k) = (n + 1) (n + 2) / ((k + 1) (k + 2))` for
`k ≤ n`. -/
theorem cast_choose_add_two_div_cast_choose {n k : ℕ} (hk : k ≤ n) :
    ((n + 2).choose (k + 2) : K) / (n.choose k : K) =
      ((n : K) + 1) * (n + 2) / (((k : K) + 1) * (k + 2)) := by
  -- Every term is a natural cast, so the identity is the cast of the one in `ℚ≥0`.
  have hk₁ : k + 1 ≤ n + 1 := Nat.add_le_add_right hk 1
  have h : ((n + 2).choose (k + 2) : ℚ≥0) / (n.choose k : ℚ≥0) =
      ((n : ℚ≥0) + 1) * (n + 2) / (((k : ℚ≥0) + 1) * (k + 2)) := by
    have h := cast_choose_add_one_div_cast_choose (K := ℚ≥0) hk₁
    push_cast at h
    rw [← div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hk₁) :
      ((n + 1).choose (k + 1) : ℚ≥0) ≠ 0), h, cast_choose_add_one_div_cast_choose hk,
      _root_.div_mul_div_comm]
    ring
  simpa using congrArg (NNRat.cast : ℚ≥0 → K) h

end DivisionSemiring

end Nat
