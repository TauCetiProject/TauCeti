/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Defs

import Mathlib.Tactic.Ring

/-!
# Extracting weighted prime powers from a pair of integers

Call a pair of integers `(A, B)` *primitive of weight `(m, n)`* if no prime `ℓ` has both
`ℓ ^ m ∣ A` and `ℓ ^ n ∣ B`. For positive weights, every pair not both zero is
`(d ^ m * A', d ^ n * B')` for a nonzero integer `d` and a pair `(A', B')` primitive of weight
`(m, n)`: stripping one prime at a time strictly decreases `|A| + |B|`. For weight `(1, 1)` this
is the extraction of a greatest common divisor, as in `Int.exists_gcd_one`; for weight `(4, 6)`
it produces the minimal-pair short Weierstrass equation `y² = x³ + Ax + B` of an elliptic curve
over `ℚ`, where `(A, B) ↦ (u⁴A, u⁶B)` is the coefficient freedom of a short equation.

## Main results

* `Int.exists_eq_pow_mul_and_forall_prime_not_pow_dvd_of_ne_zero`: the statement above.
-/

public section

namespace Int

/-- **Every pair of integers, not both zero, is a weighted power times a primitive pair**: for
positive weights `m` and `n` there are `d ≠ 0` and `A'`, `B'` with `A = d ^ m * A'`,
`B = d ^ n * B'`, and no prime `ℓ` with both `ℓ ^ m ∣ A'` and `ℓ ^ n ∣ B'`. -/
theorem exists_eq_pow_mul_and_forall_prime_not_pow_dvd_of_ne_zero {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (A B : ℤ) (h : A ≠ 0 ∨ B ≠ 0) :
    ∃ d A' B' : ℤ, d ≠ 0 ∧ A = d ^ m * A' ∧ B = d ^ n * B' ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ((ℓ : ℤ) ^ m ∣ A' ∧ (ℓ : ℤ) ^ n ∣ B') := by
  -- Strong induction on `|A| + |B|`, stripping one prime `ℓ` with `ℓ ^ m ∣ A` and `ℓ ^ n ∣ B` at
  -- a time; the measure drops because `ℓ ^ m, ℓ ^ n ≥ 2` and `(A, B) ≠ (0, 0)`.
  generalize hN : A.natAbs + B.natAbs = N
  induction N using Nat.strong_induction_on generalizing A B with
  | _ N ih =>
  by_cases hmin : ∀ ℓ : ℕ, ℓ.Prime → ¬ ((ℓ : ℤ) ^ m ∣ A ∧ (ℓ : ℤ) ^ n ∣ B)
  · exact ⟨1, A, B, one_ne_zero, by ring, by ring, hmin⟩
  push Not at hmin
  obtain ⟨ℓ, hℓ, ⟨A₁, rfl⟩, ⟨B₁, rfl⟩⟩ := hmin
  have hne : A₁ ≠ 0 ∨ B₁ ≠ 0 := h.imp right_ne_zero_of_mul right_ne_zero_of_mul
  have hlt : A₁.natAbs + B₁.natAbs < N := by
    subst hN
    have hm' := Nat.mul_le_mul_right A₁.natAbs (hℓ.two_le.trans (Nat.le_self_pow hm ℓ))
    have hn' := Nat.mul_le_mul_right B₁.natAbs (hℓ.two_le.trans (Nat.le_self_pow hn ℓ))
    have hpos : 0 < A₁.natAbs + B₁.natAbs := by
      rcases hne with h | h
      · exact Nat.add_pos_left (Int.natAbs_pos.mpr h) _
      · exact Nat.add_pos_right _ (Int.natAbs_pos.mpr h)
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    omega
  obtain ⟨d, A', B', hd, hA', hB', hmin'⟩ := ih _ hlt A₁ B₁ hne rfl
  exact ⟨ℓ * d, A', B', mul_ne_zero (Nat.cast_ne_zero.mpr hℓ.ne_zero) hd,
    by rw [hA']; ring, by rw [hB']; ring, hmin'⟩

end Int

end
