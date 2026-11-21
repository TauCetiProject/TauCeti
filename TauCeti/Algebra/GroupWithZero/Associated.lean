/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Divisors of multiples of a prime power

In a cancellative commutative monoid with zero, Mathlib's `dvd_prime_pow` characterizes the
divisors of a power `p ^ n` of a prime element `p`: every divisor of `p ^ n` is associated to
`p ^ i` for some `i ≤ n`. This file extends that splitting to products `p ^ n * a`: every divisor
of `p ^ n * a` is associated to `p ^ i * y` for some `i ≤ n` and `y ∣ a`.

## Main results

* `Prime.exists_associated_pow_mul_of_dvd_pow_mul`: if `x ∣ p ^ n * a` for a prime `p`, then `x` is
  associated to `p ^ i * y` for some `i ≤ n` and `y ∣ a`.
-/

public section

assert_not_exists Field

namespace Prime

variable {M₀ : Type*} [CommMonoidWithZero M₀] [IsCancelMulZero M₀]

/-- In a cancellative commutative monoid with zero, a divisor of `p ^ n * a` with `p` prime splits
up to association into a power `p ^ i` (`i ≤ n`) and a divisor of `a`. -/
theorem exists_associated_pow_mul_of_dvd_pow_mul {p : M₀} (hp : Prime p) {n : ℕ} {a x : M₀}
    (hx : x ∣ p ^ n * a) : ∃ i ≤ n, ∃ y, y ∣ a ∧ Associated x (p ^ i * y) := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero, one_mul] at hx
    exact ⟨0, le_rfl, x, hx, by simp⟩
  | succ n ih =>
    rw [pow_succ', mul_assoc] at hx
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul hx with ⟨z, rfl⟩ | hx'
    · rw [mul_dvd_mul_iff_left hp.ne_zero] at hx
      obtain ⟨i, hi, y, hy, hz⟩ := ih hx
      refine ⟨i + 1, Nat.succ_le_succ hi, y, hy, (hz.mul_left p).trans ?_⟩
      rw [pow_succ', mul_assoc]
    · obtain ⟨i, hi, y, hy, hxy⟩ := ih hx'
      exact ⟨i, Nat.le_succ_of_le hi, y, hy, hxy⟩

end Prime
