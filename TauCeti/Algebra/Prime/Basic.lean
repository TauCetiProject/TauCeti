/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Prime.Defs
import Mathlib.Algebra.Prime.Lemmas

/-!
# Prime divisibility and prime-power factors

If a prime `p` does not divide `u`, then multiplying `a` by any power of `u` does not change
whether `p` divides it. For example, replacing an integer radicand `a` by `a * u ^ 2` with
`p ∤ u` keeps it in the same square class without changing whether `p` divides it.

Dually, in a cancellative commutative monoid with zero, any divisor of `p ^ n * r` splits off a
prime power `p ^ i` (`i ≤ n`) leaving a divisor of `r`.

## Main results

* `Prime.dvd_mul_pow_iff`: for a prime `p` with `p ∤ u`, `p ∣ a * u ^ n ↔ p ∣ a`.
* `Prime.dvd_pow_mul_iff`: for a prime `p` in a cancellative commutative monoid with zero, a
  divisor of `p ^ n * r` has the form `p ^ i * s` with `i ≤ n` and `s ∣ r`.
-/

public section

variable {M : Type*} [CommMonoidWithZero M]

/-- If a prime `p` does not divide `u`, then `p` divides `a * u ^ n` exactly when it
divides `a`. -/
@[simp]
theorem Prime.dvd_mul_pow_iff {p a u : M} (hp : Prime p) (hu : ¬ p ∣ u) {n : ℕ} :
    p ∣ a * u ^ n ↔ p ∣ a := by
  rw [hp.dvd_mul, or_iff_left (mt hp.dvd_of_dvd_pow hu)]

/-- For a prime `p` in a cancellative commutative monoid with zero, an element divides `p ^ n * r`
if and only if it is `p ^ i * s` for some `i ≤ n` and some divisor `s` of `r`. -/
theorem Prime.dvd_pow_mul_iff [IsCancelMulZero M] {p q r : M} (hp : Prime p) (n : ℕ) :
    q ∣ p ^ n * r ↔ ∃ i ≤ n, ∃ s, s ∣ r ∧ q = p ^ i * s := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
    refine ⟨fun h ↦ ?_, fun ⟨i, hi, s, hs, hq⟩ ↦ hq ▸ mul_dvd_mul (pow_dvd_pow p hi) hs⟩
    rw [pow_succ', mul_assoc] at h
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with ⟨q', rfl⟩ | hno
    · rw [mul_dvd_mul_iff_left hp.ne_zero, ih] at h
      obtain ⟨i, hi, s, hs, rfl⟩ := h
      exact ⟨i + 1, Nat.succ_le_succ hi, s, hs, by rw [pow_succ', mul_assoc]⟩
    · obtain ⟨i, hi, s, hs, hq⟩ := ih.mp hno
      exact ⟨i, Nat.le_succ_of_le hi, s, hs, hq⟩
