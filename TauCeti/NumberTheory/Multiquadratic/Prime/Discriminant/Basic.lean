/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.RingTheory.Int.Basic

/-!
# Odd prime discriminants

For an odd prime `p`, the associated prime discriminant `p*` is

* `p` when `p ≡ 1 (mod 4)`;
* `-p` when `p ≡ 3 (mod 4)`.

It is the sign normalization of `p` that satisfies `p* ≡ 1 (mod 4)`, so `p*` is the
discriminant of the quadratic field `ℚ(√p*)`, the unique quadratic field in which `p` is the
only ramified rational prime. This file records that normalization as a small arithmetic API.
The even prime discriminants `-4`, `8`, and `-8` are treated in
`TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Even`, and the two cases are combined
in `TauCeti.NumberTheory.Multiquadratic.Prime.Discriminants`.

## Main definitions and results

* `TauCeti.Multiquadratic.oddPrimeDiscriminant`: the integer `p` if `p % 4 = 1`, and `-p`
  otherwise.
* `TauCeti.Multiquadratic.oddPrimeDiscriminant_natAbs`: its absolute value is `p`.
* `TauCeti.Multiquadratic.prime_oddPrimeDiscriminant_iff`: it is a prime integer exactly when
  `p` is a natural prime.
* `TauCeti.Multiquadratic.oddPrimeDiscriminant_dvd_iff`,
  `TauCeti.Multiquadratic.dvd_oddPrimeDiscriminant_iff`: `p*` and `p` have the same multiples
  and the same divisors in `ℤ`.
* `TauCeti.Multiquadratic.oddPrimeDiscriminant_mod_four_eq_one_iff`: it is `1 mod 4` exactly
  when `p` is odd.
* `TauCeti.Multiquadratic.oddPrimeDiscriminant_eq_neg_one_pow_pred_div_two_mul`: the standard
  formula `p* = (-1)^((p-1)/2) p`.
* `TauCeti.Multiquadratic.oddPrimeDiscriminant_eq_neg_one_pow_div_two_mul`: the equivalent
  formula `p* = (-1)^(p/2) p`.
-/

public section

namespace TauCeti.Multiquadratic

/-- The odd prime discriminant `p*`: `p` when `p % 4 = 1` and `-p` otherwise (so the value is
`-p` for every `p` with `p % 4 ≠ 1`, including even inputs). The `p ≡ 3 (mod 4)` reading of the
second case is the intended one for odd primes. The primality hypothesis is not part of the
definition so that the expression rewrites by computation; the API below supplies the
prime-specific facts. -/
@[expose] def oddPrimeDiscriminant (p : ℕ) : ℤ :=
  if p % 4 = 1 then p else -(p : ℤ)

/-- The defining `if` expression for the odd prime discriminant. -/
theorem oddPrimeDiscriminant_def (p : ℕ) :
    oddPrimeDiscriminant p = if p % 4 = 1 then (p : ℤ) else -(p : ℤ) := rfl

/-- If `p ≡ 1 (mod 4)`, its odd prime discriminant is `p`. -/
@[simp] theorem oddPrimeDiscriminant_of_mod_four_eq_one {p : ℕ} (hp : p % 4 = 1) :
    oddPrimeDiscriminant p = p := by
  simp [oddPrimeDiscriminant, hp]

/-- If `p ≠ 1 (mod 4)`, its odd prime discriminant is `-p`. For an odd prime this is the
`p ≡ 3 (mod 4)` case. -/
@[simp] theorem oddPrimeDiscriminant_of_mod_four_ne_one {p : ℕ} (hp : p % 4 ≠ 1) :
    oddPrimeDiscriminant p = -(p : ℤ) := by
  simp [oddPrimeDiscriminant, hp]

/-- If `p ≡ 3 (mod 4)`, its odd prime discriminant is `-p`. -/
theorem oddPrimeDiscriminant_of_mod_four_eq_three {p : ℕ} (hp : p % 4 = 3) :
    oddPrimeDiscriminant p = -(p : ℤ) :=
  oddPrimeDiscriminant_of_mod_four_ne_one (by omega)

/-- The absolute value of the odd prime discriminant is the underlying natural number. -/
@[simp] theorem oddPrimeDiscriminant_natAbs (p : ℕ) : (oddPrimeDiscriminant p).natAbs = p := by
  by_cases hp : p % 4 = 1 <;> simp [oddPrimeDiscriminant, hp]

/-- The odd prime discriminant is nonzero exactly when `p` is nonzero. -/
@[simp] theorem oddPrimeDiscriminant_ne_zero {p : ℕ} :
    oddPrimeDiscriminant p ≠ 0 ↔ p ≠ 0 := by
  rw [← Int.natAbs_ne_zero, oddPrimeDiscriminant_natAbs]

/-- The odd prime discriminant is a prime integer exactly when `p` is a natural prime. -/
@[simp] theorem prime_oddPrimeDiscriminant_iff {p : ℕ} :
    Prime (oddPrimeDiscriminant p) ↔ p.Prime := by
  rw [Int.prime_iff_natAbs_prime, oddPrimeDiscriminant_natAbs]

/-- The odd prime discriminant is squarefree exactly when `p` is. -/
@[simp] theorem squarefree_oddPrimeDiscriminant_iff {p : ℕ} :
    Squarefree (oddPrimeDiscriminant p) ↔ Squarefree p := by
  rw [← Int.squarefree_natAbs, oddPrimeDiscriminant_natAbs]

/-- The odd prime discriminant divides an integer exactly when `p` does. -/
@[simp] theorem oddPrimeDiscriminant_dvd_iff {p : ℕ} {D : ℤ} :
    oddPrimeDiscriminant p ∣ D ↔ (p : ℤ) ∣ D := by
  by_cases hp : p % 4 = 1 <;> simp [hp]

/-- An integer divides an odd prime discriminant exactly when it divides the underlying
natural number. -/
@[simp] theorem dvd_oddPrimeDiscriminant_iff {p : ℕ} {q : ℤ} :
    q ∣ oddPrimeDiscriminant p ↔ q ∣ (p : ℤ) := by
  by_cases hp : p % 4 = 1 <;> simp [hp]

/-- The odd prime discriminant is odd exactly when `p` is. -/
@[simp] theorem odd_oddPrimeDiscriminant_iff {p : ℕ} :
    Odd (oddPrimeDiscriminant p) ↔ Odd p := by
  rw [← Int.natAbs_odd, oddPrimeDiscriminant_natAbs]

/-- The odd prime discriminant is congruent to `1` modulo `4` exactly when `p` is odd. -/
@[simp] theorem oddPrimeDiscriminant_mod_four_eq_one_iff {p : ℕ} :
    oddPrimeDiscriminant p % 4 = 1 ↔ Odd p := by
  rw [Nat.odd_iff]
  by_cases hp : p % 4 = 1 <;> simp [hp] <;> omega

/-- The odd prime discriminant is always either `p` or `-p`. -/
theorem oddPrimeDiscriminant_eq_or_eq_neg {p : ℕ} :
    oddPrimeDiscriminant p = (p : ℤ) ∨ oddPrimeDiscriminant p = -(p : ℤ) := by
  by_cases hp : p % 4 = 1 <;> simp [hp]

/-- The sign of the odd prime discriminant is controlled by `p mod 4`. -/
theorem oddPrimeDiscriminant_pos_iff {p : ℕ} :
    0 < oddPrimeDiscriminant p ↔ p % 4 = 1 := by
  by_cases hp : p % 4 = 1 <;> simp [hp]
  omega

/-- The odd prime discriminant is negative exactly in the `p ≡ 3 (mod 4)` case. -/
theorem oddPrimeDiscriminant_neg_iff {p : ℕ} (hp : Odd p) :
    oddPrimeDiscriminant p < 0 ↔ p % 4 = 3 := by
  rw [Nat.odd_iff] at hp
  by_cases h : p % 4 = 1 <;> simp [h]
  omega

/-- The odd prime discriminant in the standard notation `p* = (-1)^(p/2) p`. -/
theorem oddPrimeDiscriminant_eq_neg_one_pow_div_two_mul {p : ℕ} (hp : Odd p) :
    oddPrimeDiscriminant p = (-1 : ℤ) ^ (p / 2) * p := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hp) with hp1 | hp3
  · rw [oddPrimeDiscriminant_of_mod_four_eq_one hp1,
      ZMod.neg_one_pow_div_two_of_one_mod_four hp1]
    simp
  · rw [oddPrimeDiscriminant_of_mod_four_eq_three hp3,
      ZMod.neg_one_pow_div_two_of_three_mod_four hp3]
    simp

/-- The odd prime discriminant in the standard notation
`p* = (-1)^((p - 1)/2) p`. -/
theorem oddPrimeDiscriminant_eq_neg_one_pow_pred_div_two_mul {p : ℕ} (hp : Odd p) :
    oddPrimeDiscriminant p = (-1 : ℤ) ^ ((p - 1) / 2) * p := by
  rw [oddPrimeDiscriminant_eq_neg_one_pow_div_two_mul hp]
  congr 2
  rcases hp with ⟨k, rfl⟩
  omega

end TauCeti.Multiquadratic
