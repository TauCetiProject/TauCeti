/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.UnitSeparation

/-!
# Cyclotomic separation at the large primes of a theta lift

In the denominator argument for a theta lift, the characters to be separated are powers of
one cyclotomic character, with exponents in a string of length at most five times the target
rank. The degree of the host field is small enough that, at large primes, the powers can
be separated by units. This is the large-prime separation in
`New.Selmer.exists_isUnit_cyclotomicChar_pow_sub_one` in
`grh/src/New/Congruences/FirstOrder/DenominatorBound.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

namespace TauCeti.OneSidedBound

/-- At `p > r^16`, the powers of the cyclotomic character with exponents below `5r` can be
separated by units at one Galois element. Here `r` is the target rank at scale `x`, and
`[E : ℚ] ≤ 2x^12` is the degree bound for the host field. -/
theorem exists_isUnit_localCyclotomicCharacter_pow_sub_one_of_large_prime
    (E : Type*) [Field E] [CharZero E] [FiniteDimensional ℚ E] {p x r : ℕ} [Fact p.Prime]
    (hr₂ : 2 ≤ r) (hr : x ^ 5 ≤ r) (hdeg : Module.finrank ℚ E ≤ 2 * x ^ 12) (hp : r ^ 16 < p) :
    ∃ g : Field.absoluteGaloisGroup E, ∀ a : ℕ, 0 < a → a < 5 * r →
      IsUnit ((localCyclotomicCharacter p E g : ℤ_[p]) ^ a - 1) := by
  have hx : 1 ≤ x := by
    by_contra! h
    obtain rfl : x = 0 := by omega
    simpa using Module.finrank_pos.not_ge hdeg
  have hdeg' : Module.finrank ℚ E ≤ 2 * r ^ 3 := hdeg.trans <| Nat.mul_le_mul_left 2 <| calc
    x ^ 12 ≤ x ^ 15 := pow_le_pow_right₀ hx (by decide)
    _ = (x ^ 5) ^ 3 := by rw [← pow_mul]
    _ ≤ r ^ 3 := Nat.pow_le_pow_left hr _
  have hr₅ : 10 < r ^ 5 := lt_of_lt_of_le (by decide : 10 < 2 ^ 5) (Nat.pow_le_pow_left hr₂ 5)
  apply exists_isUnit_localCyclotomicCharacter_pow_sub_one p E
  calc
    (5 * r - 1) * Module.finrank ℚ E ≤ (5 * r) * (2 * r ^ 3) :=
      Nat.mul_le_mul (Nat.sub_le ..) hdeg'
    _ = 10 * r ^ 4 := by ring
    _ < r ^ 5 * r ^ 4 := Nat.mul_lt_mul_of_pos_right hr₅ (by positivity)
    _ = r ^ 9 := by rw [← pow_add]
    _ ≤ r ^ 16 := pow_le_pow_right₀ (by omega) (by decide)
    _ ≤ p - 1 := Nat.le_sub_one_of_lt hp

end TauCeti.OneSidedBound
