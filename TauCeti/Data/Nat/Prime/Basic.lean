/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Defs

/-!
# Prime natural numbers: the `Fact` instance on the subtype, and the primes prime to `6`

Mathlib's `Nat.Primes` is the subtype of prime natural numbers. Much of the prime-indexed API
(`ZMod p` as a field, the `p`-adic integers `ℤ_[p]`, Sylow theory) takes its prime as a natural
number `p : ℕ` together with an instance `[Fact p.Prime]`, so a family indexed by `Nat.Primes`, such
as `∀ p : Nat.Primes, ℤ_[p]`, can only be written once the primality of `(p : ℕ)` is available to
instance search. Mathlib supplies it only as a local instance
(`Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean`); this module makes it global.

Arguments that treat the primes `2` and `3` separately, as for Weierstrass equations, need the
complementary fact that every other prime, that is, every prime `p ≥ 5`, does not divide `6`.

## Main declarations

* `Nat.Primes.instFactPrime`: for `p : Nat.Primes`, the instance `Fact (p : ℕ).Prime`.
* `Nat.Prime.not_dvd_six_of_five_le`: a prime `p ≥ 5` does not divide `6`.
-/

public section

/-- A prime, as an element of the subtype `Nat.Primes`, is prime: the `Fact` instance under which
the prime-indexed API, for instance the `p`-adic integers `ℤ_[p]`, can be used for `p : Nat.Primes`.
-/
instance Nat.Primes.instFactPrime (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- **A prime at least `5` does not divide `6`**: the primes dividing `6` are `2` and `3`. -/
theorem Nat.Prime.not_dvd_six_of_five_le {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ¬ p ∣ 6 :=
  fun h => by
    have := Nat.le_of_dvd (by decide) h
    obtain rfl | rfl : p = 5 ∨ p = 6 := by omega
    · omega
    · exact absurd hp (by decide)
