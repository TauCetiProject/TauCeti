/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Order.Filter.Cofinite

/-!
# Integers pinned by their residues at all but finitely many primes

An integer divisible by every prime outside a finite set is zero, and consequently two integers
congruent modulo every prime outside a finite set are equal. "All but finitely many" is expressed
as `∀ᶠ ℓ in Filter.cofinite`. A nonzero integer has finitely many prime divisors while the
remaining primes are infinite in number, so some prime both divides it and exceeds its absolute
value.

The exceptions are what make these usable: an argument that produces congruences one prime at a
time is typically forced to omit a characteristic, and may omit it without weakening the
conclusion; `Filter.eventually_cofinite_ne p` discharges a single omitted prime `p`.
`TauCeti.Matrix.eq_quadratic_form_of_det_trace` is such an argument.

## Main results

* `Int.eq_zero_of_eventually_prime_dvd`: an integer divisible by all but finitely many primes
  is zero.
* `Int.eq_of_eventually_prime_intCast_eq`: two integers agreeing in `ZMod ℓ` for all but finitely
  many primes `ℓ` are equal.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/WeilPairing/IntegerSeparation.lean`, declarations `int_eq_zero_of_dvd_all_primes_ne`
and `int_eq_of_congr_all_primes_ne`. The source statements exclude a single prime `p`; here they
are generalized to a cofinite set of primes, the names follow Mathlib's convention of naming after
the conclusion, and the proofs are shortened.
-/

public section

namespace Int

/-- **An integer divisible by all but finitely many primes is zero.**

A nonzero integer is divisible only by primes at most its absolute value, but the primes outside
a finite set are unbounded, so one of them both divides it and exceeds it. -/
theorem eq_zero_of_eventually_prime_dvd {D : ℤ}
    (h : ∀ᶠ ℓ : ℕ in Filter.cofinite, ℓ.Prime → (ℓ : ℤ) ∣ D) : D = 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Nat.cofinite_eq_atTop ▸ h)
  obtain ⟨ℓ, hℓN, hℓ⟩ := Nat.exists_infinite_primes (max N (D.natAbs + 1))
  exact eq_zero_of_dvd_of_natAbs_lt_natAbs (hN ℓ (by omega) hℓ) (by rw [natAbs_natCast]; omega)

/-- **Two integers agreeing modulo all but finitely many primes are equal.** -/
theorem eq_of_eventually_prime_intCast_eq {A B : ℤ}
    (h : ∀ᶠ ℓ : ℕ in Filter.cofinite, ℓ.Prime → (A : ZMod ℓ) = (B : ZMod ℓ)) : A = B :=
  (sub_eq_zero.mp <| eq_zero_of_eventually_prime_dvd <| h.mono fun ℓ hℓ hp ↦
    (ZMod.intCast_eq_intCast_iff_dvd_sub A B ℓ).mp (hℓ hp)).symm

end Int
