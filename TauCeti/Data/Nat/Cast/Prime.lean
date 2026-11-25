/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Induction
public import TauCeti.Data.Nat.Cast.IsUnit

/-!
# Natural numbers whose prime divisors cast to units

A nonzero natural number casts to a unit of a semiring if and only if each of its prime factors
does. One direction holds because a divisor of an invertible natural cast is again a unit; the
other is an induction on the prime factorization.

## Main results

* `TauCeti.isUnit_natCast_of_forall_prime_dvd`, `TauCeti.isUnit_natCast_iff_forall_prime_dvd`: a
  nonzero natural number casts to a unit in a semiring if and only if all of its prime divisors do.
-/

public section

namespace TauCeti

/-- A nonzero natural number casts to a unit in a semiring whenever all of its prime divisors do. -/
theorem isUnit_natCast_of_forall_prime_dvd {R : Type*} [Semiring R] {n : ℕ} (hn : n ≠ 0)
    (hp : ∀ p : ℕ, p.Prime → p ∣ n → IsUnit (p : R)) : IsUnit (n : R) := by
  induction n using induction_on_primes with
  | zero => exact absurd rfl hn
  | one => simp
  | prime_mul p a hpp ih =>
    rw [Nat.cast_mul]
    exact (hp p hpp (dvd_mul_right p a)).mul
      (ih (right_ne_zero_of_mul hn) fun q hq hqa ↦ hp q hq (hqa.mul_left p))

/-- A nonzero natural number casts to a unit in a semiring if and only if all of its prime divisors
cast to units. -/
theorem isUnit_natCast_iff_forall_prime_dvd {R : Type*} [Semiring R] {n : ℕ} (hn : n ≠ 0) :
    IsUnit (n : R) ↔ ∀ p : ℕ, p.Prime → p ∣ n → IsUnit (p : R) :=
  ⟨fun hu _ _ hpn ↦ hu.natCast_of_dvd hpn, isUnit_natCast_of_forall_prime_dvd hn⟩

end TauCeti
