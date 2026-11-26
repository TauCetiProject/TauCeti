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
* `TauCeti.isUnit_one_sub_natCast_pow`: `1 - p ^ e` is a unit when `e ≠ 0` and every prime `q ≠ p`
  is a unit.
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

/-- If every prime `q ≠ p` casts to a unit in a ring, then so does `1 - p ^ e` for `e ≠ 0`, since
`p ^ e - 1` is prime to `p`. -/
theorem isUnit_one_sub_natCast_pow {R : Type*} [Ring R] {p e : ℕ} (hp : 1 < p) (he : e ≠ 0)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : IsUnit (1 - (p : R) ^ e) := by
  have h1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ (by omega)
  have hp1 : p ^ e - 1 ≠ 0 := by
    have := Nat.one_lt_pow he hp
    omega
  have hu : IsUnit ((p ^ e - 1 : ℕ) : R) := by
    refine isUnit_natCast_of_forall_prime_dvd hp1 fun q hq hqd ↦ hunit q hq ?_
    rintro rfl
    have : q ∣ q ^ e - (q ^ e - 1) := Nat.dvd_sub (dvd_pow_self q he) hqd
    rw [Nat.sub_sub_self h1] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one] at hu
  simpa using hu.neg

end TauCeti
