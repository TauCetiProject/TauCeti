/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Data.Nat.Cast.Commute
public import Mathlib.Data.Nat.Factorization.Induction

/-!
# Natural numbers casting to units in a semiring

Because natural-number casts commute with every element of a semiring, any divisor of an invertible
natural cast is again a unit, and a nonzero natural number casts to a unit if and only if each of
its prime factors does.

## Main results

* `IsUnit.neZero_natCast`: a natural number invertible in a nontrivial semiring is nonzero.
* `IsUnit.natCast_of_dvd`: a divisor of a natural number casting to a unit also casts to a unit.
* `TauCeti.isUnit_natCast_of_forall_prime_dvd`, `TauCeti.isUnit_natCast_iff_forall_prime_dvd`: a
  nonzero natural number casts to a unit in a semiring if and only if all of its prime divisors do.
-/

public section

/-- A natural number invertible in a nontrivial semiring is nonzero as a natural number. -/
theorem IsUnit.neZero_natCast {R : Type*} [Semiring R] [Nontrivial R] {m : ℕ}
    (hm : IsUnit (m : R)) : NeZero m :=
  ⟨fun h ↦ hm.ne_zero (by rw [h, Nat.cast_zero])⟩

/-- A divisor of a natural number casting to a unit in a semiring also casts to a unit. -/
theorem IsUnit.natCast_of_dvd {R : Type*} [Semiring R] {m n : ℕ}
    (hn : IsUnit (n : R)) (hmn : m ∣ n) : IsUnit (m : R) := by
  obtain ⟨k, rfl⟩ := hmn
  rw [Nat.cast_mul, (Nat.cast_commute m (k : R)).isUnit_mul_iff] at hn
  exact hn.1

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
