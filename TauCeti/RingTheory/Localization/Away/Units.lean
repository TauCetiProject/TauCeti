/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.RingTheory.Localization.Away.Basic
import TauCeti.Algebra.BigOperators.Associated

/-!
# Units of a localization away from primes

In a cancellative commutative semiring with zero `R`, inverting a prime element `p` makes an
element of `R` into a unit if and only if it is associated to a power of `p`
(`Prime.isUnit_algebraMap_away_iff`), so an element not divisible by `p` becomes a unit off `(p)`
only when it was already a unit (`Prime.isUnit_of_isUnit_away_of_not_dvd`), and every unit of the
localization has the form `u * p ^ m` with `u` a unit of `R` and `m : ℤ` (`Prime.isUnit_away_iff`).
More generally, inverting a finite product `f = ∏ i ∈ s, p i` of prime elements makes an element of
`R` into a unit if and only if it is associated to a product `∏ i ∈ s, p i ^ k i`
(`TauCeti.isUnit_algebraMap_away_prod_prime_iff`), without assuming unique factorization in `R`.

## Main results

* `TauCeti.isUnit_selfZPow`: every integer power `selfZPow x S m` in a localization away from `x`
  is a unit.
* `TauCeti.isUnit_algebraMap_away_prod_prime_iff`: `algebraMap R S x` is a unit away from a product
  `∏ i ∈ s, p i` of primes if and only if `x` is associated to some `∏ i ∈ s, p i ^ k i`.
* `Prime.isUnit_algebraMap_away_iff`: `algebraMap R S x` is a unit away from a prime `p` if and
  only if `x` is associated to some `p ^ n`.
* `Prime.isUnit_of_isUnit_away_of_not_dvd`: an element not divisible by a prime `p` is a unit if it
  becomes a unit away from `p`.
* `Prime.isUnit_away_iff`: the units of a localization away from a prime `p` are the products
  `algebraMap R S u * selfZPow p S m` with `u` a unit of `R` and `m : ℤ`.
-/

public section

namespace TauCeti

/-- Every integer power `selfZPow x S m` of the inverted element `x` is a unit in a localization
away from `x`. -/
@[simp]
theorem isUnit_selfZPow {R : Type*} [CommSemiring R] (x : R) (S : Type*) [CommSemiring S]
    [Algebra R S] [IsLocalization.Away x S] (m : ℤ) : IsUnit (selfZPow x S m) :=
  .of_mul_eq_one (selfZPow x S (-m)) (selfZPow_mul_neg x S m)

/-- **Units in `R` after inverting a product of primes.** In a cancellative commutative semiring
with zero, `algebraMap R S x` is a unit in a localization away from `f = ∏ i ∈ s, p i`, where each
`p i` (`i ∈ s`) is prime, if and only if `x` is associated to `∏ i ∈ s, p i ^ k i` for some
exponents `k : ι → ℕ`. -/
theorem isUnit_algebraMap_away_prod_prime_iff {ι R S : Type*} [CommSemiring R] [IsCancelMulZero R]
    [CommSemiring S] [Algebra R S] {s : Finset ι} {p : ι → R} {f : R}
    (hp : ∀ i ∈ s, Prime (p i)) (hprod : ∏ i ∈ s, p i = f) [IsLocalization.Away f S] {x : R} :
    IsUnit (algebraMap R S x) ↔ ∃ k : ι → ℕ, Associated x (∏ i ∈ s, p i ^ k i) := by
  rw [IsLocalization.Away.algebraMap_isUnit_iff (S := S) f]
  constructor
  · rintro ⟨n, hn⟩
    rw [← hprod, ← Finset.prod_pow] at hn
    obtain ⟨k, _, hk⟩ := (dvd_prod_prime_pow hp fun _ ↦ n).mp hn
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨s.sup k, hk.dvd.trans ?_⟩
    rw [← hprod, ← Finset.prod_pow]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow (p i) (Finset.le_sup hi)

end TauCeti

namespace Prime

variable {R S : Type*} [CommSemiring R] [IsCancelMulZero R] [CommSemiring S] [Algebra R S]
  {p x : R} [IsLocalization.Away p S]

/-- In a cancellative commutative semiring with zero, `algebraMap R S x` is a unit in a
localization away from a prime `p` if and only if `x` is associated to a power of `p`. -/
theorem isUnit_algebraMap_away_iff (hp : Prime p) :
    IsUnit (algebraMap R S x) ↔ ∃ n : ℕ, Associated x (p ^ n) := by
  rw [TauCeti.isUnit_algebraMap_away_prod_prime_iff (S := S) (s := ({()} : Finset Unit))
    (p := fun _ ↦ p) (by simp [hp]) (Finset.prod_singleton _ _)]
  exact ⟨fun ⟨k, hk⟩ ↦ ⟨k (), by simpa using hk⟩, fun ⟨n, hn⟩ ↦ ⟨fun _ ↦ n, by simpa using hn⟩⟩

/-- Inverting a prime element can only make its multiples into new units. -/
theorem isUnit_of_isUnit_away_of_not_dvd (hp : Prime p)
    (hx : IsUnit (algebraMap R S x)) (hpx : ¬p ∣ x) : IsUnit x := by
  obtain ⟨i, hi⟩ := (hp.isUnit_algebraMap_away_iff (S := S)).mp hx
  by_cases hi0 : i = 0
  · exact associated_one_iff_isUnit.mp (by simpa [hi0] using hi)
  · exact (hpx ((dvd_pow_self p hi0).trans hi.dvd')).elim

/-- **Units of a localization away from a prime.** In a cancellative commutative semiring with zero
`R`, an element of a localization `S` away from a prime `p` is a unit if and only if it has the form
`algebraMap R S u * selfZPow p S m` for a unit `u` of `R` and an integer `m`. -/
theorem isUnit_away_iff (hp : Prime p) {y : S} :
    IsUnit y ↔ ∃ u : R, IsUnit u ∧ ∃ m : ℤ, algebraMap R S u * selfZPow p S m = y := by
  refine ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj p y
    have hua : IsUnit (algebraMap R S a) :=
      ha ▸ hy.mul (IsLocalization.Away.algebraMap_pow_isUnit p n)
    obtain ⟨k, hk⟩ := hp.isUnit_algebraMap_away_iff.mp hua
    obtain ⟨u, rfl⟩ := hk.symm
    refine ⟨u, u.isUnit, (k : ℤ) - n,
      (IsLocalization.Away.algebraMap_pow_isUnit p n).mul_left_inj.mp ?_⟩
    calc
      algebraMap R S ↑u * selfZPow p S ((k : ℤ) - n) * algebraMap R S p ^ n
        = algebraMap R S ↑u * (selfZPow p S ((k : ℤ) - n) * selfZPow p S (n : ℤ)) := by
          rw [mul_assoc, selfZPow_natCast]
      _ = algebraMap R S (p ^ k * ↑u) := by
          rw [← selfZPow_add, sub_add_cancel, selfZPow_natCast, map_mul, map_pow, mul_comm]
      _ = y * algebraMap R S p ^ n := ha.symm
  · rintro ⟨u, hu, m, rfl⟩
    exact (hu.map _).mul (TauCeti.isUnit_selfZPow p S m)

end Prime
