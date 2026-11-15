/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Algebra.BigOperators.Associated

/-!
# Units of localizations away from primes and products of primes

In a cancellative commutative semiring `R`, inverting a prime element `p` creates no new units in
`R` except associates of powers of `p`, and every unit of `Localization.Away p` is a unit of `R`
times an integral power of `p` (cleared of denominators as `z * p ^ n = u * p ^ i`). More
generally, inverting a finite product `∏ i ∈ s, p i` of prime elements makes an element of `R` a
unit if and only if it is associated to `∏ i ∈ s, p i ^ k i`, and every unit of the localization is
a unit of `R` times a product of powers of the `p i` divided by a power of `∏ i ∈ s, p i`.

In particular, an element of `R` not divisible by any `p i` that becomes a unit after inverting
`∏ i ∈ s, p i` is already a unit of `R`.

## Main results

* `IsLocalization.Away.algebraMap_isUnit_iff_of_prime` and
  `IsLocalization.Away.algebraMap_isUnit_iff_of_prod_prime`: an element of `R` becomes a unit after
  inverting a prime `p` (respectively `∏ i ∈ s, p i`) if and only if it is associated to `p ^ n`
  (respectively `∏ i ∈ s, p i ^ k i`).
* `IsLocalization.Away.isUnit_iff_of_prime` and `IsLocalization.Away.isUnit_iff_of_prod_prime`:
  description of all units of the localization away from a prime or a finite product of primes by
  clearing denominators.
* `Prime.isUnit_of_isUnit_away_of_not_dvd` and
  `IsLocalization.Away.isUnit_of_isUnit_away_of_prod_prime`: descending invertibility from the
  complement of a prime divisor or a finite union of prime divisors.
-/

public section

namespace IsLocalization.Away

variable {ι R S : Type*} [CommSemiring R] [IsCancelMulZero R] [CommSemiring S] [Algebra R S]

/-- In a cancellative commutative semiring, an element `a` becomes a unit after inverting a prime
`p` if and only if `a` is associated to a power of `p`. -/
theorem algebraMap_isUnit_iff_of_prime {p : R} (hp : Prime p) [IsLocalization.Away p S] {a : R} :
    IsUnit (algebraMap R S a) ↔ ∃ n : ℕ, Associated a (p ^ n) := by
  rw [algebraMap_isUnit_iff p]
  refine ⟨fun ⟨n, hn⟩ ↦ ?_, fun ⟨n, hn⟩ ↦ ⟨n, hn.dvd⟩⟩
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hp n).mp hn
  exact ⟨i, hi⟩

/-- **Units of a localization away from a prime.** In a localization of a cancellative commutative
semiring `R` away from a prime `p`, an element `z` is a unit if and only if clearing some power
`p ^ n` expresses it as a unit of `R` times a power `p ^ i`. -/
theorem isUnit_iff_of_prime {p : R} (hp : Prime p) [IsLocalization.Away p S] {z : S} :
    IsUnit z ↔ ∃ (u : Rˣ) (i n : ℕ),
      z * algebraMap R S p ^ n = algebraMap R S u * algebraMap R S p ^ i := by
  refine ⟨fun hz ↦ ?_, fun ⟨u, i, n, hz⟩ ↦ ?_⟩
  · obtain ⟨n, a, hza⟩ := surj p z
    have ha : IsUnit (algebraMap R S a) := hza ▸ hz.mul (algebraMap_pow_isUnit p n)
    obtain ⟨i, hai⟩ := (algebraMap_isUnit_iff_of_prime hp).mp ha
    obtain ⟨u, rfl⟩ := hai.symm
    refine ⟨u, i, n, hza.trans ?_⟩
    rw [mul_comm _ (u : R), map_mul, map_pow]
  · exact isUnit_of_mul_isUnit_left
      (hz ▸ (u.isUnit.map (algebraMap R S)).mul (algebraMap_pow_isUnit p i))

/-- In a cancellative commutative semiring, an element `a` becomes a unit after inverting a finite
product `∏ i ∈ s, p i` of primes if and only if `a` is associated to `∏ i ∈ s, p i ^ k i` for some
exponents `k`. -/
theorem algebraMap_isUnit_iff_of_prod_prime {s : Finset ι} {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) [IsLocalization.Away (∏ i ∈ s, p i) S] {a : R} :
    IsUnit (algebraMap R S a) ↔ ∃ k : ι → ℕ, Associated a (∏ i ∈ s, p i ^ k i) := by
  rw [algebraMap_isUnit_iff (∏ i ∈ s, p i)]
  refine ⟨fun ⟨n, hn⟩ ↦ ?_, fun ⟨k, hak⟩ ↦ ⟨s.sup k, hak.dvd.trans ?_⟩⟩
  · obtain ⟨k, -, hak⟩ := (s.dvd_pow_prod_iff_of_prime hp n).mp hn
    exact ⟨k, hak⟩
  · rw [← Finset.prod_pow]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow (p i) (Finset.le_sup hi)

/-- **Units of a localization away from a product of primes.** In a localization of a cancellative
commutative semiring `R` away from a finite product `∏ i ∈ s, p i` of primes, an element `z` is a
unit if and only if clearing a power of `∏ i ∈ s, p i` expresses it as a unit of `R` times a
product of powers of the `p i`. -/
theorem isUnit_iff_of_prod_prime {s : Finset ι} {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) [IsLocalization.Away (∏ i ∈ s, p i) S] {z : S} :
    IsUnit z ↔ ∃ (u : Rˣ) (k : ι → ℕ) (n : ℕ),
      z * algebraMap R S (∏ i ∈ s, p i) ^ n =
        algebraMap R S u * ∏ i ∈ s, algebraMap R S (p i) ^ k i := by
  refine ⟨fun hz ↦ ?_, fun ⟨u, k, n, hz⟩ ↦ ?_⟩
  · obtain ⟨n, a, hza⟩ := surj (∏ i ∈ s, p i) z
    have ha : IsUnit (algebraMap R S a) := hza ▸ hz.mul (algebraMap_pow_isUnit (∏ i ∈ s, p i) n)
    obtain ⟨k, hak⟩ := (algebraMap_isUnit_iff_of_prod_prime hp).mp ha
    obtain ⟨u, rfl⟩ := hak.symm
    refine ⟨u, k, n, hza.trans ?_⟩
    rw [mul_comm _ (u : R), map_mul, map_prod]
    simp only [map_pow]
  · have hp_unit : ∀ i ∈ s, IsUnit (algebraMap R S (p i)) := fun i hi ↦
      isUnit_of_dvd_unit (map_dvd (algebraMap R S) (Finset.dvd_prod_of_mem p hi))
        (algebraMap_isUnit (∏ j ∈ s, p j))
    have hprod : IsUnit (∏ i ∈ s, algebraMap R S (p i) ^ k i) :=
      Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one
        fun i hi ↦ (hp_unit i hi).pow (k i)
    exact isUnit_of_mul_isUnit_left (hz ▸ (u.isUnit.map (algebraMap R S)).mul hprod)

/-- Inverting a finite product `∏ i ∈ s, p i` of primes can only turn multiples of the `p i` into
new units: an element not divisible by any `p i` that becomes a unit in the localization is already
a unit of `R`. -/
theorem isUnit_of_isUnit_away_of_prod_prime {s : Finset ι} {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) [IsLocalization.Away (∏ i ∈ s, p i) S] {x : R}
    (hx : IsUnit (algebraMap R S x)) (hpx : ∀ i ∈ s, ¬p i ∣ x) : IsUnit x := by
  obtain ⟨k, hxk⟩ := (algebraMap_isUnit_iff_of_prod_prime hp).mp hx
  by_cases hk : ∀ i ∈ s, k i = 0
  · refine associated_one_iff_isUnit.mp (hxk.trans ?_)
    rw [Finset.prod_eq_one fun i hi ↦ by simp [hk i hi]]
  · push Not at hk
    obtain ⟨i, hi, hki⟩ := hk
    exact (hpx i hi ((dvd_pow_self (p i) hki).trans
      ((Finset.dvd_prod_of_mem _ hi).trans hxk.dvd'))).elim

end IsLocalization.Away

namespace Prime

variable {R S : Type*} [CommSemiring R] [IsCancelMulZero R] [CommSemiring S] [Algebra R S]
  {p x : R} [IsLocalization.Away p S]

/-- Inverting a prime element can only make its multiples into new units. -/
theorem isUnit_of_isUnit_away_of_not_dvd (hp : Prime p)
    (hx : IsUnit (algebraMap R S x)) (hpx : ¬p ∣ x) : IsUnit x := by
  obtain ⟨i, hi⟩ := (IsLocalization.Away.algebraMap_isUnit_iff_of_prime hp).mp hx
  by_cases hi0 : i = 0
  · exact associated_one_iff_isUnit.mp (by simpa [hi0] using hi)
  · exact (hpx ((dvd_pow_self p hi0).trans hi.dvd')).elim

end Prime
