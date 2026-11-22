/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.RingTheory.Localization.Away.Basic
import TauCeti.GroupTheory.MonoidLocalization.Away

/-!
# Units of localizations away from primes and products of primes

In a commutative semiring, the units of the localization away from a regular prime element `p`
are precisely the products `u * p ^ k` with `u ∈ Rˣ` and `k ∈ ℤ`. More generally, when `f` is
regular and associated to a finite product `∏ i ∈ s, p i` of primes (not necessarily distinct), an
element `x` of `Localization.Away f` is a unit if and only if clearing a power `f ^ n` yields
`u * ∏ i ∈ s, p i ^ k i` for some unit `u ∈ Rˣ` and exponents `k : ι → ℕ`.

In particular, for a regular prime `p`, an element not divisible by `p` is already a unit if it
becomes a unit after inverting `p`, allowing invertibility off a regular prime divisor to descend
to the original ring.

## Main results

* `Prime.isUnit_of_isUnit_away_of_not_dvd`: inverting a regular prime only turns its multiples into
  new units.
* `IsLocalization.Away.isUnit_iff_exists_mul_pow_eq_finsetProd`: unit criterion in a localization
  away from a regular element associated to a finite product of primes.
* `IsLocalization.Away.exists_unit_mul_zpow_of_prime` and
  `IsLocalization.Away.isUnit_iff_exists_unit_mul_zpow_of_prime`: the units of a localization away
  from a regular prime `p` are the `u * p ^ k` with `u ∈ Rˣ` and `k ∈ ℤ`.
-/

public section

namespace Prime

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {p x : R} [IsLocalization.Away p S]

/-- Inverting a regular prime element can only make its multiples into new units. -/
theorem isUnit_of_isUnit_away_of_not_dvd (hp : Prime p) (hreg : IsLeftRegular p)
    (hx : IsUnit (algebraMap R S x)) (hpx : ¬p ∣ x) : IsUnit x :=
  hp.isUnit_of_isUnit_awayMap_of_not_dvd hreg
    (IsLocalization.toLocalizationMap (Submonoid.powers p) S) hx hpx

end Prime

namespace IsLocalization.Away

variable {ι R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- In a localization away from a regular element `f` associated to a finite product `∏ i ∈ s, p i`
of primes, an element `x` is a unit if and only if multiplying by some power `f ^ n` produces
`u * ∏ i ∈ s, p i ^ k i` for a unit `u ∈ Rˣ` and exponents `k : ι → ℕ`. -/
theorem isUnit_iff_exists_mul_pow_eq_finsetProd (f : R) [IsLocalization.Away f S]
    {s : Finset ι} {p : ι → R} (hp : ∀ i ∈ s, Prime (p i))
    (hf : Associated f (∏ i ∈ s, p i)) (hreg : IsLeftRegular f) {x : S} :
    IsUnit x ↔ ∃ (u : Rˣ) (k : ι → ℕ) (n : ℕ),
      x * algebraMap R S (f ^ n) = algebraMap R S (u * ∏ i ∈ s, p i ^ k i) :=
  Submonoid.LocalizationMap.AwayMap.isUnit_iff_exists_mul_pow_eq_finsetProd
    (IsLocalization.toLocalizationMap (Submonoid.powers f) S) hp hf hreg

/-- Every unit of a localization away from a regular prime element `p` is the image of a unit of
`R` multiplied by an integer power of `p`. -/
theorem exists_unit_mul_zpow_of_prime (p : R) [IsLocalization.Away p S] (hp : Prime p)
    (hreg : IsLeftRegular p) (x : Sˣ) :
    ∃ (u : Rˣ) (k : ℤ),
      x = Units.map (algebraMap R S).toMonoidHom u *
        (algebraMap_isUnit (S := S) p).unit ^ k :=
  Submonoid.LocalizationMap.AwayMap.exists_unit_mul_zpow_of_prime
    (IsLocalization.toLocalizationMap (Submonoid.powers p) S) hp hreg x

/-- An element of a localization away from a regular prime `p` is a unit if and only if it is the
image of a unit of `R` multiplied by an integer power of `p`. -/
theorem isUnit_iff_exists_unit_mul_zpow_of_prime (p : R) [IsLocalization.Away p S] (hp : Prime p)
    (hreg : IsLeftRegular p) {x : S} :
    IsUnit x ↔ ∃ (u : Rˣ) (k : ℤ),
      x = algebraMap R S u * ((algebraMap_isUnit (S := S) p).unit ^ k : Sˣ) :=
  Submonoid.LocalizationMap.AwayMap.isUnit_iff_exists_unit_mul_zpow_of_prime
    (IsLocalization.toLocalizationMap (Submonoid.powers p) S) hp hreg

end IsLocalization.Away
