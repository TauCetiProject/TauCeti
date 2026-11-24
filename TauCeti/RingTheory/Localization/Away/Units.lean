/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.GroupTheory.MonoidLocalization.Away

/-!
# Units of a localization away from a prime or product of primes

Let `R` be a cancellative commutative semiring (`[CommSemiring R] [IsCancelMulZero R]`) and `S` a
localization of `R` away from a prime element `p`. An element of `R` becomes a unit in `S` if and
only if it divides a power of `p`, hence (by `dvd_prime_pow`) if and only if it is associated to
`p ^ n` for some `n : ℕ`. In particular, an element not divisible by `p` that becomes a unit in `S`
was already a unit in `R`, and every unit of `S` factors uniquely as `u * p ^ m` with `u : Rˣ` and
`m : ℤ`, giving a multiplicative equivalence `Rˣ × Multiplicative ℤ ≃* Sˣ`.

More generally, when `S` is a localization away from a finite product `∏ i ∈ s, p i` of primes in
`R`, every unit of `S` is a unit of `R` times integer powers of the factors `p i`, and when the
primes `p i` are pairwise non-associated this gives `Rˣ × (s → Multiplicative ℤ) ≃* Sˣ`.

The underlying multiplicative results live in `TauCeti.GroupTheory.MonoidLocalization.Away` for
`Submonoid.LocalizationMap.AwayMap`; this file specializes them to `IsLocalization.Away` via
`IsLocalization.toLocalizationMap`.

## Main definitions

* `TauCeti.Localization.awayUnitOfDvd S h`: the image of a divisor `y` of `x` as a unit of an away
  localization `S` at `x`.
* `Prime.awayUnitsMulEquiv hp S`: the unit group isomorphism `Rˣ × Multiplicative ℤ ≃* Sˣ` for a
  localization `S` of a cancellative commutative semiring `R` away from a prime `p`.
* `TauCeti.Localization.awayProdPrimesUnitsMulEquiv S s hp hs`: the unit group isomorphism
  `Rˣ × (s → Multiplicative ℤ) ≃* Sˣ` for a localization away from a product of pairwise
  non-associated primes.

## Main results

* `TauCeti.Localization.awayUnitOfDvd_one` and `TauCeti.Localization.awayUnitOfDvd_mul`:
  unit-level identities for `1` and products dividing `x`.
* `Prime.isUnit_of_isUnit_away_of_not_dvd`: an element not divisible by `p` that is a unit away
  from `p` is already a unit.
* `Prime.isUnit_algebraMap_away_iff` and `Prime.isUnit_away_iff`: characterizations of units in a
  localization away from a prime `p`.
* `Finset.isUnit_algebraMap_away_prod_primes_iff` and `Finset.isUnit_away_prod_primes_iff`:
  characterizations of units in a localization away from a product of primes.
-/

public section

namespace TauCeti.Localization

section Semiring

variable {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- Any divisor `y` of `x` maps to a unit in a localization `S` away from `x`. -/
noncomputable def awayUnitOfDvd {x y : R} (h : y ∣ x) [IsLocalization.Away x S] : Sˣ :=
  Submonoid.LocalizationMap.AwayMap.unitOfDvd
    (IsLocalization.toLocalizationMap (.powers x) S) h

@[simp]
theorem val_awayUnitOfDvd {x y : R} (h : y ∣ x) [IsLocalization.Away x S] :
    (awayUnitOfDvd S h : S) = algebraMap R S y :=
  Submonoid.LocalizationMap.AwayMap.val_unitOfDvd
    (IsLocalization.toLocalizationMap (.powers x) S) h

/-- If `x = y * z`, the inverse of `awayUnitOfDvd S h` in `S` is `algebraMap R S z * invSelf x`. -/
theorem val_inv_awayUnitOfDvd_of_eq_mul {x y z : R} (h : y ∣ x) (hx : x = y * z)
    [IsLocalization.Away x S] :
    (((awayUnitOfDvd S h)⁻¹ : Sˣ) : S) = algebraMap R S z * IsLocalization.Away.invSelf x :=
  Submonoid.LocalizationMap.AwayMap.val_inv_unitOfDvd_of_eq_mul
    (IsLocalization.toLocalizationMap (.powers x) S) h hx

@[simp]
theorem val_inv_awayUnitOfDvd_self {x : R} (h : x ∣ x) [IsLocalization.Away x S] :
    (((awayUnitOfDvd S h)⁻¹ : Sˣ) : S) = IsLocalization.Away.invSelf x :=
  Submonoid.LocalizationMap.AwayMap.val_inv_unitOfDvd_self
    (IsLocalization.toLocalizationMap (.powers x) S) h

/-- The unit associated to `1 ∣ x` is `1`. -/
@[simp]
theorem awayUnitOfDvd_one {x : R} (h : (1 : R) ∣ x) [IsLocalization.Away x S] :
    awayUnitOfDvd S h = 1 :=
  Submonoid.LocalizationMap.AwayMap.unitOfDvd_one
    (IsLocalization.toLocalizationMap (.powers x) S) h

/-- The unit associated to a product `a * b ∣ x` is the product of the units associated to `a ∣ x`
and `b ∣ x`. -/
theorem awayUnitOfDvd_mul {x a b : R} (ha : a ∣ x) (hb : b ∣ x) (hab : a * b ∣ x)
    [IsLocalization.Away x S] :
    awayUnitOfDvd S hab = awayUnitOfDvd S ha * awayUnitOfDvd S hb :=
  Submonoid.LocalizationMap.AwayMap.unitOfDvd_mul
    (IsLocalization.toLocalizationMap (.powers x) S) ha hb hab

end Semiring

end TauCeti.Localization

namespace Finset

variable {ι R S : Type*} [CommSemiring R] [IsCancelMulZero R] [CommSemiring S] [Algebra R S]

/-- In a cancellative commutative semiring `R`, the image of `x` in a localization `S` away from
`∏ i ∈ s, p i` (with each `p i` prime) is a unit if and only if `x` is associated to
`∏ i ∈ s, p i ^ m i` for some `m : ι → ℕ`. -/
theorem isUnit_algebraMap_away_prod_primes_iff (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) [IsLocalization.Away (∏ i ∈ s, p i) S] {x : R} :
    IsUnit (algebraMap R S x) ↔ ∃ m : ι → ℕ, Associated x (∏ i ∈ s, p i ^ m i) :=
  Submonoid.LocalizationMap.AwayMap.isUnit_map_prod_primes_iff s hp
    (IsLocalization.toLocalizationMap (.powers (∏ i ∈ s, p i)) S)

/-- Every element of a localization `S` of a cancellative commutative semiring `R` away from a
product `∏ i ∈ s, p i` of primes is a unit if and only if it is `u * ∏ i : s, p i ^ m i` for some
`u : Rˣ` and `m : s → ℤ`. -/
theorem isUnit_away_prod_primes_iff (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) [IsLocalization.Away (∏ i ∈ s, p i) S] {y : S} :
    IsUnit y ↔
      ∃ (u : Rˣ) (m : s → ℤ),
        algebraMap R S (u : R) *
            ((∏ i : s,
              TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p i.property) ^ m i : Sˣ) : S) =
          y :=
  Submonoid.LocalizationMap.AwayMap.isUnit_prod_primes_iff s hp
    (IsLocalization.toLocalizationMap (.powers (∏ i ∈ s, p i)) S)

end Finset

namespace TauCeti.Localization

/-- For a finite family of pairwise non-associated primes `p i` (`i ∈ s`) in a cancellative
commutative semiring `R`, the units of a localization `S` away from `∏ i ∈ s, p i` are
canonically isomorphic to `Rˣ × (s → Multiplicative ℤ)`. -/
noncomputable def awayProdPrimesUnitsMulEquiv {ι R : Type*} (S : Type*) [CommSemiring R]
    [IsCancelMulZero R] [CommSemiring S] [Algebra R S] (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ i ∈ s, p i) S] :
    Rˣ × (s → Multiplicative ℤ) ≃* Sˣ :=
  Submonoid.LocalizationMap.AwayMap.prodPrimesUnitsMulEquiv s hp hs
    (IsLocalization.toLocalizationMap (.powers (∏ i ∈ s, p i)) S)

@[simp]
theorem awayProdPrimesUnitsMulEquiv_apply {ι R : Type*} (S : Type*) [CommSemiring R]
    [IsCancelMulZero R] [CommSemiring S] [Algebra R S] (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ i ∈ s, p i) S] (u : Rˣ) (m : s → Multiplicative ℤ) :
    awayProdPrimesUnitsMulEquiv S s hp hs (u, m) =
      Units.map (algebraMap R S : R →* S) u *
        ∏ i : s, awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.property) ^ (m i).toAdd :=
  Submonoid.LocalizationMap.AwayMap.prodPrimesUnitsMulEquiv_apply s hp hs
    (IsLocalization.toLocalizationMap (.powers (∏ i ∈ s, p i)) S) u m

@[simp]
theorem awayProdPrimesUnitsMulEquiv_symm_map {ι R : Type*} (S : Type*) [CommSemiring R]
    [IsCancelMulZero R] [CommSemiring S] [Algebra R S] (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ i ∈ s, p i) S] (u : Rˣ) :
    (awayProdPrimesUnitsMulEquiv S s hp hs).symm (Units.map (algebraMap R S : R →* S) u) =
      (u, 1) :=
  Submonoid.LocalizationMap.AwayMap.prodPrimesUnitsMulEquiv_symm_map s hp hs
    (IsLocalization.toLocalizationMap (.powers (∏ i ∈ s, p i)) S) u

@[simp]
theorem awayProdPrimesUnitsMulEquiv_symm_awayUnitOfDvd {ι R : Type*} (S : Type*)
    [CommSemiring R] [IsCancelMulZero R] [CommSemiring S] [Algebra R S] (s : Finset ι)
    [DecidableEq ↥s] {p : ι → R} (hp : ∀ i ∈ s, Prime (p i))
    (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ i ∈ s, p i) S] (i : s) :
    (awayProdPrimesUnitsMulEquiv S s hp hs).symm
        (awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.property)) =
      (1, Pi.mulSingle i (Multiplicative.ofAdd (1 : ℤ))) :=
  Submonoid.LocalizationMap.AwayMap.prodPrimesUnitsMulEquiv_symm_unitOfDvd s hp hs
    (IsLocalization.toLocalizationMap (.powers (∏ i ∈ s, p i)) S) i

end TauCeti.Localization

namespace Prime

variable {R S : Type*} [CommSemiring R] [IsCancelMulZero R] [CommSemiring S] [Algebra R S]
  {p x : R} [IsLocalization.Away p S]

/-- In a cancellative commutative semiring, the image of `x` in a localization away from a prime
`p` is a unit if and only if `x` is associated to `p ^ n` for some `n : ℕ`. -/
theorem isUnit_algebraMap_away_iff (hp : Prime p) :
    IsUnit (algebraMap R S x) ↔ ∃ n : ℕ, Associated x (p ^ n) :=
  hp.isUnit_map_awayMap_iff (IsLocalization.toLocalizationMap (.powers p) S)

/-- Inverting a prime element can only make its multiples into new units. -/
theorem isUnit_of_isUnit_away_of_not_dvd (hp : Prime p)
    (hx : IsUnit (algebraMap R S x)) (hpx : ¬p ∣ x) : IsUnit x :=
  hp.isUnit_of_isUnit_awayMap_of_not_dvd (IsLocalization.toLocalizationMap (.powers p) S) hx hpx

/-- Every element of a localization `S` of a cancellative commutative semiring `R` away from a
prime `p` is a unit if and only if it has the form `u * p ^ m` with `u : Rˣ` and `m : ℤ`. -/
theorem isUnit_away_iff (hp : Prime p) {y : S} :
    IsUnit y ↔
      ∃ (u : Rˣ) (m : ℤ),
        algebraMap R S (u : R) *
            ((TauCeti.Localization.awayUnitOfDvd S (dvd_rfl : p ∣ p) ^ m : Sˣ) : S) = y :=
  hp.isUnit_awayMap_iff (IsLocalization.toLocalizationMap (.powers p) S)

/-- In a cancellative commutative semiring `R`, the units of a localization `S` away from a prime
`p` are canonically isomorphic to `Rˣ × Multiplicative ℤ`, sending `(u, m)` to `u * p ^ m`. -/
noncomputable def awayUnitsMulEquiv (hp : Prime p) (S : Type*) [CommSemiring S] [Algebra R S]
    [IsLocalization.Away p S] : Rˣ × Multiplicative ℤ ≃* Sˣ :=
  hp.awayMapUnitsMulEquiv (IsLocalization.toLocalizationMap (.powers p) S)

@[simp]
theorem awayUnitsMulEquiv_apply (hp : Prime p) (S : Type*) [CommSemiring S] [Algebra R S]
    [IsLocalization.Away p S] (u : Rˣ) (m : Multiplicative ℤ) :
    hp.awayUnitsMulEquiv S (u, m) =
      Units.map (algebraMap R S : R →* S) u *
        TauCeti.Localization.awayUnitOfDvd S (dvd_rfl : p ∣ p) ^ m.toAdd :=
  hp.awayMapUnitsMulEquiv_apply (IsLocalization.toLocalizationMap (.powers p) S) u m

@[simp]
theorem awayUnitsMulEquiv_symm_map (hp : Prime p) (S : Type*) [CommSemiring S] [Algebra R S]
    [IsLocalization.Away p S] (u : Rˣ) :
    (hp.awayUnitsMulEquiv S).symm (Units.map (algebraMap R S : R →* S) u) = (u, 1) :=
  hp.awayMapUnitsMulEquiv_symm_map (IsLocalization.toLocalizationMap (.powers p) S) u

@[simp]
theorem awayUnitsMulEquiv_symm_awayUnitOfDvd (hp : Prime p) (S : Type*) [CommSemiring S]
    [Algebra R S] [IsLocalization.Away p S] :
    (hp.awayUnitsMulEquiv S).symm (TauCeti.Localization.awayUnitOfDvd S (dvd_rfl : p ∣ p)) =
      (1, Multiplicative.ofAdd 1) :=
  hp.awayMapUnitsMulEquiv_symm_unitOfDvd (IsLocalization.toLocalizationMap (.powers p) S)

end Prime
