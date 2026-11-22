/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Units
public import TauCeti.RingTheory.Localization.Away.Units
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Units of localizations of multivariate polynomial rings away from primes

Let `R` be an additively and multiplicatively cancellative commutative semiring (`[CommSemiring R]
[IsCancelAdd R] [IsCancelMulZero R]`, in particular any domain, so `MvPolynomial σ R` is
cancellative and reduced). Combining `TauCeti.MvPolynomial.unitsMulEquiv`
(`Rˣ ≃* (MvPolynomial σ R)ˣ`) with `Prime.awayUnitsMulEquiv` and
`TauCeti.Localization.awayProdPrimesUnitsMulEquiv` identifies the unit group of a localization `S`
of `MvPolynomial σ R` away from a prime polynomial `f` with `Rˣ × Multiplicative ℤ`, and away from a
product `∏ j ∈ s, p j` of pairwise non-associated prime polynomials with
`Rˣ × (s → Multiplicative ℤ)`.

## Main definitions

* `TauCeti.MvPolynomial.awayPrimeUnitsMulEquiv`: the unit group equivalence
  `Rˣ × Multiplicative ℤ ≃* Sˣ` for a localization `S` of `MvPolynomial σ R` away from a prime `f`.
* `TauCeti.MvPolynomial.awayProdPrimesUnitsMulEquiv`: the unit group equivalence
  `Rˣ × (s → Multiplicative ℤ) ≃* Sˣ` for a localization away from a product of pairwise
  non-associated primes in `MvPolynomial σ R`.

## Main results

* `Prime.isUnit_away_mvPolynomial_iff` and `Finset.isUnit_away_prod_mvPolynomial_primes_iff`:
  characterizations of units in a localization of `MvPolynomial σ R` away from a prime or finite
  product of primes.
-/

public section

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial TauCeti.Localization

variable {σ R : Type*} [CommSemiring R] [IsCancelAdd R] [IsCancelMulZero R]

/-- Over an additively and multiplicatively cancellative commutative semiring `R`, the units of a
localization `S` of `MvPolynomial σ R` away from a prime polynomial `f` are canonically
`Rˣ × Multiplicative ℤ`, sending `(c, m)` to `C c * f ^ m`. -/
noncomputable def awayPrimeUnitsMulEquiv (S : Type*) [CommSemiring S]
    [Algebra (_root_.MvPolynomial σ R) S] {f : _root_.MvPolynomial σ R} (hprime : Prime f)
    [IsLocalization.Away f S] :
    Rˣ × Multiplicative ℤ ≃* Sˣ :=
  ((unitsMulEquiv σ R).prodCongr (MulEquiv.refl (Multiplicative ℤ))).trans
    (hprime.awayUnitsMulEquiv S)

@[simp]
theorem awayPrimeUnitsMulEquiv_apply (S : Type*) [CommSemiring S]
    [Algebra (_root_.MvPolynomial σ R) S] {f : _root_.MvPolynomial σ R} (hprime : Prime f)
    [IsLocalization.Away f S] (c : Rˣ) (m : Multiplicative ℤ) :
    awayPrimeUnitsMulEquiv S hprime (c, m) =
      Units.map ((algebraMap (_root_.MvPolynomial σ R) S).comp C : R →* S) c *
        awayUnit S f ^ m.toAdd := by
  ext
  simp [awayPrimeUnitsMulEquiv, MulEquiv.prodCongr]

@[simp]
theorem awayPrimeUnitsMulEquiv_symm_map (S : Type*) [CommSemiring S]
    [Algebra (_root_.MvPolynomial σ R) S] {f : _root_.MvPolynomial σ R} (hprime : Prime f)
    [IsLocalization.Away f S] (c : Rˣ) :
    (awayPrimeUnitsMulEquiv S hprime).symm
        (Units.map ((algebraMap (_root_.MvPolynomial σ R) S).comp C : R →* S) c) =
      (c, 1) := by
  rw [MulEquiv.symm_apply_eq]
  simp

@[simp]
theorem awayPrimeUnitsMulEquiv_symm_awayUnit (S : Type*) [CommSemiring S]
    [Algebra (_root_.MvPolynomial σ R) S] {f : _root_.MvPolynomial σ R} (hprime : Prime f)
    [IsLocalization.Away f S] :
    (awayPrimeUnitsMulEquiv S hprime).symm (awayUnit S f) = (1, Multiplicative.ofAdd 1) := by
  rw [MulEquiv.symm_apply_eq]
  simp

/-- Over an additively and multiplicatively cancellative commutative semiring `R`, the units of a
localization `S` of `MvPolynomial σ R` away from a product `∏ j ∈ s, p j` of pairwise non-associated
prime polynomials are canonically `Rˣ × (s → Multiplicative ℤ)`. -/
noncomputable def awayProdPrimesUnitsMulEquiv {J : Type*} (S : Type*) [CommSemiring S]
    [Algebra (_root_.MvPolynomial σ R) S] (s : Finset J) {p : J → _root_.MvPolynomial σ R}
    (hp : ∀ j ∈ s, Prime (p j))
    (hs : (s : Set J).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ j ∈ s, p j) S] :
    Rˣ × (s → Multiplicative ℤ) ≃* Sˣ :=
  ((unitsMulEquiv σ R).prodCongr
    (MulEquiv.refl (s → Multiplicative ℤ))).trans
    (TauCeti.Localization.awayProdPrimesUnitsMulEquiv S s hp hs)

@[simp]
theorem awayProdPrimesUnitsMulEquiv_apply {J : Type*} (S : Type*) [CommSemiring S]
    [Algebra (_root_.MvPolynomial σ R) S] (s : Finset J) {p : J → _root_.MvPolynomial σ R}
    (hp : ∀ j ∈ s, Prime (p j))
    (hs : (s : Set J).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ j ∈ s, p j) S] (c : Rˣ) (m : s → Multiplicative ℤ) :
    awayProdPrimesUnitsMulEquiv S s hp hs (c, m) =
      Units.map ((algebraMap (_root_.MvPolynomial σ R) S).comp C : R →* S) c *
        ∏ j : s, awayUnitOfDvd S (Finset.dvd_prod_of_mem p j.property) ^ (m j).toAdd := by
  ext
  simp [awayProdPrimesUnitsMulEquiv, MulEquiv.prodCongr]

@[simp]
theorem awayProdPrimesUnitsMulEquiv_symm_map {J : Type*} (S : Type*) [CommSemiring S]
    [Algebra (_root_.MvPolynomial σ R) S] (s : Finset J) {p : J → _root_.MvPolynomial σ R}
    (hp : ∀ j ∈ s, Prime (p j))
    (hs : (s : Set J).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ j ∈ s, p j) S] (c : Rˣ) :
    (awayProdPrimesUnitsMulEquiv S s hp hs).symm
        (Units.map ((algebraMap (_root_.MvPolynomial σ R) S).comp C : R →* S) c) =
      (c, 1) := by
  rw [MulEquiv.symm_apply_eq]
  simp

@[simp]
theorem awayProdPrimesUnitsMulEquiv_symm_awayUnitOfDvd {J : Type*} [DecidableEq J] (S : Type*)
    [CommSemiring S] [Algebra (_root_.MvPolynomial σ R) S] (s : Finset J)
    {p : J → _root_.MvPolynomial σ R} (hp : ∀ j ∈ s, Prime (p j))
    (hs : (s : Set J).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ j ∈ s, p j) S] (j : s) :
    (awayProdPrimesUnitsMulEquiv S s hp hs).symm
        (awayUnitOfDvd S (Finset.dvd_prod_of_mem p j.property)) =
      (1, Pi.mulSingle j (Multiplicative.ofAdd 1)) := by
  rw [awayProdPrimesUnitsMulEquiv, MulEquiv.symm_trans_apply,
    TauCeti.Localization.awayProdPrimesUnitsMulEquiv_symm_awayUnitOfDvd]
  simp [MulEquiv.prodCongr]

end TauCeti.MvPolynomial

namespace Prime

open MvPolynomial

variable {σ R : Type*} [CommSemiring R] [IsCancelAdd R] [IsCancelMulZero R]

/-- Over an additively and multiplicatively cancellative commutative semiring `R`, every unit of a
localization `S` of `MvPolynomial σ R` away from a prime `f` has the form `C c * f ^ m` with
`c : Rˣ` and `m : ℤ`. -/
theorem isUnit_away_mvPolynomial_iff {S : Type*} [CommSemiring S]
    [Algebra (MvPolynomial σ R) S] {f : MvPolynomial σ R} (hprime : Prime f)
    [IsLocalization.Away f S] {y : S} :
    IsUnit y ↔
      ∃ (c : Rˣ) (m : ℤ),
        algebraMap (MvPolynomial σ R) S (C (c : R)) *
            ((TauCeti.Localization.awayUnit S f ^ m : Sˣ) : S) = y := by
  rw [hprime.isUnit_away_iff (S := S),
    ← (TauCeti.MvPolynomial.unitsMulEquiv σ R).toEquiv.exists_congr_right]
  simp

end Prime

namespace Finset

open MvPolynomial

variable {σ R : Type*} [CommSemiring R] [IsCancelAdd R] [IsCancelMulZero R]

/-- Over an additively and multiplicatively cancellative commutative semiring `R`, every unit of a
localization `S` of `MvPolynomial σ R` away from a product `∏ j ∈ s, p j` of primes has the form
`C c * ∏ j : s, p j ^ m j` with `c : Rˣ` and `m : s → ℤ`. -/
theorem isUnit_away_prod_mvPolynomial_primes_iff {J : Type*} {S : Type*} [CommSemiring S]
    [Algebra (MvPolynomial σ R) S] (s : Finset J) {p : J → MvPolynomial σ R}
    (hp : ∀ j ∈ s, Prime (p j)) [IsLocalization.Away (∏ j ∈ s, p j) S] {y : S} :
    IsUnit y ↔
      ∃ (c : Rˣ) (m : s → ℤ),
        algebraMap (MvPolynomial σ R) S (C (c : R)) *
            ((∏ j : s,
              TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p j.property) ^ m j : Sˣ) : S) =
          y := by
  rw [s.isUnit_away_prod_primes_iff (S := S) hp,
    ← (TauCeti.MvPolynomial.unitsMulEquiv σ R).toEquiv.exists_congr_right]
  simp

end Finset
