/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import TauCeti.RingTheory.Localization.Away.Units

/-!
# Units of multivariate polynomials and their away localizations

Over a commutative ring, a polynomial is a unit exactly when its constant coefficient is a unit and
its other coefficients are nilpotent. Mapping the coefficients along an injective local
homomorphism `f : R →+* S` of commutative rings therefore reflects units: if `map f p` is a unit of
`S[X_σ]`, then, since `f` is injective and reflects units, the same coefficient conditions hold
for `p`. In other words `map f` is a local homomorphism, so irreducibility of `map f p` implies
irreducibility of `p` (`Irreducible.of_map`). Every ring homomorphism from a field `k` into a
nontrivial commutative ring is injective and local, so this holds for it with no hypothesis. This
is how absolute irreducibility, over an algebraic closure, gives irreducibility over every
intermediate field.

Over a commutative semiring `R` without zero divisors, every unit of `MvPolynomial σ R` is a scalar
unit `C c` (`isUnit_iff_eq_C_of_noZeroDivisors`, without needing subtraction on `R`). When `R` has
cancellative addition and multiplication, so does `MvPolynomial σ R`, so localizing away from a
prime polynomial `f` (or a polynomial associated to a finite product `∏ i ∈ t, p i` of primes)
yields units of the form `c * f ^ n` (`c ∈ Rˣ`, `n : ℤ`) or `c * ∏ i ∈ t, v i ^ m i`.

## Main results

* `MvPolynomial.isLocalHom_map_of_injective`: `map f` reflects units for an injective local
  homomorphism `f` of commutative rings.
* `MvPolynomial.isLocalHom_map`: its specialization to a ring homomorphism `f` out of a field into a
  nontrivial commutative ring. It is an instance, so `Irreducible.of_map` applies to `map f`
  directly.
* `MvPolynomial.isUnit_iff_totalDegree_eq_zero`: a nonzero polynomial over a field is a unit
  exactly when its total degree is zero.
* `MvPolynomial.isUnit_iff_eq_C_of_noZeroDivisors`: over a commutative semiring without zero
  divisors, a polynomial is a unit if and only if it is `C c` for a unit `c` of `R`.
* `MvPolynomial.isUnit_away_iff_of_prime` and
  `MvPolynomial.exists_unit_mul_prod_zpow_eq_of_associated_prod_prime`: over a commutative semiring
  `R` with cancellative addition and multiplication, the units of a localization of
  `MvPolynomial σ R` away from a prime polynomial or a product of prime polynomials.
-/

public section

namespace MvPolynomial

section Field

variable {σ k L : Type*} [Field k] [CommRing L]

/-- Over a field, a nonzero polynomial is a unit exactly when its total degree is zero, that is,
when it is a nonzero constant. -/
theorem isUnit_iff_totalDegree_eq_zero {p : MvPolynomial σ k} (hp : p ≠ 0) :
    IsUnit p ↔ p.totalDegree = 0 := by
  rw [isUnit_iff_totalDegree_of_isReduced, isUnit_iff_ne_zero, and_iff_right_iff_imp,
    totalDegree_eq_zero_iff_eq_C]
  exact fun h h0 ↦ hp (by rw [h, h0, C_0])

/-- **Changing the coefficients along an injective local homomorphism reflects units**: if
`f : R →+* S` is an injective local homomorphism of commutative rings and `map f p` is a unit, so
is `p`. -/
theorem isLocalHom_map_of_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    [IsLocalHom f] (hf : Function.Injective f) : IsLocalHom (map (σ := σ) f) where
  map_nonunit p hp := by
    -- A polynomial is a unit exactly when its constant coefficient is a unit and its other
    -- coefficients are nilpotent. Since `f` is injective and reflects units, both conditions
    -- pull back from `map f p` to `p`.
    simp only [isUnit_iff, coeff_map] at hp
    exact isUnit_iff.mpr ⟨isUnit_of_map_unit f _ hp.1,
      fun i hi ↦ (IsNilpotent.map_iff hf).mp (hp.2 i hi)⟩

/-- **Changing the coefficients along a ring homomorphism from a field into a nontrivial
commutative ring reflects units**: if `map f p` is a unit, so is `p`. Hence `Irreducible.of_map`
applies to `map f`. -/
instance isLocalHom_map [Nontrivial L] (f : k →+* L) : IsLocalHom (map (σ := σ) f) :=
  isLocalHom_map_of_injective f f.injective

end Field

section NoZeroDivisors

variable {R σ : Type*} [CommSemiring R] [NoZeroDivisors R]

/-- Over a commutative semiring `R` without zero divisors, a polynomial `p : MvPolynomial σ R` is a
unit if and only if `p = C c` for a unit `c` of `R`. -/
theorem isUnit_iff_eq_C_of_noZeroDivisors {p : MvPolynomial σ R} :
    IsUnit p ↔ ∃ c : R, IsUnit c ∧ p = C c := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact ⟨fun _ ↦ ⟨0, isUnit_of_subsingleton 0, Subsingleton.elim _ _⟩,
      fun _ ↦ isUnit_of_subsingleton p⟩
  simp_rw [isUnit_iff_dvd_one]
  simpa using dvd_C_iff_exists (f := p) (one_ne_zero' R)

end NoZeroDivisors

section Away

variable {R S σ : Type*} [CommSemiring R] [IsCancelAdd R] [IsCancelMulZero R] [CommSemiring S]
  [Algebra R S] [Algebra (MvPolynomial σ R) S] [IsScalarTower R (MvPolynomial σ R) S]

/-- **Units of a localized polynomial ring away from a prime.** Over a commutative semiring `R` with
cancellative addition and multiplication, an element of a localization `S` of `MvPolynomial σ R`
away from a prime polynomial `f` is a unit if and only if it has the form
`algebraMap R S c * selfZPow f S n` for a scalar unit `c` of `R` and `n : ℤ`. -/
theorem isUnit_away_iff_of_prime {f : MvPolynomial σ R} [IsLocalization.Away f S] (hf : Prime f)
    {s : S} :
    IsUnit s ↔ ∃ c : R, IsUnit c ∧ ∃ n : ℤ, algebraMap R S c * selfZPow f S n = s := by
  rw [IsLocalization.Away.isUnit_iff_of_prime hf]
  constructor
  · rintro ⟨p, hp, n, rfl⟩
    obtain ⟨c, hc, rfl⟩ := isUnit_iff_eq_C_of_noZeroDivisors.mp hp
    refine ⟨c, hc, n, ?_⟩
    rw [← algebraMap_eq, ← IsScalarTower.algebraMap_apply R (MvPolynomial σ R) S]
  · rintro ⟨c, hc, n, rfl⟩
    refine ⟨C c, hc.map C, n, ?_⟩
    rw [← algebraMap_eq, ← IsScalarTower.algebraMap_apply R (MvPolynomial σ R) S]

/-- **Units of a localized polynomial ring away from a product of primes.** Over a commutative
semiring `R` with cancellative addition and multiplication, if `f : MvPolynomial σ R` is associated
to a finite product `∏ i ∈ t, p i` of prime polynomials and `v i : Sˣ` represents `p i` in a
localization `S` away from `f`, then every unit of `S` is a scalar unit `c : Rˣ` times
`∏ i ∈ t, v i ^ m i` (`m : ι → ℤ`). -/
theorem exists_unit_mul_prod_zpow_eq_of_associated_prod_prime {ι : Type*} {t : Finset ι}
    {p : ι → MvPolynomial σ R} {f : MvPolynomial σ R} [IsLocalization.Away f S]
    (hp : ∀ i ∈ t, Prime (p i)) (hf : Associated f (∏ i ∈ t, p i)) {v : ι → Sˣ}
    (hv : ∀ i ∈ t, (v i : S) = algebraMap (MvPolynomial σ R) S (p i)) (u : Sˣ) :
    ∃ (c : Rˣ) (m : ι → ℤ),
      Units.map (algebraMap R S : R →* S) c * ∏ i ∈ t, v i ^ m i = u := by
  obtain ⟨q, m, hqm⟩ :=
    IsLocalization.Away.exists_unit_mul_prod_zpow_eq_of_associated_prod_prime hp hf hv u
  obtain ⟨r, hr, hqr⟩ := isUnit_iff_eq_C_of_noZeroDivisors.mp q.isUnit
  refine ⟨hr.unit, m, ?_⟩
  have hmap : Units.map (algebraMap R S : R →* S) hr.unit =
      Units.map (algebraMap (MvPolynomial σ R) S : MvPolynomial σ R →* S) q := by
    ext
    rw [Units.coe_map, Units.coe_map, MonoidHom.coe_ofClass, MonoidHom.coe_ofClass,
      IsUnit.unit_spec, hqr, ← algebraMap_eq,
      ← IsScalarTower.algebraMap_apply R (MvPolynomial σ R) S]
  rw [hmap, hqm]

end Away

end MvPolynomial
