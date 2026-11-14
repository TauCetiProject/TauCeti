/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Units of multivariate polynomial rings

Over a commutative ring, a polynomial is a unit exactly when its constant coefficient is a unit and
its other coefficients are nilpotent (`MvPolynomial.isUnit_iff`). Over a reduced commutative ring,
or over any commutative semiring without zero divisors, every unit is therefore a constant unit
`C r`, giving a canonical multiplicative equivalence `Rˣ ≃* (MvPolynomial σ R)ˣ` via `C` and
`constantCoeff`.

Mapping the coefficients along an injective local homomorphism `f : R →+* S` of commutative rings
also reflects units: if `map f p` is a unit of `S[X_σ]`, then, since `f` is injective and reflects
units, the same coefficient conditions hold for `p`. In other words `map f` is a local
homomorphism, so irreducibility of `map f p` implies irreducibility of `p` (`Irreducible.of_map`).
Every ring homomorphism from a field `k` into a nontrivial commutative ring is injective and local,
so this holds for it with no hypothesis. This is how absolute irreducibility, over an algebraic
closure, gives irreducibility over every intermediate field.

## Main definitions

* `MvPolynomial.unitsMulEquiv`: the unit group equivalence `Rˣ ≃* (MvPolynomial σ R)ˣ` over a
  reduced commutative ring `R`.
* `MvPolynomial.unitsMulEquivOfNoZeroDivisors`: the unit group equivalence
  `Rˣ ≃* (MvPolynomial σ R)ˣ` over a commutative semiring `R` without zero divisors.

## Main results

* `MvPolynomial.isUnit_iff_eq_C_of_noZeroDivisors`: over a commutative semiring without zero
  divisors, a multivariate polynomial is a unit if and only if it is `C r` for a unit `r`.
* `MvPolynomial.isLocalHom_map_of_injective`: `map f` reflects units for an injective local
  homomorphism `f` of commutative rings.
* `MvPolynomial.isLocalHom_map`: its specialization to a ring homomorphism `f` out of a field into a
  nontrivial commutative ring. It is an instance, so `Irreducible.of_map` applies to `map f`
  directly.
* `MvPolynomial.isUnit_iff_totalDegree_eq_zero`: a nonzero polynomial over a field is a unit
  exactly when its total degree is zero.
-/

public section

namespace MvPolynomial

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

/-- Over a commutative semiring without zero divisors, a multivariate polynomial is a unit if and
only if it is `C r` for a unit `r` of the coefficient semiring. -/
theorem isUnit_iff_eq_C_of_noZeroDivisors {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    {p : MvPolynomial σ R} : IsUnit p ↔ ∃ r, IsUnit r ∧ p = C r := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton (MvPolynomial σ R) :=
      ⟨fun f g ↦ MvPolynomial.ext f g fun _ ↦ Subsingleton.elim _ _⟩
    exact ⟨fun _ ↦ ⟨0, isUnit_of_subsingleton 0, Subsingleton.elim _ _⟩,
      fun _ ↦ isUnit_of_subsingleton p⟩
  · rw [isUnit_iff_dvd_one, ← map_one C, dvd_C_iff_exists one_ne_zero]
    simp_rw [isUnit_iff_dvd_one]

/-- Over a commutative semiring `R` without zero divisors, `C` and `constantCoeff` identify the
units of `R` with the units of `MvPolynomial σ R`. -/
noncomputable def unitsMulEquivOfNoZeroDivisors (σ R : Type*) [CommSemiring R] [NoZeroDivisors R] :
    Rˣ ≃* (MvPolynomial σ R)ˣ where
  toFun := Units.map (C : R →+* MvPolynomial σ R).toMonoidHom
  invFun := Units.map (constantCoeff : MvPolynomial σ R →+* R).toMonoidHom
  left_inv u := Units.ext (by simp)
  right_inv u := by
    obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_noZeroDivisors.mp u.isUnit
    exact Units.ext (by simp [hr])
  map_mul' := map_mul _

@[simp]
theorem coe_unitsMulEquivOfNoZeroDivisors (σ R : Type*) [CommSemiring R] [NoZeroDivisors R]
    (u : Rˣ) :
    ((unitsMulEquivOfNoZeroDivisors σ R u : (MvPolynomial σ R)ˣ) : MvPolynomial σ R) = C (u : R) :=
  (rfl)

@[simp]
theorem coe_unitsMulEquivOfNoZeroDivisors_symm (σ R : Type*) [CommSemiring R] [NoZeroDivisors R]
    (u : (MvPolynomial σ R)ˣ) :
    (((unitsMulEquivOfNoZeroDivisors σ R).symm u : Rˣ) : R) =
      constantCoeff (u : MvPolynomial σ R) :=
  (rfl)

/-- Over a reduced commutative ring `R`, `C` and `constantCoeff` identify the units of `R` with
the units of `MvPolynomial σ R`. -/
noncomputable def unitsMulEquiv (σ R : Type*) [CommRing R] [IsReduced R] :
    Rˣ ≃* (MvPolynomial σ R)ˣ where
  toFun := Units.map (C : R →+* MvPolynomial σ R).toMonoidHom
  invFun := Units.map (constantCoeff : MvPolynomial σ R →+* R).toMonoidHom
  left_inv u := Units.ext (by simp)
  right_inv u := by
    obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
    exact Units.ext (by simp [hr])
  map_mul' := map_mul _

@[simp]
theorem coe_unitsMulEquiv (σ R : Type*) [CommRing R] [IsReduced R] (u : Rˣ) :
    ((unitsMulEquiv σ R u : (MvPolynomial σ R)ˣ) : MvPolynomial σ R) = C (u : R) :=
  (rfl)

@[simp]
theorem coe_unitsMulEquiv_symm (σ R : Type*) [CommRing R] [IsReduced R]
    (u : (MvPolynomial σ R)ˣ) :
    (((unitsMulEquiv σ R).symm u : Rˣ) : R) = constantCoeff (u : MvPolynomial σ R) :=
  (rfl)

end MvPolynomial
