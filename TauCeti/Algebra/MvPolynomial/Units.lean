/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-!
# Units of multivariate polynomial rings

Over a commutative ring, a polynomial is a unit exactly when its constant coefficient is a unit and
its other coefficients are nilpotent (`MvPolynomial.isUnit_iff`). Over any reduced commutative
semiring `R`, every unit of `MvPolynomial σ R` is a constant unit `C r`
(`TauCeti.MvPolynomial.isUnit_iff_eq_C`), giving a canonical multiplicative equivalence
`Rˣ ≃* (MvPolynomial σ R)ˣ` via `C` and `constantCoeff` (`TauCeti.MvPolynomial.unitsMulEquiv`).

Mapping the coefficients along an injective local homomorphism `f : R →+* S` of commutative rings
also reflects units: if `map f p` is a unit of `S[X_σ]`, then, since `f` is injective and reflects
units, the same coefficient conditions hold for `p`. In other words `map f` is a local
homomorphism, so irreducibility of `map f p` implies irreducibility of `p` (`Irreducible.of_map`).
Every ring homomorphism from a field `k` into a nontrivial commutative ring is injective and local,
so this holds for it with no hypothesis. This is how absolute irreducibility, over an algebraic
closure, gives irreducibility over every intermediate field.

## Main definitions

* `TauCeti.MvPolynomial.unitsMulEquiv`: the unit group equivalence `Rˣ ≃* (MvPolynomial σ R)ˣ` over
  any reduced commutative semiring `R`.

## Main results

* `TauCeti.MvPolynomial.isUnit_iff_eq_C`: over a reduced commutative semiring, a multivariate
  polynomial is a unit if and only if it is `C r` for a unit `r`.
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

end MvPolynomial

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial

/-- Over any reduced commutative semiring, a multivariate polynomial is a unit if and only if it is
`C r` for a unit `r` of the coefficient semiring. This generalizes Mathlib's ring result
`MvPolynomial.isUnit_iff_eq_C_of_isReduced` via a separate leading-monomial proof using `degLex`. -/
theorem isUnit_iff_eq_C {σ R : Type*} [CommSemiring R] [IsReduced R]
    {p : _root_.MvPolynomial σ R} : IsUnit p ↔ ∃ r, IsUnit r ∧ p = C r := by
  refine ⟨fun hp ↦ ?_, ?_⟩
  · rcases subsingleton_or_nontrivial R with hR | hR
    · exact ⟨0, isUnit_of_subsingleton 0, Subsingleton.elim _ _⟩
    obtain ⟨q, hpq⟩ := hp.exists_right_inv
    have hp0 : p ≠ 0 := by rintro rfl; simp at hpq
    cases exists_wellFoundedGT σ
    let m : MonomialOrder σ := MonomialOrder.degLex
    let a : R := m.leadingCoeff p
    have ha : a ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hp0
    let r : _root_.MvPolynomial σ R := C a * q
    have hpr : p * r = C a := by rw [mul_left_comm p (C a) q, hpq, mul_one]
    have hr0 : r ≠ 0 := by
      rintro hr0
      apply ha
      simpa [hr0] using congrArg constantCoeff hpr.symm
    have hlr : m.leadingCoeff r ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hr0
    -- Scaling `q` by `a = m.leadingCoeff p` makes `m.leadingCoeff r` a multiple of `a`, so if
    -- `a * m.leadingCoeff r = 0` then `(m.leadingCoeff r) ^ 2 = 0`, contradicting reducedness.
    have hmul : a * m.leadingCoeff r ≠ 0 := by
      intro hzero
      apply hlr
      apply eq_zero_of_pow_eq_zero (n := 2)
      have hcoeff : m.leadingCoeff r = a * q.coeff (m.degree r) := by
        simp [MonomialOrder.leadingCoeff, r]
      rw [sq, hcoeff, mul_right_comm, ← hcoeff, hzero, zero_mul]
    have hdeg : m.degree p + m.degree r = 0 := by
      rw [← m.degree_mul_of_mul_leadingCoeff_ne_zero hmul, hpr, m.degree_C]
    have hp_eq : p = C (m.leadingCoeff p) :=
      m.eq_C_of_degree_eq_zero (add_eq_zero.mp hdeg).1
    have hc : IsUnit (constantCoeff p) := hp.map constantCoeff
    rw [hp_eq, constantCoeff_C] at hc
    exact ⟨m.leadingCoeff p, hc, hp_eq⟩
  · rintro ⟨r, hr, rfl⟩
    exact hr.map C

/-- Over a reduced commutative semiring `R`, `C` and `constantCoeff` identify the units of `R` with
the units of `MvPolynomial σ R`. -/
noncomputable def unitsMulEquiv (σ R : Type*) [CommSemiring R] [IsReduced R] :
    Rˣ ≃* (_root_.MvPolynomial σ R)ˣ where
  toFun := Units.map (C : R →+* _root_.MvPolynomial σ R).toMonoidHom
  invFun := Units.map (constantCoeff : _root_.MvPolynomial σ R →+* R).toMonoidHom
  left_inv u := Units.ext (by simp)
  right_inv u := by
    obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C.mp u.isUnit
    exact Units.ext (by simp [hr])
  map_mul' := map_mul _

@[simp]
theorem coe_unitsMulEquiv (σ R : Type*) [CommSemiring R] [IsReduced R] (u : Rˣ) :
    ((unitsMulEquiv σ R u : (_root_.MvPolynomial σ R)ˣ) : _root_.MvPolynomial σ R) = C (u : R) := by
  simp [unitsMulEquiv]

@[simp]
theorem coe_unitsMulEquiv_symm (σ R : Type*) [CommSemiring R] [IsReduced R]
    (u : (_root_.MvPolynomial σ R)ˣ) :
    (((unitsMulEquiv σ R).symm u : Rˣ) : R) = constantCoeff (u : _root_.MvPolynomial σ R) := by
  simp [unitsMulEquiv]

end TauCeti.MvPolynomial
