/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.Basic
import TauCeti.RingTheory.PowerSeries.Dvd

/-!
# Coprime polynomial factorisations of entire power series

This file provides tools for manipulating coprime polynomial factorisations `H = Q * S` inside
`PowerSeries.IsEntire.subring R`, where `Q : Polynomial R` has unit leading coefficient and
`S : PowerSeries R` is entire.

When `H(0) = 1`, the constant coefficient `Q(0)` is a unit, so rescaling by
`b = Ring.inverse (Q.coeff 0)` reduces to the normalised factorisation
`H = (C b * Q) * (C (Q.coeff 0) * S)` with `(C b * Q)(0) = 1`
(`PowerSeries.IsEntire.normalised_factorisation`). Bounded ring homomorphisms transport coprime
polynomial factorisations along `IsEntire.mapHom` (`PowerSeries.IsEntire.map_factorisation`).

## Main results

* `PowerSeries.IsEntire.normalised_factorisation`: rescales a coprime polynomial factorisation
  `u_series = Q * S` with `u_series(0) = 1` to the normalised case `(C b * Q)(0) = 1`.
* `PowerSeries.IsEntire.map_factorisation`: transports a coprime polynomial factorisation along a
  bounded ring homomorphism into a nontrivial normed commutative ring.
-/

public section

namespace PowerSeries

section Factorisation

/-- Rescales a general coprime factorisation `u_series = Q * S` (with `u_series(0) = 1`) to the
normalised case `(C b * Q)(0) = 1` via `b = Ring.inverse (Q.coeff 0)` and `S₁ = C (Q.coeff 0) * S`.
-/
theorem IsEntire.normalised_factorisation {R : Type*} [NormedCommRing R]
    {u_series : R⟦X⟧} (hu0 : constantCoeff u_series = 1)
    {Q : Polynomial R} {S : R⟦X⟧} (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hQS : u_series = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    let b := Ring.inverse (Q.coeff 0)
    let Q₁ := Polynomial.C b * Q
    let S₁ := C (Q.coeff 0) * S
    IsUnit b ∧ S₁.IsEntire ∧ Q₁.coeff 0 = 1 ∧ IsUnit Q₁.leadingCoeff ∧
      Q₁.natDegree = Q.natDegree ∧ u_series = (Q₁ : R⟦X⟧) * S₁ ∧
      IsCoprime (IsEntire.polynomialHom Q₁)
        ⟨S₁, IsEntire.mem_subring.mpr ((isEntire_C (Q.coeff 0)).mul hS)⟩ := by
  have ha : IsUnit (Q.coeff 0) := isUnit_coeff_zero_of_eq_coe_mul hu0 hQS
  set a : R := Q.coeff 0
  set b : R := Ring.inverse a
  have hba : b * a = 1 := Ring.inverse_mul_cancel a ha
  have hb : IsUnit b := IsUnit.of_mul_eq_one a hba
  set Q₁ : Polynomial R := Polynomial.C b * Q
  set S₁ : R⟦X⟧ := C a * S
  have hS₁ : S₁.IsEntire := (isEntire_C a).mul hS
  have hQ₁0 : Q₁.coeff 0 = 1 := by simp [Q₁, hba, a]
  have hQ₁deg : Q₁.natDegree = Q.natDegree := Polynomial.natDegree_C_mul_of_isUnit hb Q
  have hQ₁lc : IsUnit Q₁.leadingCoeff := by
    rw [Polynomial.leadingCoeff_C_mul_of_isUnit hb]
    exact hb.mul hQ
  have hQS₁ : u_series = (Q₁ : R⟦X⟧) * S₁ := by
    rw [hQS]
    simp only [Q₁, S₁, Polynomial.coe_mul, Polynomial.coe_C]
    calc (Q : R⟦X⟧) * S = C (b * a) * ((Q : R⟦X⟧) * S) := by rw [hba, map_one, one_mul]
      _ = C b * (Q : R⟦X⟧) * (C a * S) := by rw [map_mul]; ring
  let S₀ : IsEntire.subring R := ⟨S, IsEntire.mem_subring.mpr hS⟩
  let S₁sub : IsEntire.subring R := ⟨S₁, IsEntire.mem_subring.mpr hS₁⟩
  have hS₁sub : S₁sub = IsEntire.polynomialHom (Polynomial.C a) * S₀ :=
    Subtype.ext (by simp [S₁sub, S₁, S₀])
  have hb' : IsUnit (IsEntire.polynomialHom (Polynomial.C b)) :=
    hb.map (IsEntire.polynomialHom.comp Polynomial.C)
  have ha' : IsUnit (IsEntire.polynomialHom (Polynomial.C a)) :=
    ha.map (IsEntire.polynomialHom.comp Polynomial.C)
  have hcop₁ : IsCoprime (IsEntire.polynomialHom Q₁) S₁sub := by
    rw [hS₁sub]
    simpa only [Q₁, map_mul] using (isCoprime_mul_units_left hb' ha' _ _).2 hcop
  exact ⟨hb, hS₁, hQ₁0, hQ₁lc, hQ₁deg, hQS₁, hcop₁⟩

/-- Transports a coprime polynomial factorisation `H = Q * S'` in entire power series along a
bounded ring homomorphism `f : R →+* S` into a nontrivial normed commutative ring `S`. -/
theorem IsEntire.map_factorisation {R S : Type*} [NormedCommRing R] [NormedCommRing S]
    [Nontrivial S] {H : R⟦X⟧} {Q : Polynomial R} {S' : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS' : S'.IsEntire) (hQS' : H = (Q : R⟦X⟧) * S')
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S', IsEntire.mem_subring.mpr hS'⟩)
    (f : R →+* S) {C : ℝ} (hf : ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (Q.map f).natDegree = Q.natDegree ∧
      IsUnit (Q.map f).leadingCoeff ∧
      (PowerSeries.map f S').IsEntire ∧
      PowerSeries.map f H = ((Q.map f : Polynomial S) : S⟦X⟧) * PowerSeries.map f S' ∧
      IsCoprime (IsEntire.polynomialHom (Q.map f))
        ⟨PowerSeries.map f S', IsEntire.mem_subring.mpr (hS'.map f hf)⟩ := by
  have hQdeg : (Q.map f).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff f hQ
  have hQlc : IsUnit (Q.map f).leadingCoeff := by
    rw [Polynomial.leadingCoeff_map_eq_of_isUnit_leadingCoeff f hQ]
    exact hQ.map f
  have hFS : (PowerSeries.map f S').IsEntire := hS'.map f hf
  have hHS : PowerSeries.map f H = ((Q.map f : Polynomial S) : S⟦X⟧) * PowerSeries.map f S' := by
    rw [hQS', map_mul, Polynomial.polynomial_map_coe]
  let S₀ : IsEntire.subring R := ⟨S', IsEntire.mem_subring.mpr hS'⟩
  let S₁ : IsEntire.subring S := ⟨PowerSeries.map f S', IsEntire.mem_subring.mpr hFS⟩
  have hS₁ : IsEntire.mapHom f hf S₀ = S₁ := Subtype.ext (IsEntire.coe_mapHom f hf S₀)
  have hcopS : IsCoprime (IsEntire.polynomialHom (Q.map f)) S₁ := by
    rw [← hS₁, ← IsEntire.mapHom_polynomialHom f hf Q]
    exact hcop.map (IsEntire.mapHom f hf)
  exact ⟨hQdeg, hQlc, hFS, hHS, hcopS⟩

end Factorisation

end PowerSeries
