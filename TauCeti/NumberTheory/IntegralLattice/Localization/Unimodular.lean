/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Henselian
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Henselian.Basic

/-!
# Classification of unimodular localizations at odd primes

When the signed determinants of two integral lattices are units at an odd prime, their integral
localizations are isometric exactly when they have equal ranks and their determinants agree
modulo squares in `ℤ_p`. Global unimodularity is unnecessary: the hypotheses concern the local
determinants alone. The isometry preserves the actual integral forms on `ℤ_p ⊗[ℤ] L`.

The forward implication holds at every prime and without any determinant-unit hypothesis.

## Main results

* `TauCeti.IntegralLattice.isPerfPair_localIntegralForm_of_isUnit_determinant`: the localized
  integral form is a perfect pairing when the determinant is a unit at `p`.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_imp`: integral local isometry preserves
  the rank and determinant square class at every prime.
* `TauCeti.IntegralLattice.exists_determinant_eq_unit_sq_mul_of_localIntegralForm_equivalent`:
  the signed determinants of integrally isometric localizations differ by a unit square.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff`: for local unit determinants at an
  odd prime, these invariants classify the integral local forms.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_of_not_dvd`: equal rank and signed
  determinant give integral local isometry outside the prime factors of twice the determinant.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, 92:1--92:2.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

open Module

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- **A lattice whose determinant is a unit at `p` has a unimodular localization.** The localized
integral form is then a perfect pairing on `ℤ_p ⊗[ℤ] L`. -/
theorem isPerfPair_localIntegralForm_of_isUnit_determinant (L : IntegralLattice V) (p : ℕ)
    [Fact p.Prime] (hdet : IsUnit (L.determinant : ℤ_[p])) :
    (L.localIntegralForm p).IsPerfPair := by
  rw [← L.det_toMatrix_localIntegralForm p (Module.finBasis ℤ L)] at hdet
  -- `LinearMap.BilinForm.toMatrix b` is defined as `LinearMap.toMatrix₂ b b`.
  exact (Module.finBasis ℤ L).baseChange ℤ_[p] |>.isPerfPair_of_isUnit_det _ hdet

/-- Integrally isometric localizations have equal ranks and determinant products that are
squares, at every prime and without any determinant-unit hypothesis. -/
theorem localIntegralForm_equivalent_imp
    (L : IntegralLattice V) (M : IntegralLattice W) (p : ℕ) [Fact p.Prime]
    (h : (L.localIntegralForm p).Equivalent (M.localIntegralForm p)) :
    finrank ℤ L = finrank ℤ M ∧
      IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])) := by
  classical
  let b := Module.finBasis ℤ L
  let c := Module.finBasis ℤ M
  obtain ⟨e⟩ := id h
  have hn : finrank ℤ L = finrank ℤ M := by
    have h := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_eq_card_basis (b.baseChange ℤ_[p]),
      Module.finrank_eq_card_basis (c.baseChange ℤ_[p])] at h
    simpa using h
  let c' := c.reindex (finCongr hn.symm)
  refine ⟨hn, ?_⟩
  simpa only [det_toMatrix_localIntegralForm] using
    LinearMap.BilinForm.Equivalent.isSquare_det_mul_det
      h (b.baseChange ℤ_[p]) (c'.baseChange ℤ_[p])

/-- Integrally isometric localizations have signed determinants differing by the square of a
`p`-adic unit, at every prime and without any determinant-unit hypothesis. -/
theorem exists_determinant_eq_unit_sq_mul_of_localIntegralForm_equivalent
    (L : IntegralLattice V) (M : IntegralLattice W) (p : ℕ) [Fact p.Prime]
    (h : (L.localIntegralForm p).Equivalent (M.localIntegralForm p)) :
    ∃ u : ℤ_[p]ˣ, (L.determinant : ℤ_[p]) = (u : ℤ_[p]) ^ 2 * (M.determinant : ℤ_[p]) := by
  classical
  let b := Module.finBasis ℤ L
  let c := (Module.finBasis ℤ M).reindex
    (finCongr (L.localIntegralForm_equivalent_imp M p h).1.symm)
  simpa only [det_toMatrix_localIntegralForm] using
    h.exists_det_eq_unit_sq_mul_det (b.baseChange ℤ_[p]) (c.baseChange ℤ_[p])

/-- Localizations unimodular at an odd prime are integrally isometric exactly when their ranks
and determinant square classes agree. The input lattices need not be globally unimodular. -/
theorem localIntegralForm_equivalent_iff
    (L : IntegralLattice V) (M : IntegralLattice W) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hL : IsUnit (L.determinant : ℤ_[p])) (hM : IsUnit (M.determinant : ℤ_[p])) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      finrank ℤ L = finrank ℤ M ∧
        IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])) := by
  classical
  let b := Module.finBasis ℤ L
  let c := Module.finBasis ℤ M
  have hdetL : ((L.localIntegralForm p).toMatrix (b.baseChange ℤ_[p])).det =
      (L.determinant : ℤ_[p]) := L.det_toMatrix_localIntegralForm p b
  have hsame (hn : finrank ℤ L = finrank ℤ M) :
      (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
        IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])) := by
    let c' := c.reindex (finCongr hn.symm)
    have hdetM' : ((M.localIntegralForm p).toMatrix (c'.baseChange ℤ_[p])).det =
        (M.determinant : ℤ_[p]) := M.det_toMatrix_localIntegralForm p c'
    simpa only [hdetL, hdetM'] using
      (L.isSymm_localIntegralForm p).equivalent_iff_isSquare_det_mul_det
        (M.isSymm_localIntegralForm p) (PadicInt.isUnit_two hp) (b.baseChange ℤ_[p])
        (c'.baseChange ℤ_[p]) (hdetL.symm ▸ hL) (hdetM'.symm ▸ hM)
  constructor
  · exact L.localIntegralForm_equivalent_imp M p
  · rintro ⟨hn, hs⟩
    exact (hsame hn).mpr hs

/-- Lattices of equal rank and signed determinant have isometric integral localizations at
every prime not dividing twice the absolute determinant. -/
theorem localIntegralForm_equivalent_of_not_dvd
    (L : IntegralLattice V) (M : IntegralLattice W) {p : ℕ} [Fact p.Prime]
    (hrank : finrank ℤ L = finrank ℤ M) (hdet : L.determinant = M.determinant)
    (hp : ¬p ∣ 2 * L.determinant.natAbs) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hp (dvd_mul_right 2 L.determinant.natAbs)
  have hunit : IsUnit (L.determinant : ℤ_[p]) := by
    by_contra h
    have hdiv := PadicInt.norm_intCast_lt_one_iff.mp (PadicInt.not_isUnit_iff.mp h)
    exact hp (dvd_mul_of_dvd_right (Int.natCast_dvd.mp hdiv) 2)
  apply (L.localIntegralForm_equivalent_iff M hp2 hunit (hdet ▸ hunit)).mpr
  exact ⟨hrank, hdet ▸ IsSquare.mul_self (L.determinant : ℤ_[p])⟩

end TauCeti.IntegralLattice
