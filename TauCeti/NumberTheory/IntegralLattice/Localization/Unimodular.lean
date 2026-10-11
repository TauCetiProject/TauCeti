/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Henselian
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Henselian.Basic

/-!
# Classification of unimodular localizations at odd primes

When the signed determinants of two integral lattices are units at an odd prime, their integral
localizations are isometric exactly when they have equal ranks and their determinants agree
modulo squares in `ℤ_p`. Global unimodularity is unnecessary: the hypotheses concern the local
determinants alone. The isometry preserves the actual integral forms on `ℤ_p ⊗[ℤ] L`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, 92:1--92:2.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

open Module

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

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
      (L.determinant : ℤ_[p]) := by
    rw [toMatrix_localIntegralForm, L.determinant_eq_gramDet b, gramDet_def, Int.cast_det]
  have hsame (hn : finrank ℤ L = finrank ℤ M) :
      (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
        IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])) := by
    let c' := c.reindex (finCongr hn.symm)
    have hdetM' : ((M.localIntegralForm p).toMatrix (c'.baseChange ℤ_[p])).det =
        (M.determinant : ℤ_[p]) := by
      rw [toMatrix_localIntegralForm, M.determinant_eq_gramDet c', gramDet_def, Int.cast_det]
    simpa only [hdetL, hdetM'] using
      (L.isSymm_localIntegralForm p).equivalent_iff_isSquare_det_mul_det
        (M.isSymm_localIntegralForm p) (PadicInt.isUnit_two hp) (b.baseChange ℤ_[p])
        (c'.baseChange ℤ_[p]) (hdetL.symm ▸ hL) (hdetM'.symm ▸ hM)
  constructor
  · rintro ⟨e⟩
    have hn : finrank ℤ L = finrank ℤ M := by
      have h := e.toLinearEquiv.finrank_eq
      rw [Module.finrank_eq_card_basis (b.baseChange ℤ_[p]),
        Module.finrank_eq_card_basis (c.baseChange ℤ_[p])] at h
      simpa using h
    exact ⟨hn, (hsame hn).mp ⟨e⟩⟩
  · rintro ⟨hn, hs⟩
    exact (hsame hn).mpr hs

end TauCeti.IntegralLattice
