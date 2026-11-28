/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import TauCeti.RingTheory.MvPolynomial.Quotient.Basic

/-!
# Detecting the unit ideal on polynomial fibres

A system of polynomial equations cuts out the empty scheme precisely when it does so
on every residue-field fibre. In particular this detects whether the partial derivatives
generate the unit ideal on a hypersurface over an arbitrary base ring.
-/

public section

namespace Ideal

open MvPolynomial

/-- A polynomial ideal is the unit ideal exactly when its image over the residue
field at every prime of the coefficient ring is the unit ideal. -/
theorem eq_top_iff_forall_map_residueField_eq_top {R ι : Type*} [CommRing R]
    (I : Ideal (MvPolynomial ι R)) :
    I = ⊤ ↔ ∀ p : PrimeSpectrum R,
      I.map (MvPolynomial.map (algebraMap R p.asIdeal.ResidueField)) = ⊤ := by
  refine ⟨fun h p ↦ by rw [h, Ideal.map_top], fun h ↦ ?_⟩
  by_contra hI
  let S := MvPolynomial ι R ⧸ I
  have : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨q⟩ := (inferInstance : Nonempty (PrimeSpectrum S))
  let p := PrimeSpectrum.comap (algebraMap R S) q
  have := (p.nontrivial_iff_mem_rangeComap (S := S)).mpr ⟨q, rfl⟩
  let e := I.tensorQuotientMvPolynomialEquiv (B := p.asIdeal.ResidueField)
  exact Ideal.Quotient.nontrivial_iff.mp e.symm.toEquiv.nontrivial (h p)

end Ideal
