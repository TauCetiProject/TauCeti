/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Minimal polynomials of Eisenstein roots

An Eisenstein polynomial with unit leading coefficient over an integrally closed domain is
associated to the minimal polynomial of any of its roots in a torsion-free domain algebra. Over a
local ring, every polynomial that is Eisenstein at the maximal ideal has unit leading coefficient.

## Main results

* `Polynomial.IsEisensteinAt.isUnit_leadingCoeff`: over a local ring, a polynomial that is
  Eisenstein at the maximal ideal has unit leading coefficient.
* `Polynomial.IsEisensteinAt.associated_minpoly` and
  `Polynomial.IsEisensteinAt.eq_C_leadingCoeff_mul_minpoly` identify the minimal polynomial up to
  a unit and up to `C f.leadingCoeff`.
-/

public section

namespace Polynomial.IsEisensteinAt

/-- Over a local ring, a polynomial that is Eisenstein at the maximal ideal has unit leading
coefficient. -/
theorem isUnit_leadingCoeff {R : Type*} [CommSemiring R] [IsLocalRing R] {f : R[X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal R)) : IsUnit f.leadingCoeff :=
  IsLocalRing.notMem_maximalIdeal.mp hf.leading

variable {R S : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing S] [IsDomain S] [Algebra R S] [Module.IsTorsionFree R S]

/-- The minimal polynomial of a root of an Eisenstein polynomial `f` with unit leading coefficient
over an integrally closed domain is associated to `f`. -/
theorem associated_minpoly {𝓟 : Ideal R} [𝓟.IsPrime] {f : R[X]} {ξ : S}
    (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff)
    (hroot : (f.map (algebraMap R S)).IsRoot ξ) : Associated (minpoly R ξ) f := by
  have haeval : aeval ξ f = 0 := by simpa [aeval_def] using hroot
  have hdeg : 0 < f.natDegree :=
    natDegree_pos_of_aeval_root (leadingCoeff_ne_zero.1 hlc.ne_zero) haeval
      fun _ ↦ (FaithfulSMul.algebraMap_eq_zero_iff R S).1
  have hfirr : Irreducible f := hf.irreducible inferInstance
    (isPrimitive_iff_isUnit_of_C_dvd.2 fun r hr ↦
      isUnit_of_dvd_unit (by simpa using (C_dvd_iff_dvd_coeff r f).1 hr f.natDegree) hlc) hdeg
  have hξ : IsIntegral R ξ := IsIntegral.of_isUnit_leadingCoeff hlc haeval
  exact (minpoly.irreducible hξ).associated_of_dvd hfirr (minpoly.isIntegrallyClosed_dvd hξ haeval)

/-- An Eisenstein polynomial `f` with unit leading coefficient over an integrally closed domain
equals `C f.leadingCoeff * minpoly R ξ` for any root `ξ` in a torsion-free domain algebra. -/
theorem eq_C_leadingCoeff_mul_minpoly {𝓟 : Ideal R} [𝓟.IsPrime] {f : R[X]} {ξ : S}
    (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff)
    (hroot : (f.map (algebraMap R S)).IsRoot ξ) :
    f = C f.leadingCoeff * minpoly R ξ := by
  have hassoc := hf.associated_minpoly hlc hroot
  have hξ : IsIntegral R ξ :=
    IsIntegral.of_isUnit_leadingCoeff hlc (by simpa [aeval_def] using hroot)
  exact eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hξ) hassoc.dvd
    (natDegree_le_natDegree (degree_eq_degree_of_associated hassoc).symm.le)

end Polynomial.IsEisensteinAt
