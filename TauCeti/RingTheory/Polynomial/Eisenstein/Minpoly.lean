/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Minimal polynomials of Eisenstein roots

An Eisenstein polynomial with unit leading coefficient over an integrally closed domain is
associated to the minimal polynomial of any of its roots in a torsion-free domain algebra. Over a
local ring, every polynomial that is Eisenstein at the maximal ideal has unit leading coefficient.

## Main results

* `TauCeti.associated_minpoly_of_eisenstein_isRoot` identifies the minimal polynomial up to a
  unit.
-/

public section

open Polynomial

namespace TauCeti

variable {R S : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing S] [IsDomain S] [Algebra R S] [Module.IsTorsionFree R S]

/-- The minimal polynomial of a root of an Eisenstein polynomial `f` with unit leading coefficient
over an integrally closed domain is associated to `f`. -/
theorem associated_minpoly_of_eisenstein_isRoot {𝓟 : Ideal R} [𝓟.IsPrime] {f : R[X]} {ξ : S}
    (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff)
    (hroot : (f.map (algebraMap R S)).IsRoot ξ) : Associated (minpoly R ξ) f := by
  have haeval : aeval ξ f = 0 := by simpa [aeval_def] using hroot
  have hdeg : 0 < f.natDegree :=
    natDegree_pos_of_aeval_root (leadingCoeff_ne_zero.1 hlc.ne_zero) haeval
      fun _ ↦ (FaithfulSMul.algebraMap_eq_zero_iff R S).1
  have hfirr : Irreducible f := hf.irreducible inferInstance
    (isPrimitive_iff_isUnit_of_C_dvd.2 fun r hr ↦
      isUnit_of_dvd_unit (by simpa using (C_dvd_iff_dvd_coeff r f).1 hr f.natDegree) hlc) hdeg
  have hξ : IsIntegral R ξ :=
    (minpoly.IsIntegrallyClosed.isIntegral_iff_isUnit_leadingCoeff hfirr haeval).2 hlc
  exact (minpoly.irreducible hξ).associated_of_dvd hfirr (minpoly.isIntegrallyClosed_dvd hξ haeval)

end TauCeti
