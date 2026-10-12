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

An Eisenstein polynomial over an integrally closed local domain is associated to the minimal
polynomial of any of its roots in a torsion-free domain algebra.

## Main results

* `TauCeti.associated_minpoly_of_eisenstein_isRoot` identifies the minimal polynomial up to a
  unit.
-/

public section

open IsLocalRing Module

namespace TauCeti

variable {R S : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsIntegrallyClosed R]
  [CommRing S] [IsDomain S] [Algebra R S] [IsTorsionFree R S]

/-- The minimal polynomial of a root is associated to an Eisenstein polynomial over an integrally
closed local domain. -/
theorem associated_minpoly_of_eisenstein_isRoot
    (ξ : S) (f : Polynomial R) (hf : f.IsEisensteinAt (maximalIdeal R))
    (hroot : (f.map (algebraMap R S)).IsRoot ξ) : Associated (minpoly R ξ) f := by
  have hdeg : 0 < f.natDegree := by
    by_contra h
    have hdeg0 : f.natDegree = 0 := Nat.eq_zero_of_not_pos h
    have hlc : IsUnit f.leadingCoeff := notMem_maximalIdeal.mp hf.leading
    have hc0 : f.coeff 0 = f.leadingCoeff := by
      rw [← Polynomial.coeff_natDegree, hdeg0]
    have hmaplc : algebraMap R S (f.coeff 0) ≠ 0 :=
      hc0.symm ▸ (hlc.map (algebraMap R S)).ne_zero
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, Polynomial.map_C] at hroot
    exact Polynomial.not_isRoot_C _ _ hmaplc hroot
  have hprim : f.IsPrimitive := by
    rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
    intro r hr
    apply isUnit_of_dvd_unit _ (notMem_maximalIdeal.mp hf.leading)
    rw [← Polynomial.coeff_natDegree]
    exact (Polynomial.C_dvd_iff_dvd_coeff r f).mp hr f.natDegree
  have hfirr : Irreducible f :=
    hf.irreducible (maximalIdeal.isMaximal R).isPrime hprim hdeg
  have haeval : Polynomial.aeval ξ f = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hroot
  have hξ : IsIntegral R ξ :=
    (minpoly.IsIntegrallyClosed.isIntegral_iff_isUnit_leadingCoeff hfirr haeval).2
      (notMem_maximalIdeal.mp hf.leading)
  exact (minpoly.irreducible hξ).associated_of_dvd hfirr
    (minpoly.isIntegrallyClosed_dvd hξ haeval)

end TauCeti
