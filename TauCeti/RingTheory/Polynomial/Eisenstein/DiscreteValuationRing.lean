/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Eisenstein polynomials over discrete valuation rings

The Eisenstein condition over a discrete valuation ring makes the constant coefficient a
uniformizer. An Eisenstein polynomial is also associated to the minimal polynomial of any of
its roots in a torsion-free domain algebra.

## Main results

* `Polynomial.IsEisensteinAt.irreducible_coeff_zero` identifies the constant coefficient as an
  irreducible element.
* `TauCeti.associated_minpoly_of_eisenstein_isRoot` identifies an Eisenstein polynomial
  over an integrally closed local domain with the minimal polynomial of a root up to a unit.
-/

public section

open IsLocalRing

namespace Polynomial.IsEisensteinAt

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The constant coefficient of an Eisenstein polynomial of positive degree over a discrete
valuation ring is irreducible. -/
theorem irreducible_coeff_zero {f : R[X]} (hf : f.IsEisensteinAt (maximalIdeal R))
    (hdeg : 0 < f.natDegree) : Irreducible (f.coeff 0) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmem : f.coeff 0 ∈ maximalIdeal R := hf.mem hdeg
  have hnotmem : f.coeff 0 ∉ maximalIdeal R ^ 2 := hf.notMem
  have hc0 : f.coeff 0 ≠ 0 := by
    intro hc0
    apply hnotmem
    simp [hc0]
  have hdvd : ϖ ∣ f.coeff 0 := by
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    exact hmem
  have hnotsq : ¬ϖ ^ 2 ∣ f.coeff 0 := by
    intro hsq
    apply hnotmem
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hsq
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  have hn1 : 1 ≤ n := by
    have hval : (1 : ℕ∞) ≤ IsDiscreteValuationRing.addVal R (f.coeff 0) := by
      rw [← IsDiscreteValuationRing.addVal_uniformizer hϖ,
        IsDiscreteValuationRing.addVal_le_iff_dvd]
      exact hdvd
    rw [hu, IsDiscreteValuationRing.addVal_def' u hϖ n] at hval
    exact_mod_cast hval
  have hn2 : ¬2 ≤ n := by
    intro hn
    apply hnotsq
    rw [hu]
    exact (pow_dvd_pow ϖ hn).trans (dvd_mul_left _ _)
  have hn : n = 1 := by omega
  subst n
  exact Associated.irreducible ⟨u, by simpa [mul_comm] using hu.symm⟩ hϖ

end Polynomial.IsEisensteinAt

namespace TauCeti

open Module

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
