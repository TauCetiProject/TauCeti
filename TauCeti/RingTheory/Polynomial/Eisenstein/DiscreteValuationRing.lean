/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# Eisenstein polynomials over discrete valuation rings

The Eisenstein condition over a discrete valuation ring makes the constant coefficient a
uniformizer. Conversely, `X ^ n` minus a uniformizer is Eisenstein for positive `n`, and so is
`X ^ n + a X` plus a uniformizer for `a` in the maximal ideal and `2 ≤ n`.

## Main results

* `Polynomial.IsEisensteinAt.irreducible_coeff_zero` identifies the constant coefficient as an
  irreducible element.
* `Polynomial.IsEisensteinAt.exists_eq_X_pow_add_C_coeff_zero_mul` writes a monic Eisenstein
  polynomial `f` as `X ^ deg f + f(0) g` with `g(0) = 1`, and
  `Polynomial.IsEisensteinAt.exists_pow_natDegree_eq` gives the corresponding identity
  `x ^ deg f = -f(0) g(x)` for a root `x`.
* `Polynomial.IsEisensteinAt.ne_zero_of_aeval_eq_zero`: such a root is nonzero in an algebra
  with injective structure map.
* `TauCeti.isEisensteinAt_X_pow_sub_C_of_irreducible` and
  `TauCeti.isEisensteinAt_X_pow_add_C_mul_X_add_C_of_irreducible` give Eisenstein polynomials
  from uniformizers.
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

/-- A monic Eisenstein polynomial `f` of positive degree over a discrete valuation ring is
`X ^ deg f + f(0) g` for some `g` with `g(0) = 1`, since every non-leading coefficient of `f` is
divisible by the uniformizer `f(0)`. -/
theorem exists_eq_X_pow_add_C_coeff_zero_mul {f : R[X]} (hf : f.IsEisensteinAt (maximalIdeal R))
    (hmo : f.Monic) (hdeg : 0 < f.natDegree) :
    ∃ g : R[X], g.coeff 0 = 1 ∧ f = X ^ f.natDegree + C (f.coeff 0) * g := by
  have hirr := hf.irreducible_coeff_zero hdeg
  have hdvd : C (f.coeff 0) ∣ f - X ^ f.natDegree := by
    refine C_dvd_iff_dvd_coeff _ _ |>.mpr fun i ↦ ?_
    rcases lt_trichotomy i f.natDegree with hi | rfl | hi
    · have : (f - X ^ f.natDegree).coeff i = f.coeff i := by simp [coeff_X_pow, hi.ne]
      rw [this, ← Ideal.mem_span_singleton, ← hirr.maximalIdeal_eq]
      exact hf.mem hi
    · simp [hmo.coeff_natDegree]
    · simp [coeff_X_pow, hi.ne', coeff_eq_zero_of_natDegree_lt hi]
  obtain ⟨g, hg⟩ := hdvd
  refine ⟨g, ?_, by rw [← hg]; ring⟩
  have := congrArg (coeff · 0) hg
  simp only [coeff_sub, coeff_X_pow, hdeg.ne, ite_false, sub_zero, coeff_C_mul] at this
  exact (mul_eq_left₀ hirr.ne_zero).mp this.symm

variable {S : Type*} [CommRing S] [Algebra R S] {f : R[X]} {x : S}

/-- If `x` is a root of a monic polynomial `f` which is Eisenstein at the maximal ideal of a
discrete valuation ring, then `x ^ deg f = -f(0) g(x)` for some `g` with `g(0) = 1`. -/
theorem exists_pow_natDegree_eq [Nontrivial S] (hf : f.IsEisensteinAt (maximalIdeal R))
    (hmo : f.Monic) (hx : aeval x f = 0) :
    ∃ g : R[X], g.coeff 0 = 1 ∧
      x ^ f.natDegree = -(algebraMap R S (f.coeff 0) * aeval x g) := by
  obtain ⟨g, hg0, hg⟩ := hf.exists_eq_X_pow_add_C_coeff_zero_mul hmo
    (hmo.natDegree_pos.mpr (by rintro rfl; simp at hx))
  refine ⟨g, hg0, eq_neg_of_add_eq_zero_left ?_⟩
  simpa [hx] using (congrArg (aeval x) hg).symm

/-- A root of a monic polynomial which is Eisenstein at the maximal ideal of a discrete valuation
ring `R` is nonzero in any `R`-algebra with injective structure map. -/
theorem ne_zero_of_aeval_eq_zero [FaithfulSMul R S] (hf : f.IsEisensteinAt (maximalIdeal R))
    (hmo : f.Monic) (hx : aeval x f = 0) : x ≠ 0 := by
  have := (FaithfulSMul.algebraMap_injective R S).nontrivial
  rintro rfl
  have hirr := hf.irreducible_coeff_zero (hmo.natDegree_pos.mpr (by rintro rfl; simp at hx))
  rw [← coeff_zero_eq_aeval_zero', map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective R S)] at hx
  exact hirr.ne_zero hx

end Polynomial.IsEisensteinAt

namespace TauCeti

open Polynomial

/-- Over a discrete valuation ring, `X ^ n` minus a uniformizer is Eisenstein for positive `n`. -/
theorem isEisensteinAt_X_pow_sub_C_of_irreducible
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {n : ℕ} (hn : 0 < n) :
    (X ^ n - C ϖ).IsEisensteinAt (maximalIdeal R) := by
  apply isEisensteinAt_X_pow_sub_C (by simp [hϖ.maximalIdeal_eq]) _ hn
  rw [IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal,
    IsDiscreteValuationRing.addVal_uniformizer hϖ]
  simp

/-- Over a discrete valuation ring, `X ^ n + C a * X + C ϖ` is Eisenstein when `a` lies in the
maximal ideal, `ϖ` is a uniformizer and `2 ≤ n`. -/
theorem isEisensteinAt_X_pow_add_C_mul_X_add_C_of_irreducible
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a ϖ : R} (ha : a ∈ maximalIdeal R) (hϖ : Irreducible ϖ) {n : ℕ} (hn : 2 ≤ n) :
    (X ^ n + C a * X + C ϖ).IsEisensteinAt (maximalIdeal R) := by
  apply isEisensteinAt_X_pow_add_C_mul_X_add_C ha (by simp [hϖ.maximalIdeal_eq]) _ hn
  rw [IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal,
    IsDiscreteValuationRing.addVal_uniformizer hϖ]
  simp

end TauCeti
