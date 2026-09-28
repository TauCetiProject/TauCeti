/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Eisenstein polynomials over discrete valuation rings

This file records the elementary consequence of the Eisenstein condition that the constant
coefficient is a uniformizer, and conversely that `X ^ n - ϖ` is Eisenstein for every uniformizer
`ϖ`.  It complements Mathlib's general Eisenstein criterion with the specialization to a discrete
valuation ring.
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

/-- Over a discrete valuation ring, `X ^ n - C ϖ` is Eisenstein at the maximal ideal for every
uniformizer `ϖ` and every `n > 0`: the polynomial whose roots are the `n`-th roots of `ϖ`. -/
theorem Irreducible.isEisensteinAt_X_pow_sub_C {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) {n : ℕ} (hn : 0 < n) :
    (Polynomial.X ^ n - Polynomial.C ϖ).IsEisensteinAt (maximalIdeal R) := by
  refine (Polynomial.monic_X_pow_sub_C ϖ hn.ne').isEisensteinAt_of_mem_of_notMem
    (maximalIdeal.isMaximal R).ne_top (fun {m} hm ↦ ?_) ?_
  · rw [Polynomial.natDegree_X_pow_sub_C] at hm
    rcases eq_or_ne m 0 with rfl | hm0
    · rw [hϖ.maximalIdeal_eq]
      simp [hn.ne]
    · simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, hm0, hm.ne]
  · have hsq : ¬ϖ ^ 2 ∣ ϖ ^ 1 := by
      rw [pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit]
      lia
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simpa [Polynomial.coeff_X_pow, hn.ne] using hsq
