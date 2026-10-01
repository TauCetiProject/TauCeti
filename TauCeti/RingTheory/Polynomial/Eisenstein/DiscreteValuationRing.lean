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

The Eisenstein condition over a discrete valuation ring makes the constant coefficient a
uniformizer.

## Main results

* `Polynomial.IsEisensteinAt.irreducible_coeff_zero` identifies the constant coefficient as an
  irreducible element.
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
