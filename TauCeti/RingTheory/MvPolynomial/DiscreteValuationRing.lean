/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Multivariate polynomials over discrete valuation rings

Any nonzero multivariate polynomial over a discrete valuation ring `R` factors out the minimum
valuation of its coefficients as a power of a uniformizer `π`, leaving a primitive polynomial
having at least one coefficient not divisible by `π`
(`MvPolynomial.exists_C_pow_mul_and_not_dvd_coeff`).

## Main results

* `MvPolynomial.exists_C_pow_mul_and_not_dvd_coeff`: uniformizer power factorization for nonzero
  multivariate polynomials over a discrete valuation ring.
-/

public section

namespace MvPolynomial

/-- A nonzero multivariate polynomial over a discrete valuation ring factors out a power of a
uniformizer so that at least one coefficient is not divisible by the uniformizer. -/
theorem exists_C_pow_mul_and_not_dvd_coeff {R ι : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π)
    {f : MvPolynomial ι R} (hf : f ≠ 0) :
    ∃ (n : ℕ) (g : MvPolynomial ι R) (m : ι →₀ ℕ),
      f = C (π ^ n) * g ∧ ¬ π ∣ g.coeff m := by
  classical
  obtain ⟨m₀, hm₀, hmin⟩ :=
    f.support.exists_min_image (fun m ↦ (IsDiscreteValuationRing.addVal R (f.coeff m)).toNat)
      (support_nonempty.mpr hf)
  set n := (IsDiscreteValuationRing.addVal R (f.coeff m₀)).toNat
  have hval_m₀ : IsDiscreteValuationRing.addVal R (f.coeff m₀) = n :=
    (ENat.natCast_toNat (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr
      (mem_support_iff.mp hm₀))).symm
  have hdvd (m : ι →₀ ℕ) : π ^ n ∣ f.coeff m := by
    by_cases hm : m ∈ f.support
    · rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hπ.addVal_pow]
      have hne : IsDiscreteValuationRing.addVal R (f.coeff m) ≠ ⊤ :=
        IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (mem_support_iff.mp hm)
      rw [← ENat.natCast_toNat hne]
      exact mod_cast hmin m hm
    · rw [notMem_support_iff.mp hm]
      exact dvd_zero _
  obtain ⟨g, hfg⟩ := (MvPolynomial.C_dvd_iff_dvd_coeff (π ^ n) f).mpr hdvd
  refine ⟨n, g, m₀, hfg, fun ⟨d, hd⟩ ↦ ?_⟩
  have hle : ((n + 1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal R (f.coeff m₀) := by
    rw [← hπ.addVal_pow, IsDiscreteValuationRing.addVal_le_iff_dvd]
    have hcoeff : f.coeff m₀ = π ^ n * g.coeff m₀ :=
      (congrArg (fun p ↦ p.coeff m₀) hfg).trans (coeff_C_mul _ _ _)
    exact ⟨d, by rw [hcoeff, hd, pow_succ, mul_assoc]⟩
  rw [hval_m₀] at hle
  exact Nat.not_succ_le_self n (ENat.natCast_le_natCast.mp hle)

end MvPolynomial
