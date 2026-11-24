/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

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
  have hC : ¬IsUnit (C (σ := ι) π) := fun h ↦
    hπ.not_isUnit (by simpa using h.map constantCoeff)
  obtain ⟨g, hfg, hndvd⟩ :=
    (FiniteMultiplicity.of_not_isUnit hC hf).exists_eq_pow_mul_and_not_dvd
  rw [← map_pow] at hfg
  obtain ⟨m, hm⟩ := not_forall.mp ((C_dvd_iff_dvd_coeff π g).not.mp hndvd)
  exact ⟨multiplicity (C π) f, g, m, hfg, hm⟩

end MvPolynomial
