/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Polynomials over quotients by a decreasing sequence of ideals

Coefficientwise reduction `MvPolynomial.map (Ideal.Quotient.factor _)` transports one-step
compatibility of a sequence of multivariate polynomials `p n ∈ (R ⧸ I n)[X_σ]` along an antitone
filtration `I : ℕ → Ideal R` to compatibility across arbitrary indices `m ≤ n`, lifting
`Ideal.Quotient.eq_factor_of_eq_factor_succ` from scalars to polynomial coefficients.

## Main results

* `TauCeti.MvPolynomial.map_factor_eq_of_map_factor_succ_eq`: one-step compatibility under
  `MvPolynomial.map (Ideal.Quotient.factor _)` implies compatibility for all `m ≤ n`.
-/

public section

namespace TauCeti

/-- In a multivariate polynomial ring over quotients by a decreasing sequence of ideals, one-step
compatibility of a sequence of polynomials under coefficient reduction along
`Ideal.Quotient.factor` implies compatibility across all indices `m ≤ n`. -/
theorem MvPolynomial.map_factor_eq_of_map_factor_succ_eq {R σ : Type*} [CommRing R]
    {I : ℕ → Ideal R} (hI : Antitone I) {p : ∀ n : ℕ, MvPolynomial σ (R ⧸ I n)}
    (hp : ∀ m, MvPolynomial.map (Ideal.Quotient.factor (hI m.le_succ)) (p (m + 1)) = p m)
    {m n : ℕ} (hmn : m ≤ n) :
    MvPolynomial.map (Ideal.Quotient.factor (hI hmn)) (p n) = p m := by
  ext ν
  rw [MvPolynomial.coeff_map]
  exact (Ideal.Quotient.eq_factor_of_eq_factor_succ hI (fun k ↦ (p k).coeff ν)
    (fun k ↦ by
      simpa only [MvPolynomial.coeff_map] using (congrArg (·.coeff ν) (hp k)).symm)
    hmn).symm

end TauCeti
