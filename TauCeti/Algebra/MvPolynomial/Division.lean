/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Division

/-!
# Divisibility by powers of a variable

A power `Xᵢ ^ k` of one variable of a multivariate polynomial ring divides `Xⱼ ^ l * p`, for a
different variable `Xⱼ`, exactly when it divides `p`: multiplying by `Xⱼ ^ l` shifts every exponent
vector in the support of `p` by `l` in the coordinate `j` only, which does not change the exponents
of `Xᵢ`. No hypothesis on the coefficient semiring is needed.

This is the divisibility input to the computation of the global sections of the twisting sheaves
`𝒪(n)` on projective space, where the two monomials are powers of two homogeneous coordinates.

## Main results

* `MvPolynomial.X_pow_dvd_X_pow_mul_iff`: for `i ≠ j`, `Xᵢ ^ k ∣ Xⱼ ^ l * p ↔ Xᵢ ^ k ∣ p`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- **A power of a variable divides a polynomial times a power of another variable iff it divides
the polynomial.** -/
theorem X_pow_dvd_X_pow_mul_iff {i j : σ} (hij : i ≠ j) {k l : ℕ} {p : MvPolynomial σ R} :
    X i ^ k ∣ X j ^ l * p ↔ X i ^ k ∣ p := by
  refine ⟨fun h ↦ ?_, fun h ↦ dvd_mul_of_dvd_right h _⟩
  rw [X_pow_eq_monomial, monomial_one_dvd_iff_modMonomial_eq_zero] at h ⊢
  ext m
  by_cases hm : Finsupp.single i k ≤ m
  · exact coeff_modMonomial_of_le _ hm
  -- the coefficient of `p` at `m` is that of `Xⱼ ^ l * p` at `m + l eⱼ`, which has the same
  -- exponent of `Xᵢ` as `m`
  have hm' : ¬Finsupp.single i k ≤ m + Finsupp.single j l := by
    simpa [Finsupp.single_le_iff, Finsupp.single_apply, hij.symm] using hm
  have h' := congrArg (fun q ↦ q.coeff (m + Finsupp.single j l)) h
  rw [coeff_modMonomial_of_not_le _ hm', X_pow_eq_monomial, add_comm m, coeff_monomial_mul,
    one_mul] at h'
  rw [coeff_modMonomial_of_not_le _ hm, h']
  simp

end MvPolynomial
