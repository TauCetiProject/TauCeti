/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Polynomials whose coefficients generate the unit ideal

If some combination `∑ i ∈ s, p.coeff (m i) * c i` of coefficients of a multivariate polynomial
`p` equals `1`, then scalar multiplication on `p` is faithful: `r • p = 0` forces `r = 0`. This
holds in every commutative ring, including rings with torsion, where `p` having a nonzero
coefficient would not be enough.

## Main results

* `MvPolynomial.eq_zero_of_smul_eq_zero_of_sum_coeff_mul_eq_one`: if a combination of the
  coefficients of `p` is `1`, then `r • p = 0` forces `r = 0`.
-/

public section

namespace MvPolynomial

/-- If some combination `∑ i ∈ s, p.coeff (m i) * c i` of coefficients of `p` is `1`, then
`r • p = 0` forces `r = 0`. -/
theorem eq_zero_of_smul_eq_zero_of_sum_coeff_mul_eq_one {R σ ι : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} (s : Finset ι) (m : ι → σ →₀ ℕ) (c : ι → R)
    (hc : ∑ i ∈ s, p.coeff (m i) * c i = 1) {r : R} (h : r • p = 0) : r = 0 := by
  calc r = ∑ i ∈ s, (r • p).coeff (m i) * c i := by
        simp only [coeff_smul, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hc, mul_one]
    _ = 0 := by simp [h]

end MvPolynomial
