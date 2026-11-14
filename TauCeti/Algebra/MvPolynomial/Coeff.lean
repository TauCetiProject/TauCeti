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
`p` equals `1`, then scalar multiplication on `p` is faithful: `r ↦ r • p` is injective, since
taking the same combination of the coefficients of `r • p` recovers `r`. In particular
`r • p = 0` if and only if `r = 0`. This holds in every commutative semiring, including rings with
torsion, where `p` having a nonzero coefficient would not be enough.

## Main results

* `MvPolynomial.smul_left_injective_of_sum_coeff_mul_eq_one`: if a combination of the
  coefficients of `p` is `1`, then `r ↦ r • p` is injective.
* `MvPolynomial.smul_eq_zero_iff_left_of_sum_coeff_mul_eq_one`: under the same hypothesis,
  `r • p = 0 ↔ r = 0`.
-/

public section

namespace MvPolynomial

variable {R σ ι : Type*} [CommSemiring R] {p : MvPolynomial σ R}

/-- If some combination `∑ i ∈ s, p.coeff (m i) * c i` of coefficients of `p` is `1`, then
`r ↦ r • p` is injective: the same combination of the coefficients of `r • p` is `r`. -/
theorem smul_left_injective_of_sum_coeff_mul_eq_one (s : Finset ι) (m : ι → σ →₀ ℕ) (c : ι → R)
    (hc : ∑ i ∈ s, p.coeff (m i) * c i = 1) : Function.Injective fun r : R => r • p :=
  Function.LeftInverse.injective (g := fun q => ∑ i ∈ s, q.coeff (m i) * c i) fun r => by
    simp only [coeff_smul, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hc, mul_one]

/-- If some combination `∑ i ∈ s, p.coeff (m i) * c i` of coefficients of `p` is `1`, then
`r • p = 0` if and only if `r = 0`. -/
theorem smul_eq_zero_iff_left_of_sum_coeff_mul_eq_one (s : Finset ι) (m : ι → σ →₀ ℕ)
    (c : ι → R) (hc : ∑ i ∈ s, p.coeff (m i) * c i = 1) {r : R} : r • p = 0 ↔ r = 0 :=
  (smul_left_injective_of_sum_coeff_mul_eq_one s m c hc).eq_iff' (zero_smul R p)

end MvPolynomial
