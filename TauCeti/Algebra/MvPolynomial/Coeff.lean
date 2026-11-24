/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# Coefficients of multivariate polynomials

The coefficients of a power sum `∑ g ∈ s, (∑ i, a g i • X i) ^ n` of linear forms are multinomial
multiples of the power sums `∑ g ∈ s, ∏ i, a g i ^ e i`.

If some combination `∑ i ∈ s, p.coeff (m i) * c i` of coefficients of a multivariate polynomial
`p` equals `1`, then scalar multiplication on `p` is faithful: `r ↦ r • p` is injective, since
taking the same combination of the coefficients of `r • p` recovers `r`. In particular
`r • p = 0` if and only if `r = 0`. This holds in every commutative semiring, including rings with
torsion, where `p` having a nonzero coefficient would not be enough.

The coefficient of a single variable `Xᵢ` in a product obeys the Leibniz rule at `0`, as for the
linear coefficient of a univariate power series (`PowerSeries.coeff_one_mul`).

## Main results

* `MvPolynomial.coeff_sum_linearCombination_X_pow_of_fintype`: the coefficients of a power sum of
  linear forms.
* `MvPolynomial.smul_left_injective_of_sum_coeff_mul_eq_one`: if a combination of the
  coefficients of `p` is `1`, then `r ↦ r • p` is injective.
* `MvPolynomial.smul_eq_zero_iff_left_of_sum_coeff_mul_eq_one`: under the same hypothesis,
  `r • p = 0 ↔ r = 0`.
* `MvPolynomial.coeff_single_one_mul`: the coefficient of `Xᵢ` in `p * q` is
  `pᵢ q(0) + p(0) qᵢ`.
-/

public section

namespace MvPolynomial

variable {R σ ι : Type*} [CommSemiring R] {p : MvPolynomial σ R}

/-- If some combination `∑ i ∈ s, p.coeff (m i) * c i` of coefficients of `p` is `1`, then
`r ↦ r • p` is injective: the same combination of the coefficients of `r • p` is `r`. -/
theorem smul_left_injective_of_sum_coeff_mul_eq_one (s : Finset ι) (m : ι → σ →₀ ℕ) (c : ι → R)
    (hc : ∑ i ∈ s, p.coeff (m i) * c i = 1) : Function.Injective fun r : R => r • p :=
  Function.LeftInverse.injective (g := fun q => ∑ i ∈ s, q.coeff (m i) * c i) fun r => by
    simp only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hc,
      mul_one]

/-- If some combination `∑ i ∈ s, p.coeff (m i) * c i` of coefficients of `p` is `1`, then
`r • p = 0` if and only if `r = 0`. -/
theorem smul_eq_zero_iff_left_of_sum_coeff_mul_eq_one (s : Finset ι) (m : ι → σ →₀ ℕ)
    (c : ι → R) (hc : ∑ i ∈ s, p.coeff (m i) * c i = 1) {r : R} : r • p = 0 ↔ r = 0 :=
  (smul_left_injective_of_sum_coeff_mul_eq_one s m c hc).eq_iff' (zero_smul R p)

/-- **Coefficients of power sums of linear forms.** The coefficient of `X ^ e` in
`∑ g ∈ s, (∑ i, a g i • X i) ^ n` is `multinomial e * ∑ g ∈ s, ∏ i, a g i ^ e i` if `e` has total
degree `n`, and zero otherwise. -/
theorem coeff_sum_linearCombination_X_pow_of_fintype [Fintype σ] (s : Finset ι) (a : ι → σ → R)
    (e : σ →₀ ℕ) (n : ℕ) :
    (∑ g ∈ s, (∑ i, a g i • X i : MvPolynomial σ R) ^ n).coeff e =
      if e.sum (fun _ m ↦ m) = n then e.multinomial * ∑ g ∈ s, e.prod (fun i m ↦ a g i ^ m)
      else 0 := by
  simp only [coeff_sum, coeff_linearCombination_X_pow_of_fintype]
  split_ifs <;> simp [Finset.mul_sum]

/-- **The linear coefficients of a product**: the coefficient of the variable `Xᵢ` in `p * q` is
`pᵢ q(0) + p(0) qᵢ`, so taking it is a derivation at `0`. -/
theorem coeff_single_one_mul (i : σ) (p q : MvPolynomial σ R) :
    (p * q).coeff (Finsupp.single i 1) =
      p.coeff (Finsupp.single i 1) * constantCoeff q +
        constantCoeff p * q.coeff (Finsupp.single i 1) := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, constantCoeff_eq, add_comm]

end MvPolynomial
