/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import TauCeti.RingTheory.Derivation.Basic

/-!
# Chain rule for derivations on evaluated multivariate polynomials

For a `k`-derivation `D : Derivation k A A`, a multivariate polynomial `F : MvPolynomial σ A`
evaluated at a point `t : σ → A` satisfies the multivariable chain rule

`D (F.eval t) = (∑ e ∈ F.support, D (F.coeff e) * ∏ j, t j ^ e j) +`
`  ∑ j, (pderiv j F).eval t * D (t j)`,

differentiating both the coefficients of `F` and the coordinate entries `t j`.

## Main results

* `Derivation.apply_eval_monomial`: chain rule on an evaluated monomial.
* `Derivation.apply_eval_mvPolynomial`: chain rule on an evaluated multivariate polynomial.
-/

public section

namespace Derivation

open MvPolynomial

variable {k A σ : Type*} [CommSemiring k] [CommSemiring A] [Algebra k A] [Fintype σ]

/-- Applying a `k`-derivation of `A` to a monomial evaluated at `t` differentiates the coefficient
and the variable powers via the Leibniz rule. -/
theorem apply_eval_monomial (D : Derivation k A A) (e : σ →₀ ℕ) (a : A) (t : σ → A) :
    D ((monomial e a).eval t) =
      D a * (∏ j, t j ^ e j) + ∑ j, (pderiv j (monomial e a)).eval t * D (t j) := by
  classical
  have hprod : e.prod (fun j n ↦ t j ^ n) = ∏ j, t j ^ e j :=
    Finsupp.prod_fintype e (fun j n ↦ t j ^ n) fun _ ↦ pow_zero _
  rw [eval_monomial, hprod, D.leibniz, smul_eq_mul, smul_eq_mul, add_comm,
    mul_comm (∏ j, t j ^ e j)]
  congr 1
  rw [D.leibniz_prod, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_eq_mul, D.leibniz_pow, nsmul_eq_mul, smul_eq_mul, pderiv_monomial, eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  by_cases hj : e j = 0
  · simp [hj]
  · have hsub : ∏ l, t l ^ (e - Finsupp.single j (1 : ℕ)) l =
        t j ^ (e j - 1) * ∏ l ∈ Finset.univ.erase j, t l ^ e l := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      congr 1
      · simp
      · refine Finset.prod_congr rfl fun l hl ↦ ?_
        simp [Finset.ne_of_mem_erase hl]
    rw [hsub]
    ring

/-- **Chain rule for a derivation on a polynomial evaluated at elements of `A`.** -/
theorem apply_eval_mvPolynomial (D : Derivation k A A) (F : MvPolynomial σ A) (t : σ → A) :
    D (F.eval t) =
      (∑ e ∈ F.support, D (F.coeff e) * ∏ j, t j ^ e j) +
        ∑ j, (pderiv j F).eval t * D (t j) := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum, map_sum]
  simp_rw [apply_eval_monomial, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← F.as_sum]

end Derivation
