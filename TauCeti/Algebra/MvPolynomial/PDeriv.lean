/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The chain rule for partial derivatives of multivariate polynomials

Substituting polynomials `fᵢ ∈ R[Y_τ]` for the finitely many variables `Xᵢ` of `p ∈ R[X_σ]` and
differentiating with respect to `Y_j` obeys the chain rule

`∂/∂Y_j (p(f)) = ∑ᵢ (∂p/∂Xᵢ)(f) · ∂fᵢ/∂Y_j`.

## Main results

* `MvPolynomial.pderiv_aeval`: the chain rule.
-/

public section

namespace MvPolynomial

variable {R σ τ : Type*} [CommSemiring R] [Fintype σ]

/-- **The chain rule**: `∂/∂Y_j (p(f)) = ∑ᵢ (∂p/∂Xᵢ)(f) · ∂fᵢ/∂Y_j` for a substitution
`Xᵢ ↦ fᵢ` of polynomials in the variables `Y`. -/
theorem pderiv_aeval (f : σ → MvPolynomial τ R) (j : τ) (p : MvPolynomial σ R) :
    pderiv j (aeval f p) = ∑ i, aeval f (pderiv i p) * pderiv j (f i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, pderiv_X, map_add,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single i (fun m _ hm ↦ by simp [hm]) (by simp)]
      simp [mul_comm]
    · refine Finset.sum_congr rfl fun m _ ↦ ?_
      ring

end MvPolynomial
