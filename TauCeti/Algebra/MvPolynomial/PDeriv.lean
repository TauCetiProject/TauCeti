/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The chain rule for partial derivatives of multivariate polynomials

Substituting polynomials `fᵢ ∈ R[Y_τ]` for the variables `Xᵢ` of `p ∈ R[X_σ]` and differentiating
with respect to `Y_j` obeys the chain rule

`∂/∂Y_j (p(f)) = ∑ᵢ (∂p/∂Xᵢ)(f) · ∂fᵢ/∂Y_j`,

where the sum runs over any finite set of indices containing the variables of `p`.

## Main results

* `MvPolynomial.pderiv_aeval`: the chain rule, summed over all variables of a finite type.
* `MvPolynomial.pderiv_aeval_of_vars_subset`: the chain rule, summed over a finite set containing
  the variables of `p`.
-/

public section

namespace MvPolynomial

variable {R σ τ : Type*} [CommSemiring R]

/-- **The chain rule**: `∂/∂Y_j (p(f)) = ∑ᵢ (∂p/∂Xᵢ)(f) · ∂fᵢ/∂Y_j` for a substitution
`Xᵢ ↦ fᵢ` of polynomials in the variables `Y`. -/
theorem pderiv_aeval [Fintype σ] (f : σ → MvPolynomial τ R) (j : τ) (p : MvPolynomial σ R) :
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

/-- **The chain rule** over an arbitrary type of variables:
`∂/∂Y_j (p(f)) = ∑ᵢ (∂p/∂Xᵢ)(f) · ∂fᵢ/∂Y_j`, the sum running over any finite set `s` containing the
variables of `p`. -/
theorem pderiv_aeval_of_vars_subset (f : σ → MvPolynomial τ R) (j : τ) {p : MvPolynomial σ R}
    {s : Finset σ} (hs : p.vars ⊆ s) :
    pderiv j (aeval f p) = ∑ i ∈ s, aeval f (pderiv i p) * pderiv j (f i) := by
  -- Write `p` as a polynomial in the variables indexed by `s` and apply the finite chain rule.
  obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range p ((↑) : s → σ) Subtype.val_injective
    (by simpa using hs)
  rw [aeval_rename, pderiv_aeval, ← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [pderiv_rename Subtype.val_injective, aeval_rename, Function.comp_apply]

end MvPolynomial
