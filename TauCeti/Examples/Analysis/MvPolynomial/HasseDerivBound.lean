/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.MvPolynomial.HasseDerivBound

/-!
# Examples of bounds on evaluated multivariate Hasse derivatives

For `F = Z W` the product-binomial bound on `∂_Z^[1] F (2, 3) = 3` is
`choose 1 1 · 2⁰ · 3¹ = 3`, an equality.
-/

open Finset

namespace TauCeti.MvHasseDerivBoundExample

open MvPolynomial

example : ‖eval ![(2 : ℂ), 3] (hasseDeriv (Finsupp.single 0 1) (X 0 * X 1))‖ ≤ 3 := by
  have hF : (X 0 * X 1 : MvPolynomial (Fin 2) ℂ) ∈
      restrictSupport ℂ (({Finsupp.single 0 1 + Finsupp.single 1 1} : Finset (Fin 2 →₀ ℕ)) :
        Set (Fin 2 →₀ ℕ)) := by
    rw [X, X, monomial_mul_monomial, one_mul, mem_restrictSupport_iff]
    exact support_monomial_subset.trans (by simp)
  refine (norm_eval_hasseDeriv_le hF (H := 1) (fun μ hμ ↦ ?_) (A := ![2, 3])
    (fun s ↦ by fin_cases s <;> simp) _).trans_eq ?_
  · rw [mem_singleton.1 hμ, X, X, monomial_mul_monomial, one_mul, coeff_monomial]; simp
  · simp [Fin.prod_univ_two]

end TauCeti.MvHasseDerivBoundExample
