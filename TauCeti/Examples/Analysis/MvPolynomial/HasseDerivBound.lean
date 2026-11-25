/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.MvPolynomial.HasseDerivBound
import TauCeti.Examples.Analysis.Polynomial.HasseDerivBound
import TauCeti.RingTheory.MvPolynomial.Abv.Taylor

/-!
# Examples of bounds on evaluated multivariate Hasse derivatives

For `F = Z W` the product-binomial bound on `∂_Z^[1] F (2, 3) = 3` is
`choose 1 1 · 2⁰ · 3¹ = 3`, an equality.

The bound of `AbsoluteValue.apply_eval_hasseDeriv_le` on `1 + Z + Z²` in `MvPolynomial (Fin 1) ℂ`
at `1`, with partial degree bound `L = 2` and coefficient bound `B = 1`, is
`1 · 3 · (2 · 1)² = 12`, the same as the coarse univariate bound.
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

example : IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)
    (eval ![1] (hasseDeriv 0 (1 + X 0 + X 0 ^ 2 : MvPolynomial (Fin 1) ℂ))) ≤ 12 := by
  have hcoeff (s : Fin 1 →₀ ℕ) :
      ‖(1 + X 0 + X 0 ^ 2 : MvPolynomial (Fin 1) ℂ).coeff s‖ ≤ 1 := by
    have h : (1 + X 0 + X 0 ^ 2 : MvPolynomial (Fin 1) ℂ) =
        (uniqueAlgEquiv ℂ (Fin 1)).symm (1 + .X + .X ^ 2) := by
      simp
    rw [h, coeff_uniqueAlgEquiv_symm]
    exact HasseDerivBoundExample.norm_coeff_one_add_X_add_X_sq_le _
  have hdeg : (1 + X 0 + X 0 ^ 2 : MvPolynomial (Fin 1) ℂ).degreeOf 0 ≤ 2 := by
    refine (degreeOf_add_le _ _ _).trans
      (max_le ((degreeOf_add_le _ _ _).trans (max_le ?_ ?_)) ?_)
    · simp
    · simp
    · exact (degreeOf_pow_le _ _ _).trans (by simp)
  exact ((IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)).apply_eval_hasseDeriv_le
    (L := fun _ ↦ 2) (fun i ↦ by fin_cases i; exact hdeg) (B := 1) hcoeff ![1] 0).trans_eq
    (by norm_num)

end TauCeti.MvHasseDerivBoundExample
