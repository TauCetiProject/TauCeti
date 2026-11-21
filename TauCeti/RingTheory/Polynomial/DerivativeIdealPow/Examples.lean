/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.DerivativeIdealPow
public import TauCeti.RingTheory.MvPolynomial.DerivativeIdealPow
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Examples for derivative divisibility in ideal powers

These examples keep the derivative order bound visible, allow an unrestricted cofactor and empty
factor families, and separate ordinary from Hasse hypotheses over the integers. The multivariate
example differentiates in a variable other than the first.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Lemma 11.14 and (11.22), p. 283.
-/

public section

namespace Polynomial

/-- Ordinary jets of `X³` through order `3` lie in `(3)`, whereas its third Hasse jet does not. -/
example :
    (∀ k ≤ 3, (derivative^[k] (X ^ 3 : ℤ[X])).eval 0 ∈ Ideal.span ({3} : Set ℤ)) ∧
      (hasseDeriv 3 (X ^ 3 : ℤ[X])).eval 0 ∉ Ideal.span ({3} : Set ℤ) := by
  constructor
  · intro k hk
    interval_cases k <;> norm_num [iterate_derivative_X_pow_eq_smul, eval_smul,
      Ideal.mem_span_singleton]
  · norm_num [X_pow_eq_monomial, hasseDeriv_monomial, Ideal.mem_span_singleton]

/-- Empty factor families contribute no ideal power, for ordinary and Hasse derivatives alike. -/
example {R : Type*} [CommSemiring R] (g : R[X]) (a : R) (J : Ideal R) (K : ℕ) :
    (∀ k ≤ K, (derivative^[k] (g * ∏ _ : Fin 0, (0 : R[X]))).eval a ∈ J ^ 0) ∧
      (∀ k ≤ K, (hasseDeriv k (g * ∏ _ : Fin 0, (0 : R[X]))).eval a ∈ J ^ 0) :=
  ⟨derivative_prod_mem_ideal_pow (fun _ : Fin 0 ↦ 0) g a J K (fun i ↦ Fin.elim0 i),
    hasseDeriv_prod_mem_ideal_pow (fun _ : Fin 0 ↦ 0) g a J K (fun i ↦ Fin.elim0 i)⟩

/-- A zero factor satisfies both sets of hypotheses at every order and with every cofactor. -/
example {R : Type*} [CommSemiring R] (g : R[X]) (a : R) (J : Ideal R) (K : ℕ) :
    (∀ k ≤ K, (derivative^[k] (g * ∏ _ : Fin 1, (0 : R[X]))).eval a ∈ J ^ 1) ∧
      (∀ k ≤ K, (hasseDeriv k (g * ∏ _ : Fin 1, (0 : R[X]))).eval a ∈ J ^ 1) :=
  ⟨derivative_prod_mem_ideal_pow (fun _ : Fin 1 ↦ 0) g a J K (by simp),
    hasseDeriv_prod_mem_ideal_pow (fun _ : Fin 1 ↦ 0) g a J K (by simp)⟩

/-- At order bound zero two vanishing linear factors contribute `(0)²`. Their second derivative
at zero is `2 ∉ (0)²`, so the conclusion need not hold at every order without hypotheses through
that order. -/
example :
    (∀ k ≤ 0, (derivative^[k] (1 * ∏ _ : Fin 2, (X : ℤ[X]))).eval 0 ∈
      (⊥ : Ideal ℤ) ^ 2) ∧
      (derivative^[2] (1 * ∏ _ : Fin 2, (X : ℤ[X]))).eval 0 = 2 ∧
      (derivative^[2] (1 * ∏ _ : Fin 2, (X : ℤ[X]))).eval 0 ∉ (⊥ : Ideal ℤ) ^ 2 := by
  refine ⟨derivative_prod_mem_ideal_pow (fun _ : Fin 2 ↦ X) 1 0 ⊥ 0 (by simp), ?_⟩
  norm_num [Finset.prod_const, iterate_derivative_X_pow_eq_smul, eval_smul]

/-- A single linear factor satisfies the order-zero hypothesis at zero. -/
example : (derivative^[0] (1 * ∏ _ : Fin 1, (X : ℤ[X]))).eval 0 ∈ (⊥ : Ideal ℤ) ^ 1 :=
  derivative_prod_mem_ideal_pow (fun _ : Fin 1 ↦ X) 1 0 ⊥ 0 (by simp) 0 le_rfl

/-- The same linear factor fails the hypothesis when the order bound is increased to one. -/
example : (derivative^[1] (X : ℤ[X])).eval 0 ∉ (⊥ : Ideal ℤ) := by
  simp

/-- The cofactor `X⁵` needs no derivative hypothesis: the single factor `X⁴` supplies one power
of the zero ideal through order `3`. -/
example : ∀ k ≤ 3,
    (derivative^[k] (X ^ 5 * ∏ _ : Fin 1, (X ^ 4 : ℤ[X]))).eval 0 ∈ (⊥ : Ideal ℤ) ^ 1 := by
  apply derivative_prod_mem_ideal_pow (fun _ : Fin 1 ↦ X ^ 4) (X ^ 5) 0 ⊥ 3
  intro _ k hk
  interval_cases k <;> norm_num [iterate_derivative_X_pow_eq_smul, eval_smul]

/-- The Hasse product theorem admits the same nonconstant cofactor and finite order bound. -/
example : ∀ k ≤ 3,
    (hasseDeriv k (X ^ 5 * ∏ _ : Fin 1, (X ^ 4 : ℤ[X]))).eval 0 ∈ (⊥ : Ideal ℤ) ^ 1 := by
  apply hasseDeriv_prod_mem_ideal_pow (fun _ : Fin 1 ↦ X ^ 4) (X ^ 5) 0 ⊥ 3
  intro _ k hk
  interval_cases k <;> norm_num [X_pow_eq_monomial, hasseDeriv_monomial]

end Polynomial

namespace MvPolynomial

/-- Two factors in the third variable, evaluated at `(7, 7, 0)`, give the square of the zero ideal
at order zero even with the nonconstant cofactor in the first variable. -/
example : ∀ k ≤ 0,
    eval ![7, 7, 0] ((pderiv (2 : Fin 3))^[k]
      (X 0 * ∏ _ : Fin 2, (X 2 : MvPolynomial (Fin 3) ℤ))) ∈ (⊥ : Ideal ℤ) ^ 2 := by
  apply pderiv_prod_mem_ideal_pow (2 : Fin 3) (fun _ : Fin 2 ↦ X 2) (X 0) ![7, 7, 0] ⊥ 0
  simp

/-- The second partial derivative in that third variable evaluates to `14`, outside `(0)²`,
so the finite order bound matters. -/
example :
    eval ![7, 7, 0] ((pderiv (2 : Fin 3))^[2]
      (X 0 * ∏ _ : Fin 2, (X 2 : MvPolynomial (Fin 3) ℤ))) = 14 ∧
      eval ![7, 7, 0] ((pderiv (2 : Fin 3))^[2]
        (X 0 * ∏ _ : Fin 2, (X 2 : MvPolynomial (Fin 3) ℤ))) ∉ (⊥ : Ideal ℤ) ^ 2 := by
  norm_num [Finset.prod_const, Function.iterate_succ_apply, pderiv_mul, pderiv_pow, pderiv_X]

end MvPolynomial
