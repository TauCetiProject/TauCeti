/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Complex.ExpPolynomial.Growth
import TauCeti.Analysis.Complex.ExpPolynomial.LinearIndependence
import TauCeti.Analysis.SpecialFunctions.Exp.ExponentialPolynomial

/-!
# Examples and sharpness checks for complex exponential polynomials

Worked checks and counterexamples for the growth and linear independence theorems on complex
exponential polynomials:

* evaluating `TauCeti.norm_prod_pow_mul_cexp_le` on `z ^ 2 * exp z` at `z = 1` gives
  `Real.exp 1 ≤ (1 + 1) ^ 2 * Real.exp 1`, and on the pure exponential `exp z` at `z = 1` both
  sides equal `Real.exp 1`;
* `1 - exp z` vanishes at `z = 0` while taking the nonzero value `1 - exp 1` at `z = 1`, showing
  that linear independence requires vanishing everywhere rather than at a single point;
* for `f(z) = 1 - exp(I * z)` with frequencies `0` and `I`, applying the differential operator
  `d/dz - I` eliminates the `exp(I * z)` term and leaves the nonzero constant `-I`;
* duplicate frequencies allow a nontrivial relation `(1) * exp 0 + (-1) * exp 0 = 0`, showing that
  `Set.InjOn` cannot be dropped;
* in two variables, `P₀(z) + P₁(z) exp(z₀ + I * z₁) = 0` for all `z : Fin 2 → ℂ` forces both
  `P₀ = 0` and `P₁ = 0`, and similarly in one variable for `(p 0)(z) + (p I)(z) exp(I * z) = 0`.
-/

open scoped Polynomial

namespace TauCeti.ExpPolynomialExamples

-- Growth bound on `z ^ 2 * exp z` at `z = 1`: `exp 1 ≤ (1 + 1) ^ 2 * exp 1`.
example :
    ‖(∏ v : Fin 1, (![(1 : ℂ)] v) ^ (![2] v)) *
        Complex.exp (∑ v : Fin 1, (![(1 : ℂ)] v) * (![(1 : ℂ)] v))‖ = Real.exp 1 ∧
      Real.exp 1 ≤ (1 + 1) ^ 2 * Real.exp 1 := by
  have hbound := norm_prod_pow_mul_cexp_le ![2] ![(1 : ℂ)] ![(1 : ℂ)]
  have hnorm : ‖![(1 : ℂ)]‖ = 1 := by rw [Pi.norm_def]; simp
  refine ⟨by simp [Complex.norm_exp], ?_⟩
  simpa [Complex.norm_exp, hnorm] using hbound

-- Sharpness of `norm_prod_pow_mul_cexp_le` at degree `0` (`exp z` at `z = 1`).
example :
    ‖(∏ v : Fin 1, (![(1 : ℂ)] v) ^ (![0] v)) *
        Complex.exp (∑ v : Fin 1, (![(1 : ℂ)] v) * (![(1 : ℂ)] v))‖ =
      (1 + ‖![(1 : ℂ)]‖) ^ (∑ v : Fin 1, ![0] v) *
        Real.exp ((∑ v : Fin 1, ‖![(1 : ℂ)] v‖) * ‖![(1 : ℂ)]‖) := by
  have hnorm : ‖![(1 : ℂ)]‖ = 1 := by rw [Pi.norm_def]; simp
  simp [Complex.norm_exp, hnorm]

-- Rejection test: `1 - exp z` vanishes at `z = 0` but equals `1 - exp 1 ≠ 0` at `z = 1`, so
-- vanishing at a single point does not force the coefficient polynomials to vanish.
example :
    (1 : ℂ) - Complex.exp 0 = 0 ∧ (1 : ℂ) - Complex.exp 1 ≠ 0 := by
  refine ⟨by simp, sub_ne_zero.2 fun h ↦ ?_⟩
  have h1 : (1 : ℝ) = Real.exp 1 := by
    simpa [Complex.norm_exp] using congrArg norm h
  linarith [Real.one_lt_exp_iff.2 zero_lt_one]

-- Differential-operator check: on `f(z) = 1 - exp(I * z)` (frequencies `0` and `I`), applying
-- `d/dz - I` kills `exp(I * z)` and leaves the nonzero constant `-I`.
example (z : ℂ) :
    deriv (fun w : ℂ ↦ 1 - Complex.exp (Complex.I * w)) z -
      Complex.I * (1 - Complex.exp (Complex.I * z)) = -Complex.I ∧
      (-Complex.I : ℂ) ≠ 0 := by
  have hd : HasDerivAt (fun w : ℂ ↦ 1 - Complex.exp (Complex.I * w))
      (-Complex.I * Complex.exp (Complex.I * z)) z :=
    ((hasDerivAt_const z (1 : ℂ)).fun_sub
      (((hasDerivAt_id' z).const_mul Complex.I).cexp)).congr_deriv (by ring)
  refine ⟨by rw [hd.deriv]; ring, neg_ne_zero.2 Complex.I_ne_zero⟩

-- Rejection test for `Set.InjOn`: equal frequencies allow nonzero coefficients whose sum vanishes
-- everywhere.
example :
    let w : Bool → Fin 1 → ℂ := fun _ _ ↦ 0
    let P : Bool → MvPolynomial (Fin 1) ℂ := fun b ↦ if b then 1 else -1
    (∀ z : Fin 1 → ℂ,
      ∑ b ∈ ({false, true} : Finset Bool),
        MvPolynomial.eval z (P b) * Complex.exp (∑ v, w b v * z v) = 0) ∧
      P true ≠ 0 := by
  simp

-- Positive bivariate check: `P₀(z) + P₁(z) * exp(z₀ + I * z₁) = 0` everywhere forces
-- `P₀ = 0` and `P₁ = 0`.
example (P₀ P₁ : MvPolynomial (Fin 2) ℂ)
    (h : ∀ z : Fin 2 → ℂ,
      MvPolynomial.eval z P₀ +
        MvPolynomial.eval z P₁ * Complex.exp (z 0 + Complex.I * z 1) = 0) :
    P₀ = 0 ∧ P₁ = 0 := by
  let w : Bool → Fin 2 → ℂ := fun b ↦ if b then ![1, Complex.I] else 0
  let P : Bool → MvPolynomial (Fin 2) ℂ := fun b ↦ if b then P₁ else P₀
  have hw : Set.InjOn w ({false, true} : Finset Bool) := by
    intro b₁ _ b₂ _ hb
    cases b₁ <;> cases b₂
    · rfl
    · exfalso
      simpa [w] using congrFun hb 0
    · exfalso
      simpa [w] using congrFun hb 0
    · rfl
  have hsum : ∀ z : Fin 2 → ℂ,
      ∑ b ∈ ({false, true} : Finset Bool),
        MvPolynomial.eval z (P b) * Complex.exp (∑ v, w b v * z v) = 0 := by
    intro z
    simpa [w, P, Fin.sum_univ_two] using h z
  have hzero := eq_zero_of_sum_eval_mul_cexp_of_injOn hw hsum
  exact ⟨by simpa [P] using hzero false (by simp),
    by simpa [P] using hzero true (by simp)⟩

-- Positive univariate check: `p(0)(z) + p(I)(z) * exp(I * z) = 0` everywhere forces both
-- univariate polynomials `p 0` and `p I` to vanish.
example (p : ℂ → ℂ[X])
    (h : ∀ z : ℂ, (p 0).eval z + (p Complex.I).eval z * Complex.exp (Complex.I * z) = 0) :
    p 0 = 0 ∧ p Complex.I = 0 := by
  have h0I : (0 : ℂ) ≠ Complex.I := Complex.I_ne_zero.symm
  have hsum : ∀ z : ℂ,
      ∑ c ∈ ({0, Complex.I} : Finset ℂ), (p c).eval z * Complex.exp (c * z) = 0 := by
    intro z
    simpa [Finset.sum_pair h0I] using h z
  have hzero := eq_zero_of_sum_eval_mul_cexp_eq_zero hsum
  exact ⟨hzero 0 (by simp), hzero Complex.I (by simp)⟩

end TauCeti.ExpPolynomialExamples
