/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.BigOperators

/-!
# Real and imaginary parts of complex polynomials at real points

At a real point, the real and imaginary parts of a complex polynomial are obtained by taking
real and imaginary parts of its coefficients. These identities are shared by the semialgebraic
and measure-theoretic descriptions of real zero loci.
-/

public section

namespace MvPolynomial

variable {σ : Type*}

/-- At a real point, the real part of a complex polynomial is the evaluation of the polynomial
formed from the real parts of its coefficients. -/
theorem re_eval_ofReal (P : MvPolynomial σ ℂ) (x : σ → ℝ) :
    (eval (fun i ↦ (x i : ℂ)) P).re =
      eval x (∑ d ∈ P.support, monomial d (P.coeff d).re) := by
  have hmon (d : σ →₀ ℕ) :
      ∏ i ∈ d.support, (x i : ℂ) ^ d i = ((∏ i ∈ d.support, x i ^ d i : ℝ) : ℂ) := by
    simp only [Complex.ofReal_prod, Complex.ofReal_pow]
  rw [eval_eq]
  simp only [hmon, Complex.re_sum, Complex.re_mul_ofReal, _root_.map_sum, eval_monomial,
    Finsupp.prod]

/-- At a real point, the imaginary part of a complex polynomial is the evaluation of the
polynomial formed from the imaginary parts of its coefficients. -/
theorem im_eval_ofReal (P : MvPolynomial σ ℂ) (x : σ → ℝ) :
    (eval (fun i ↦ (x i : ℂ)) P).im =
      eval x (∑ d ∈ P.support, monomial d (P.coeff d).im) := by
  have hmon (d : σ →₀ ℕ) :
      ∏ i ∈ d.support, (x i : ℂ) ^ d i = ((∏ i ∈ d.support, x i ^ d i : ℝ) : ℂ) := by
    simp only [Complex.ofReal_prod, Complex.ofReal_pow]
  rw [eval_eq]
  simp only [hmon, Complex.im_sum, Complex.im_mul_ofReal, _root_.map_sum, eval_monomial,
    Finsupp.prod]

end MvPolynomial
