/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.VonMangoldtCoeff
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Mellin
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Inversion

/-!
# First Riesz sums of twisted von Mangoldt coefficients

For a completely multiplicative ideal weight `χ`, the first Riesz sum of `χ Λ_K` has Mellin
transform `-(L'/L)(s) / (s (s - 1))`, where `L` is the Dirichlet series of `χ`. Perron–Riesz
inversion expresses the sum as a vertical-line integral of the same logarithmic derivative.
These are the prime-side identities before subtraction of the main terms of a smoothed explicit
formula. They do not require continuation of `L` to the left of its half-plane of convergence.

See H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Chapter 5, for the
Perron integral method. The Mellin identity is the ideal-weight version of the prime-sum term
in L. Alpöge's `Deduction.mellin_Gchi_of_ne_one`.
-/

public section

open Complex MeasureTheory Set
open scoped Real

namespace TauCeti.MultiplicativeIdealWeight

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)

/-- The first Riesz sum of the norm-regrouped twisted von Mangoldt coefficients has an
absolutely convergent Mellin integral equal to `-(L'/L)(s) / (s (s - 1))`. -/
theorem integrableOn_and_integral_rieszSum_vonMangoldtTransform_mul_cpow {s : ℂ}
    (hs : 1 < s.re) (hχ : idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    (IntegrableOn (fun y : ℝ ↦ rieszSum
        (normCoeff K χ.toIdealArithmeticFunction.vonMangoldtTransform) y * (y : ℂ) ^ (-s - 1))
        (Ioi 1)) ∧
    ∫ y in Ioi (1 : ℝ), rieszSum (normCoeff K χ.toIdealArithmeticFunction.vonMangoldtTransform)
        y * (y : ℂ) ^ (-s - 1) =
      -logDeriv (LSeries (normCoeff K χ.toIdealArithmeticFunction)) s / (s * (s - 1)) := by
  have h := χ.LSeriesHasSum_normCoeff_vonMangoldtTransform hχ
  exact ⟨integrableOn_rieszSum_mul_cpow hs h.LSeriesSummable,
    (integral_rieszSum_mul_cpow hs h.LSeriesSummable).trans
      (congrArg (· / (s * (s - 1))) h.LSeries_eq)⟩

/-- On a vertical line right of both `1` and the abscissa of absolute convergence, the
Perron–Riesz integral of `-L'/L` is absolutely convergent and recovers the first Riesz sum
of the norm-regrouped twisted von Mangoldt coefficients. -/
theorem integrable_and_inv_mul_integral_neg_logDeriv_mul_perronRieszKernel {y c : ℝ}
    (hy : 0 ≤ y) (hc : 1 < c) (hχ : idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < c) :
    (Integrable fun t : ℝ ↦ -logDeriv (LSeries (normCoeff K χ.toIdealArithmeticFunction))
      ((c : ℂ) + t * I) * perronRieszKernel y c t) ∧
    ((2 * π : ℝ) : ℂ)⁻¹ * (∫ t : ℝ, -logDeriv (LSeries (normCoeff K χ.toIdealArithmeticFunction))
      ((c : ℂ) + t * I) * perronRieszKernel y c t) =
      rieszSum (normCoeff K χ.toIdealArithmeticFunction.vonMangoldtTransform) y := by
  have heq (t : ℝ) := (χ.LSeriesHasSum_normCoeff_vonMangoldtTransform
    (s := (c : ℂ) + t * I) (by simpa using hχ)).LSeries_eq
  simp_rw [← heq]
  exact ⟨integrable_LSeries_mul_perronRieszKernel _ hy (zero_lt_one.trans hc).ne' hc.ne',
    inv_mul_integral_LSeries_mul_perronRieszKernel_eq_rieszSum hy hc
      (χ.LSeriesHasSum_normCoeff_vonMangoldtTransform (s := (c : ℂ))
        (by simpa using hχ)).LSeriesSummable⟩

end TauCeti.MultiplicativeIdealWeight
