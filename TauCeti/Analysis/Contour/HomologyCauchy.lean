/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.CauchyIntegralFormula
public import TauCeti.Analysis.Contour.DixonFunctionDiff
public import TauCeti.Analysis.Contour.DixonLiouville

/-!
# Homology Cauchy consequences of Dixon's theorem

Dixon's argument in `DixonLiouville` proves that the glued Dixon function vanishes for a closed
null-homologous curve. `CauchyIntegralFormula` then extracts two algebraic consequences from
pointwise vanishing. This file packages the direct null-homologous forms:

* `dixonH2_eq_windingNumber_mul_f_of_nullHomologous` — Cauchy's integral formula at an off-curve
  point of the domain.
* `homologyCauchyTheorem_of_point_off_curve` — the contour integral of a holomorphic function
  around such a closed null-homologous curve is zero, assuming an off-curve point in the domain is
  supplied.

The explicit off-curve point hypothesis is the final local form before the full global homology
Cauchy theorem: removing it requires a separate geometric existence lemma for the domain minus the
curve. This file does not assert that existence theorem.

## Provenance

These are the final assembly steps of Dixon's proof, migrated from the AINTLIB
`LeanModularForms` development (`DixonTheorem.lean`) and restated for the raw curve
`γ : ℝ → ℂ` used by the contour-integration roadmap. See J. D. Dixon, *A brief proof of Cauchy's
integral theorem*, Proc. Amer. Math. Soc. 29 (1971).
-/

public section

open Complex MeasureTheory Set

open scoped Real Interval

namespace TauCeti.Contour

/-- **Null-homologous Cauchy integral formula at an off-curve point.** Let `γ` be a closed curve in
an open set `U`, continuous on `uIcc a b`, differentiable off a countable set, with
interval-integrable derivative, and null-homologous in `U`. If `f` is holomorphic on `U` and
`w ∈ U` is not on the curve, then the Cauchy-type integral evaluates to
`2πi · windingNumber γ a b w · f w`.

This is the Cauchy-integral-formula output of Dixon's vanishing theorem. The off-curve point is
kept as an explicit hypothesis; proving that such a point exists in the ambient domain is a separate
geometric prerequisite for the full global homology Cauchy theorem. -/
theorem dixonH2_eq_windingNumber_mul_f_of_nullHomologous {f : ℂ → ℂ} {U : Set ℂ}
    {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ} {w : ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_null : IsNullHomologous γ a b U) (hwU : w ∈ U) (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) :
    dixonH2 f γ a b w = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w * f w :=
  dixonH2_eq_windingNumber_mul_f_of_dixonFunction_eq_zero hγ_cont hwU hoff
    (dixonFunction_eq_zero hU hf hγ_cont hγU hderiv_int hclosed hP hγ_diff h_null w)
    (cauchy_integrand_intervalIntegrable hf.continuousOn hγ_cont hγU hderiv_int hoff)
    (intervalIntegrable_inv_sub_mul_deriv hγ_cont hoff hderiv_int)

/-- **Homology Cauchy theorem with a supplied off-curve point.** Let `γ` be a closed curve in an
open set `U`, continuous on `uIcc a b`, differentiable off a countable set, with
interval-integrable derivative, and null-homologous in `U`. If `f` is holomorphic on `U`, the usual
contour integrand is interval-integrable, and `U` contains a point `w₀` not lying on the curve, then
`∫ t in a..b, deriv γ t • f (γ t) = 0`.

The proof applies the null-homologous Cauchy integral formula to
`z ↦ (z - w₀) * f z`, whose value at `w₀` is zero. This is the immediate Dixon-theoretic
prerequisite for the roadmap's full homology Cauchy theorem; only the off-curve-point existence
step is not included here. -/
theorem homologyCauchyTheorem_of_point_off_curve {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ}
    {a b : ℝ} {P : Set ℝ} {w₀ : ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_null : IsNullHomologous γ a b U) (hw₀U : w₀ ∈ U)
    (hw₀off : ∀ t ∈ uIcc a b, γ t ≠ w₀)
    (h_int : IntervalIntegrable (fun t ↦ deriv γ t • f (γ t)) volume a b) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 := by
  have hg : DifferentiableOn ℂ (fun z ↦ (z - w₀) * f z) U := by
    fun_prop
  exact intervalIntegral_deriv_smul_eq_zero_of_dixonFunction_eq_zero hγ_cont w₀ hw₀U hw₀off
    (dixonFunction_eq_zero hU hg hγ_cont hγU hderiv_int hclosed hP hγ_diff h_null w₀)
    h_int (intervalIntegrable_inv_sub_mul_deriv hγ_cont hw₀off hderiv_int)

end TauCeti.Contour

end
