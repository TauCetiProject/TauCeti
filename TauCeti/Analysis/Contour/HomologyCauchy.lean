/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Dixon.Def
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Contour.Cauchy.IntegralFormula
import TauCeti.Analysis.Contour.Curve.Distance
import TauCeti.Analysis.Contour.Dixon.FunctionDiff
import TauCeti.Analysis.Contour.Dixon.Liouville
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The homology Cauchy theorem, via Dixon's argument

Dixon's argument in `DixonLiouville` proves that the glued Dixon function vanishes for a closed
null-homologous absolutely continuous curve. `CauchyIntegralFormula` then extracts two algebraic
consequences from pointwise vanishing. This file packages the direct null-homologous forms and
assembles the theorem:

* `dixonH2_eq_windingNumber_mul_f_of_nullHomologous` — Cauchy's integral formula at an off-curve
  point.
* `homologyCauchyTheorem` — **the homology form of Cauchy's theorem**: for a closed absolutely
  continuous curve `γ`, null-homologous in an open `Ω`, and `f` holomorphic on `Ω`, the contour
  integral `∫ t in a..b, deriv γ t • f (γ t)` vanishes. The base point off the curve that Dixon's
  argument needs comes from `exists_mem_off_curve`.

Absolute continuity is the natural regularity for the contour integral
`∫ t in a..b, deriv γ t • f (γ t)`: it makes `deriv γ` interval-integrable and the winding number
of a closed curve an integer off its trace, which is all Dixon's argument uses. It covers every
piecewise-`C¹` curve (`TauCeti.IsPiecewiseC1On.absolutelyContinuousOnInterval`) and every continuous
curve that is differentiable off a countable set with interval-integrable derivative
(`ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable`).

## Provenance

These are the final assembly steps of Dixon's proof, migrated from the AINTLIB
`LeanModularForms` development (`DixonTheorem.lean`) and restated for the raw curve
`γ : ℝ → ℂ`. See J. D. Dixon, *A brief proof of Cauchy's integral theorem*, Proc. Amer. Math. Soc.
29 (1971).
-/

public section

open Complex MeasureTheory Set

open scoped Real Interval

namespace TauCeti.Contour

/-- **Null-homologous Cauchy integral formula at an off-curve point.** Let `γ` be a closed
absolutely continuous curve in an open set `U`, null-homologous in `U`. If `f` is holomorphic on
`U` and `w` is a point not on the curve, then the Cauchy-type integral evaluates to
`2πi · windingNumber γ a b w · f w`. (For `w ∉ U` both sides vanish.)

This is the Cauchy-integral-formula output of Dixon's vanishing theorem. The point is kept as an
explicit hypothesis: it is any point off the curve, not necessarily in `U`; since the trace of the
curve is compact, such a point always exists. -/
theorem dixonH2_eq_windingNumber_mul_f_of_nullHomologous {f : ℂ → ℂ} {U : Set ℂ}
    {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b)
    (h_null : IsNullHomologous γ a b U) (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) :
    dixonH2 f γ a b w = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w * f w := by
  have hderiv_int := hγ.intervalIntegrable_deriv_of_finiteDimensional
  have h_zero := dixonFunction_eq_zero hU hf hγ hγU hclosed h_null w
  by_cases hwU : w ∈ U
  · exact dixonH2_eq_windingNumber_mul_f_of_dixonFunction_eq_zero hγ.continuousOn hwU hoff h_zero
      (cauchy_integrand_intervalIntegrable hf.continuousOn hγ.continuousOn hγU hderiv_int hoff)
      (intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn hoff hderiv_int)
  · rw [dixonFunction_eq_dixonH2 hwU] at h_zero
    rw [h_zero, isNullHomologous_iff.mp h_null w hwU]
    simp

/-- **The homology Cauchy theorem.** Let `γ` be a closed absolutely continuous curve on
`[[a, b]]`, null-homologous in an open set `Ω` containing it, and let `f` be holomorphic on `Ω`.
Then the contour integral of `f` along `γ` vanishes: `∫ t in a..b, deriv γ t • f (γ t) = 0`.

Dixon's argument: the compact curve image cannot exhaust the open `Ω`, giving a base point
`w₀ ∈ Ω` off the curve (`exists_mem_off_curve`); the glued Dixon function of `(· - w₀) * f`
vanishes identically by Liouville (`dixonFunction_eq_zero`); and its vanishing at `w₀` is the
Cauchy integral formula there, which reads `∫ t in a..b, deriv γ t • f (γ t) = 0`. -/
theorem homologyCauchyTheorem {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_ac : AbsolutelyContinuousOnInterval γ a b) (hγ : ∀ t ∈ uIcc a b, γ t ∈ Ω)
    (hclosed : γ a = γ b) (hf : DifferentiableOn ℂ f Ω) (hnull : IsNullHomologous γ a b Ω) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 := by
  have hγ_cont := hγ_ac.continuousOn
  have hderiv_int := hγ_ac.intervalIntegrable_deriv_of_finiteDimensional
  -- Mathlib keeps path-connectedness of real vector spaces out of instance search.
  have : PathConnectedSpace ℂ := IsTopologicalAddGroup.pathConnectedSpace
  obtain ⟨w₀, hw₀Ω, hw₀off⟩ := exists_mem_off_curve hΩ hγ_cont hγ
  have hg : DifferentiableOn ℂ (fun z ↦ (z - w₀) * f z) Ω := by
    fun_prop
  have h_int_mul : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b :=
    hderiv_int.continuousOn_mul (hf.continuousOn.comp hγ_cont hγ)
  have h_int : IntervalIntegrable (fun t ↦ deriv γ t • f (γ t)) volume a b := by
    rw [intervalIntegrable_iff] at h_int_mul ⊢
    exact h_int_mul.congr_fun (fun t _ ↦ by rw [smul_eq_mul, mul_comm]) measurableSet_uIoc
  exact intervalIntegral_deriv_smul_eq_zero_of_dixonFunction_eq_zero hγ_cont w₀ hw₀Ω hw₀off
    (dixonFunction_eq_zero hΩ hg hγ_ac hγ hclosed hnull w₀) h_int
    (intervalIntegrable_inv_sub_mul_deriv hγ_cont hw₀off hderiv_int)

end TauCeti.Contour

end
