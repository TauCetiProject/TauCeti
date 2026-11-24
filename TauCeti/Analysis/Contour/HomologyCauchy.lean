/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import TauCeti.Analysis.Contour.Cauchy.IntegralFormula
import TauCeti.Analysis.Contour.Curve.Distance
import TauCeti.Analysis.Contour.Dixon.FunctionDiff
import TauCeti.Analysis.Contour.Dixon.Liouville
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The homology Cauchy theorem and integral formula, via Dixon's argument

Let `f` be holomorphic on an open set `U` and let `γ` be a closed absolutely continuous curve in `U`
that is null-homologous there. Dixon's argument in `Dixon.Liouville` (`dixonFunction_eq_zero`)
proves that the glued Dixon function of `f` along `γ` vanishes identically, and
`Cauchy.IntegralFormula` extracts two algebraic consequences from its vanishing at a single point
(`dixonH2_eq_windingNumber_mul_f_of_dixonFunction_eq_zero` and
`intervalIntegral_deriv_smul_eq_zero_of_dixonFunction_eq_zero`). This file discharges the vanishing
hypothesis and records the two resulting statements:

* `cauchyIntegralFormula_nullHomologous` — **Cauchy's integral formula in homology form**: for a
  point `z` off the curve,
  `∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z)) = 2πi · windingNumber γ a b z · f z`.
* `homologyCauchyTheorem` — **the homology form of Cauchy's theorem**:
  `∫ t in a..b, deriv γ t • f (γ t) = 0`. The base point off the curve that Dixon's argument needs
  comes from `exists_mem_off_curve`.

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

/-- **Cauchy's integral formula, homology form.** Let `f` be holomorphic on an open set `U`, let
`γ` be a closed absolutely continuous curve in `U` that is null-homologous there, and let `z` be a
point off the curve. Then

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z)) = 2πi · n_z(γ) · f z`,

where `n_z(γ) = windingNumber γ a b z` is the generalized winding number. The Cauchy-type integral
thus determines the winding-weighted value `n_z(γ) · f z`; it determines `f z` itself only when
`n_z(γ) ≠ 0`. The point `z` need not lie in `U`: for `z ∉ U` the winding number vanishes by
null-homology and the formula says that the integral is `0`.

The companion statement without the Cauchy kernel is `TauCeti.Contour.homologyCauchyTheorem`, and
the formulas for the derivatives of `f` are
`TauCeti.Contour.cauchyIntegralFormula_iteratedDeriv_nullHomologous`. -/
theorem cauchyIntegralFormula_nullHomologous {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b) (hnull : IsNullHomologous γ a b U)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z))
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z * f z := by
  have hderiv_int := hγ.intervalIntegrable_deriv_of_finiteDimensional
  -- Dixon's function vanishes at `z`. On `U` that is the formula, by the `h₁`/`h₂` identity; off
  -- `U` it says that the Cauchy-type integral `dixonH2` vanishes, and so does the winding number.
  have h_zero := dixonFunction_eq_zero hU hf hγ hγU hclosed hnull z
  have hH2 : dixonH2 f γ a b z = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z * f z := by
    by_cases hzU : z ∈ U
    · exact dixonH2_eq_windingNumber_mul_f_of_dixonFunction_eq_zero hγ.continuousOn hzU hoff h_zero
        (cauchy_integrand_intervalIntegrable hf.continuousOn hγ.continuousOn hγU hderiv_int hoff)
        (intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn hoff hderiv_int)
    · rw [dixonFunction_eq_dixonH2 hzU] at h_zero
      rw [h_zero, isNullHomologous_iff.mp hnull z hzU]
      simp
  rw [← hH2, dixonH2_def]
  exact intervalIntegral.integral_congr fun t _ ↦ by rw [smul_eq_mul, mul_comm]

/-- **The homology Cauchy theorem.** Let `γ` be a closed absolutely continuous curve on
`[[a, b]]`, null-homologous in an open set `Ω` containing it, and let `f` be holomorphic on `Ω`.
Then the contour integral of `f` along `γ` vanishes: `∫ t in a..b, deriv γ t • f (γ t) = 0`. -/
theorem homologyCauchyTheorem {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_ac : AbsolutelyContinuousOnInterval γ a b) (hγ : ∀ t ∈ uIcc a b, γ t ∈ Ω)
    (hclosed : γ a = γ b) (hf : DifferentiableOn ℂ f Ω) (hnull : IsNullHomologous γ a b Ω) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 := by
  have hγ_cont := hγ_ac.continuousOn
  have hderiv_int := hγ_ac.intervalIntegrable_deriv_of_finiteDimensional
  -- Dixon's argument. The compact curve image cannot exhaust the open `Ω`, which gives a base
  -- point `w₀ ∈ Ω` off the curve. The glued Dixon function of `(· - w₀) * f` vanishes identically,
  -- and its vanishing at `w₀` reads `∫ t in a..b, deriv γ t • f (γ t) = 0`.
  -- Mathlib keeps path-connectedness of real vector spaces out of instance search.
  have : PathConnectedSpace ℂ := IsTopologicalAddGroup.pathConnectedSpace
  obtain ⟨w₀, hw₀Ω, hw₀off⟩ := exists_mem_off_curve hΩ hγ_cont hγ
  have hg : DifferentiableOn ℂ (fun z ↦ (z - w₀) * f z) Ω := by
    fun_prop
  exact intervalIntegral_deriv_smul_eq_zero_of_dixonFunction_eq_zero hγ_cont w₀ hw₀Ω hw₀off
    (dixonFunction_eq_zero hΩ hg hγ_ac hγ hclosed hnull w₀)
    (hderiv_int.smul_continuousOn (hf.continuousOn.comp hγ_cont hγ))
    (intervalIntegrable_inv_sub_mul_deriv hγ_cont hw₀off hderiv_int)

end TauCeti.Contour

end
