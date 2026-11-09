/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Distributions.Fernique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Increments along a quarter rotation

For `(x, y) ∈ E × E` and the rotation
`R θ (x, y) = (cos θ • x + sin θ • y, -sin θ • x + cos θ • y)`
(`ContinuousLinearMap.rotation`), the first coordinate of `R θ (x, y)` runs along a quarter
circle from `x` (at `θ = 0`) to `y` (at `θ = π / 2`) with velocity the second coordinate. By the
fundamental theorem of calculus, the increment of a `C¹` function `f` between `x` and `y` is

`f y - f x = ∫ θ in 0..π/2, f' (R θ (x, y)).1 (R θ (x, y)).2`.

This is the interpolation identity behind the Maurey–Pisier proof of Gaussian concentration.

## Main results

* `ContDiff.sub_eq_integral_fderiv_rotation`: the identity above.
-/

public section

open Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The Gaussian interpolation identity.** The first coordinate of the rotation of `(x, y)`
by `θ` runs from `x` (at `θ = 0`) to `y` (at `θ = π / 2`) with velocity the second coordinate,
so the increment of a `C¹` function between `x` and `y` is the integral of its derivative along
this quarter circle. -/
theorem ContDiff.sub_eq_integral_fderiv_rotation {f : E → F} (hf : ContDiff ℝ 1 f)
    (p : E × E) :
    f p.2 - f p.1 = ∫ θ in (0)..(π / 2),
      fderiv ℝ f (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2 := by
  have hd (θ : ℝ) : HasDerivAt (fun θ : ℝ ↦ f (Real.cos θ • p.1 + Real.sin θ • p.2))
      (fderiv ℝ f (ContinuousLinearMap.rotation θ p).1
        (ContinuousLinearMap.rotation θ p).2) θ := by
    have hγ := ((hasDerivAt_cos θ).smul_const p.1).add ((hasDerivAt_sin θ).smul_const p.2)
    exact (hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt θ hγ
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ ↦ hd θ)]
  · simp
  · refine Continuous.intervalIntegrable ?_ _ _
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
