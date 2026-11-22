/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import TauCeti.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Analytic.Constructions

/-!
# Derivatives of analytic functions and of power series on balls

Mathlib's `HasFPowerSeriesOnBall.fderiv` shows that the Fréchet derivative of an analytic function
into a complete normed space is represented on the same open extended ball by `p.derivSeries`.
Specializing to one-dimensional domain `𝕜` and evaluating at `1 : 𝕜` gives the scalar-derivative
power series `∑ₙ (n + 1) • p.coeff (n + 1) • zⁿ` on `Metric.eball z₀ r`
(`HasFPowerSeriesOnBall.deriv`).

Mathlib's `AnalyticAt.fderiv` says that the derivative `fderiv 𝕜 f` of a function analytic at `x`
is analytic at `x`. Evaluating it on a vector field `ξ` analytic at `x` gives the derivative of
`f` along `ξ`, `z ↦ f'(z) (ξ z)`, which is again analytic at `x` (`AnalyticAt.fderiv_apply`).
-/

public section

open scoped ENNReal

/-- If `f : 𝕜 → E` into a complete normed space has formal power series `p` on `Metric.eball z₀ r`,
then `deriv f` has formal power series `mkPiRingSeries 𝕜 (fun n ↦ (n + 1 : 𝕜) • p.coeff (n + 1))`
on the same ball `Metric.eball z₀ r`. -/
theorem HasFPowerSeriesOnBall.deriv
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) :
    HasFPowerSeriesOnBall (deriv f)
      (TauCeti.mkPiRingSeries 𝕜 fun n ↦ ((n : 𝕜) + 1) • p.coeff (n + 1)) z₀ r := by
  convert (ContinuousLinearMap.apply 𝕜 E (1 : 𝕜)).comp_hasFPowerSeriesOnBall hf.fderiv using 1
  · ext z
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, fderiv_apply_one_eq_deriv]
  · rw [← ((ContinuousLinearMap.apply 𝕜 E (1 : 𝕜)).compFormalMultilinearSeries
      p.derivSeries).mkPiRingSeries_coeff]
    congr 1
    ext n
    simp [← Nat.cast_smul_eq_nsmul 𝕜]

/-- The derivative of a function analytic at `x` along a vector field analytic at `x` is analytic
at `x`. -/
theorem AnalyticAt.fderiv_apply
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] {f : E → F} {ξ : E → E} {x : E}
    (hf : AnalyticAt 𝕜 f x) (hξ : AnalyticAt 𝕜 ξ x) :
    AnalyticAt 𝕜 (fun z ↦ fderiv 𝕜 f z (ξ z)) x :=
  ((ContinuousLinearMap.apply 𝕜 F : E →L[𝕜] (E →L[𝕜] F) →L[𝕜] F).analyticAt_bilinear _).comp
    (hξ.prod hf.fderiv)

end
