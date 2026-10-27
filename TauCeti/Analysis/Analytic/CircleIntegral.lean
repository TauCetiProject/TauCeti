/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Circle.ContinuousMap
public import Mathlib.Analysis.Analytic.Basic

/-! # Integrating parameter power series over a circle

A power series with values in the continuous functions on a circle is a parameter expansion
uniform in the boundary variable. Circle integration preserves its parameter ball and
integrates each multilinear coefficient. Consequently the integrated partial sums converge
uniformly on every smaller parameter ball.

The hypotheses concern the boundary expansion in its uniform norm; pointwise expansions
with no uniform control are not sufficient. The parameter space may be any complex normed
space, and the codomain need not be complete. No analyticity in the contour variable is
required.

The construction uses `ContinuousLinearMap.comp_hasFPowerSeriesOnBall` and
`TauCeti.circleIntegralCLM`, rather than a second construction of analytic contour integrals.

## References

L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Filter Metric Set
open scoped ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A parameter expansion uniform on a circle can be integrated coefficient by coefficient
on the same parameter ball. -/
theorem HasFPowerSeriesOnBall.circleIntegral {c : ℂ} {R : ℝ}
    {f : E → ℂ → F} (hc : ∀ x, ContinuousOn (f x) (sphere c |R|))
    {p : FormalMultilinearSeries ℂ E C(sphere c |R|, F)} {a : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall (fun x => ⟨fun z => f x z, (hc x).domRestrict⟩) p a r) :
    HasFPowerSeriesOnBall (fun x => ∮ z in C(c, R), f x z)
      ((TauCeti.circleIntegralCLM c R).compFormalMultilinearSeries p) a r := by
  convert (TauCeti.circleIntegralCLM c R).comp_hasFPowerSeriesOnBall hf using 1
  funext x
  exact (TauCeti.circleIntegralCLM_eq_circleIntegral c R _ (f x) fun _ => rfl).symm

/-- Integrated coefficients have the same degree-wise norm bound, multiplied by the
circumference. In particular integration does not shrink the convergence radius. -/
theorem FormalMultilinearSeries.norm_circleIntegral_le {c : ℂ} {R : ℝ}
    (p : FormalMultilinearSeries ℂ E C(sphere c |R|, F)) (n : ℕ) :
    ‖((TauCeti.circleIntegralCLM c R).compFormalMultilinearSeries p) n‖ ≤
      2 * Real.pi * |R| * ‖p n‖ := by
  exact ((TauCeti.circleIntegralCLM c R).norm_compContinuousMultilinearMap_le (p n)).trans
    (mul_le_mul_of_nonneg_right (TauCeti.norm_circleIntegralCLM_le c R) (norm_nonneg _))

/-- Partial sums of the integrated parameter series converge uniformly on every smaller
parameter ball. -/
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn_circleIntegral {c : ℂ} {R : ℝ}
    {f : E → ℂ → F} (hc : ∀ x, ContinuousOn (f x) (sphere c |R|))
    {p : FormalMultilinearSeries ℂ E C(sphere c |R|, F)} {a : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall (fun x => ⟨fun z => f x z, (hc x).domRestrict⟩) p a r)
    {r' : ℝ≥0} (hr : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn
      (fun N y => TauCeti.circleIntegralCLM c R (p.partialSum N y))
      (fun y => ∮ z in C(c, R), f (a + y) z) atTop (ball (0 : E) r') := by
  convert (hf.circleIntegral hc).tendstoUniformlyOn hr using 1
  funext N y
  simp [FormalMultilinearSeries.partialSum]
