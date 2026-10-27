/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Circle.ContinuousMap
public import TauCeti.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Analytic.Basic

/-! # Integrating parameter power series over a circle

A power series with values in the continuous functions on a circle is a parameter expansion
uniform in the boundary variable. Circle integration preserves its parameter ball and
integrates each multilinear coefficient. Consequently the integrated partial sums converge
uniformly on every smaller parameter ball, including expansions restricted to a set.

The hypotheses concern the boundary expansion in its uniform norm; pointwise expansions
with no uniform control are not sufficient. The parameter space may be any complex normed
space. No analyticity in the contour variable is required. For an incomplete codomain,
Mathlib defines the integral to be zero, so the conclusions are trivial in that case.

The integrated coefficient series is the composition of `TauCeti.circleIntegralCLM` with
the original formal multilinear series.

## References

L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Filter Metric Set
open scoped ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A parameter expansion uniform on a circle can be integrated coefficient by coefficient
within a set on the same parameter ball. -/
theorem HasFPowerSeriesWithinOnBall.circleIntegral {c : ℂ} {R : ℝ}
    {f : E → ℂ → F} (hc : ∀ x, ContinuousOn (f x) (sphere c |R|))
    {p : FormalMultilinearSeries ℂ E C(sphere c |R|, F)} {s : Set E} {a : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesWithinOnBall
      (fun x => ⟨fun z => f x z, (hc x).domRestrict⟩) p s a r) :
    HasFPowerSeriesWithinOnBall (fun x => ∮ z in C(c, R), f x z)
      ((TauCeti.circleIntegralCLM c R).compFormalMultilinearSeries p) s a r := by
  convert (TauCeti.circleIntegralCLM c R).comp_hasFPowerSeriesWithinOnBall hf using 1
  funext x
  exact (TauCeti.circleIntegralCLM_eq_circleIntegral c R _ (f x) fun _ => rfl).symm

/-- A parameter expansion uniform on a circle can be integrated coefficient by coefficient
on the same parameter ball. -/
theorem HasFPowerSeriesOnBall.circleIntegral {c : ℂ} {R : ℝ}
    {f : E → ℂ → F} (hc : ∀ x, ContinuousOn (f x) (sphere c |R|))
    {p : FormalMultilinearSeries ℂ E C(sphere c |R|, F)} {a : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall (fun x => ⟨fun z => f x z, (hc x).domRestrict⟩) p a r) :
    HasFPowerSeriesOnBall (fun x => ∮ z in C(c, R), f x z)
      ((TauCeti.circleIntegralCLM c R).compFormalMultilinearSeries p) a r := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact hf.circleIntegral hc

/-- Integrated partial sums converge uniformly on every smaller parameter ball restricted
to the translated set of parameter increments, including the center. -/
theorem HasFPowerSeriesWithinOnBall.tendstoUniformlyOn_circleIntegral {c : ℂ} {R : ℝ}
    {f : E → ℂ → F} (hc : ∀ x, ContinuousOn (f x) (sphere c |R|))
    {p : FormalMultilinearSeries ℂ E C(sphere c |R|, F)} {s : Set E} {a : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesWithinOnBall
      (fun x => ⟨fun z => f x z, (hc x).domRestrict⟩) p s a r)
    {r' : ℝ≥0} (hr : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn
      (fun N y => TauCeti.circleIntegralCLM c R (p.partialSum N y))
      (fun y => ∮ z in C(c, R), f (a + y) z) atTop
      ((a + ·) ⁻¹' (insert a s) ∩ ball (0 : E) r') := by
  simpa only [ContinuousLinearMap.compFormalMultilinearSeries_partialSum] using
    (hf.circleIntegral hc).tendstoUniformlyOn hr

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
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn_circleIntegral hc hr
