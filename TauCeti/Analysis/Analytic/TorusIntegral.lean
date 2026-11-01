/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Torus.ContinuousMap
public import TauCeti.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Analytic.Basic

/-! # Integrating parameter power series over polytori

A power series with values in continuous functions on a product of circles is a parameter
expansion uniform in the boundary variables. Integrating over that torus preserves the
parameter ball and integrates each multilinear coefficient. The integrated partial sums
converge uniformly on every smaller parameter ball, also for expansions restricted to a set.

The expansion hypothesis is in the uniform norm on the whole distinguished boundary;
pointwise parameter expansions alone do not suffice. Parameters may lie in any complex
normed space, and no analyticity in the boundary variables is needed. Radii may be negative
or zero, and dimension zero is included.

These statements are the polytorus counterparts of the circle-integration laws in
`TauCeti.Analysis.Analytic.CircleIntegral`. Both use continuous linear mapping of native
formal multilinear series.

## References

L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Filter Metric Set
open scoped ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {n : ℕ}

/-- A parameter expansion uniform on a polytorus can be integrated coefficient by coefficient
within a set, on the same parameter ball. -/
theorem HasFPowerSeriesWithinOnBall.torusIntegral {c : Fin n → ℂ} {R : Fin n → ℝ}
    {f : E → (Fin n → ℂ) → F}
    (hc : ∀ x, Continuous (fun z : (i : Fin n) → sphere (c i) |R i| => f x (fun i => z i)))
    {p : FormalMultilinearSeries ℂ E C((i : Fin n) → sphere (c i) |R i|, F)}
    {s : Set E} {a : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesWithinOnBall
      (fun x => ⟨fun z => f x (fun i => z i), hc x⟩) p s a r) :
    HasFPowerSeriesWithinOnBall (fun x => ∯ z in T(c, R), f x z)
      ((TauCeti.torusIntegralCLM c R).compFormalMultilinearSeries p) s a r := by
  convert (TauCeti.torusIntegralCLM c R).comp_hasFPowerSeriesWithinOnBall hf using 1
  funext x
  exact (TauCeti.torusIntegralCLM_eq_torusIntegral c R _ (f x) fun _ => rfl).symm

/-- A parameter expansion uniform on a polytorus can be integrated coefficient by coefficient
on the same parameter ball. -/
theorem HasFPowerSeriesOnBall.torusIntegral {c : Fin n → ℂ} {R : Fin n → ℝ}
    {f : E → (Fin n → ℂ) → F}
    (hc : ∀ x, Continuous (fun z : (i : Fin n) → sphere (c i) |R i| => f x (fun i => z i)))
    {p : FormalMultilinearSeries ℂ E C((i : Fin n) → sphere (c i) |R i|, F)}
    {a : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall
      (fun x => ⟨fun z => f x (fun i => z i), hc x⟩) p a r) :
    HasFPowerSeriesOnBall (fun x => ∯ z in T(c, R), f x z)
      ((TauCeti.torusIntegralCLM c R).compFormalMultilinearSeries p) a r := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact hf.torusIntegral hc

/-- Integrated partial sums converge uniformly on every smaller parameter ball restricted
to the translated set of parameter increments, including the center. -/
theorem HasFPowerSeriesWithinOnBall.tendstoUniformlyOn_torusIntegral
    {c : Fin n → ℂ} {R : Fin n → ℝ} {f : E → (Fin n → ℂ) → F}
    (hc : ∀ x, Continuous (fun z : (i : Fin n) → sphere (c i) |R i| => f x (fun i => z i)))
    {p : FormalMultilinearSeries ℂ E C((i : Fin n) → sphere (c i) |R i|, F)}
    {s : Set E} {a : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesWithinOnBall
      (fun x => ⟨fun z => f x (fun i => z i), hc x⟩) p s a r)
    {r' : ℝ≥0} (hr : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn
      (fun N y => TauCeti.torusIntegralCLM c R (p.partialSum N y))
      (fun y => ∯ z in T(c, R), f (a + y) z) atTop
      ((a + ·) ⁻¹' (insert a s) ∩ ball (0 : E) r') := by
  simpa only [ContinuousLinearMap.compFormalMultilinearSeries_partialSum] using
    (hf.torusIntegral hc).tendstoUniformlyOn hr

/-- Partial sums of the integrated parameter series converge uniformly on every smaller
parameter ball. -/
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn_torusIntegral
    {c : Fin n → ℂ} {R : Fin n → ℝ} {f : E → (Fin n → ℂ) → F}
    (hc : ∀ x, Continuous (fun z : (i : Fin n) → sphere (c i) |R i| => f x (fun i => z i)))
    {p : FormalMultilinearSeries ℂ E C((i : Fin n) → sphere (c i) |R i|, F)}
    {a : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall
      (fun x => ⟨fun z => f x (fun i => z i), hc x⟩) p a r)
    {r' : ℝ≥0} (hr : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn
      (fun N y => TauCeti.torusIntegralCLM c R (p.partialSum N y))
      (fun y => ∯ z in T(c, R), f (a + y) z) atTop (ball (0 : E) r') := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn_torusIntegral hc hr
