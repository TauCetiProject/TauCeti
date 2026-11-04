/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Normed.Operator.Mul
public import TauCeti.Analysis.Analytic.ConvergenceRadius
public import TauCeti.MeasureTheory.Integral.Bochner.ContinuousMap

/-!
# Integrating parameter power series against `L¹` weights on compact spaces

Given a parameter family `f : W → C(X, E)` with a formal multilinear series expansion in the uniform
norm on a compact space `X`, pairing `f w` through a continuous `𝕜`-bilinear map
`B : E →L[𝕜] F →L[𝕜] G` with an integrable weight `g : X → F` and integrating against `μ` preserves
the parameter ball and integrates each multilinear coefficient
(`HasFPowerSeriesOnBall.integral_bilin`).

In particular:
* the integrated partial sums converge uniformly on every strictly smaller parameter ball
  (`HasFPowerSeriesOnBall.tendstoUniformlyOn_integral_bilin`);
* analyticity at a point or on a neighborhood transports directly through the weighted integral
  (`AnalyticAt.integral_bilin`, `AnalyticOnNhd.integral_bilin`);
* in any normed `𝕜`-algebra `A` (not necessarily commutative), both left-weighted and right-weighted
  integrals `w ↦ ∫ x, f w x * g x ∂μ` and `w ↦ ∫ x, g x * f w x ∂μ` inherit the same radius of
  convergence.
-/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal

section Bilinear

variable {X W 𝕜 E F G : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [SMulCommClass ℝ 𝕜 G]

/-- A parameter power series in `C(X, E)` within `s` can be paired through a continuous bilinear map
with an integrable weight and integrated coefficient by coefficient on the same parameter ball. -/
theorem HasFPowerSeriesWithinOnBall.integral_bilin (B : E →L[𝕜] F →L[𝕜] G)
    {f : W → C(X, E)} {p : FormalMultilinearSeries 𝕜 W C(X, E)} {s : Set W} {a : W} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesWithinOnBall f p s a r) {g : X → F} (hg : Integrable g μ) :
    HasFPowerSeriesWithinOnBall (fun w ↦ ∫ x, B (f w x) (g x) ∂μ)
      ((B.continuousMapIntegralCLM hg).compFormalMultilinearSeries p) s a r := by
  simpa [Function.comp_def] using
    (B.continuousMapIntegralCLM hg).comp_hasFPowerSeriesWithinOnBall hf

/-- A parameter power series in `C(X, E)` can be paired through a continuous bilinear map with an
integrable weight and integrated coefficient by coefficient on the same parameter ball. -/
theorem HasFPowerSeriesOnBall.integral_bilin (B : E →L[𝕜] F →L[𝕜] G)
    {f : W → C(X, E)} {p : FormalMultilinearSeries 𝕜 W C(X, E)} {a : W} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p a r) {g : X → F} (hg : Integrable g μ) :
    HasFPowerSeriesOnBall (fun w ↦ ∫ x, B (f w x) (g x) ∂μ)
      ((B.continuousMapIntegralCLM hg).compFormalMultilinearSeries p) a r := by
  simpa [Function.comp_def] using (B.continuousMapIntegralCLM hg).comp_hasFPowerSeriesOnBall hf

/-- Partial sums of a parameter series in `C(X, E)` within `s`, after weighted Bochner integration,
converge uniformly on every strictly smaller parameter ball intersected with the translated set. -/
theorem HasFPowerSeriesWithinOnBall.tendstoUniformlyOn_integral_bilin (B : E →L[𝕜] F →L[𝕜] G)
    {f : W → C(X, E)} {p : FormalMultilinearSeries 𝕜 W C(X, E)} {s : Set W} {a : W} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesWithinOnBall f p s a r) {g : X → F} (hg : Integrable g μ)
    {r' : ℝ≥0} (hr : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn
      (fun N y ↦ ∫ x, B (p.partialSum N y x) (g x) ∂μ)
      (fun y ↦ ∫ x, B (f (a + y) x) (g x) ∂μ) atTop
      ((a + ·) ⁻¹' (insert a s) ∩ ball (0 : W) r') := by
  simpa only [ContinuousLinearMap.compFormalMultilinearSeries_partialSum,
    ContinuousLinearMap.continuousMapIntegralCLM_apply] using
    (hf.integral_bilin B hg).tendstoUniformlyOn hr

/-- Partial sums of a parameter series in `C(X, E)`, after weighted Bochner integration, converge
uniformly on every strictly smaller parameter ball. -/
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn_integral_bilin (B : E →L[𝕜] F →L[𝕜] G)
    {f : W → C(X, E)} {p : FormalMultilinearSeries 𝕜 W C(X, E)} {a : W} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p a r) {g : X → F} (hg : Integrable g μ)
    {r' : ℝ≥0} (hr : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn
      (fun N y ↦ ∫ x, B (p.partialSum N y x) (g x) ∂μ)
      (fun y ↦ ∫ x, B (f (a + y) x) (g x) ∂μ) atTop (ball (0 : W) r') := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn_integral_bilin B hg hr

/-- Pairing an analytic `C(X, E)`-valued parameter family within `s` with an integrable weight and
integrating produces a function analytic within `s`. -/
theorem AnalyticWithinAt.integral_bilin (B : E →L[𝕜] F →L[𝕜] G)
    {f : W → C(X, E)} {s : Set W} {a : W} (hf : AnalyticWithinAt 𝕜 f s a)
    {g : X → F} (hg : Integrable g μ) :
    AnalyticWithinAt 𝕜 (fun w ↦ ∫ x, B (f w x) (g x) ∂μ) s a := by
  rcases hf with ⟨p, r, hp⟩
  exact (hp.integral_bilin B hg).analyticWithinAt

/-- Pairing an analytic `C(X, E)`-valued parameter family with an integrable weight and integrating
produces an analytic function at the same parameter point. -/
theorem AnalyticAt.integral_bilin (B : E →L[𝕜] F →L[𝕜] G)
    {f : W → C(X, E)} {a : W} (hf : AnalyticAt 𝕜 f a)
    {g : X → F} (hg : Integrable g μ) :
    AnalyticAt 𝕜 (fun w ↦ ∫ x, B (f w x) (g x) ∂μ) a := by
  rcases hf with ⟨p, r, hp⟩
  exact (hp.integral_bilin B hg).analyticAt

/-- Pairing an `AnalyticOn` `C(X, E)`-valued family with an integrable weight and integrating
preserves `AnalyticOn`. -/
theorem AnalyticOn.integral_bilin (B : E →L[𝕜] F →L[𝕜] G)
    {f : W → C(X, E)} {s : Set W} (hf : AnalyticOn 𝕜 f s)
    {g : X → F} (hg : Integrable g μ) :
    AnalyticOn 𝕜 (fun w ↦ ∫ x, B (f w x) (g x) ∂μ) s := by
  simpa [Function.comp_def] using (B.continuousMapIntegralCLM hg).comp_analyticOn hf

/-- Pairing an `AnalyticOnNhd` `C(X, E)`-valued family with an integrable weight and integrating
preserves `AnalyticOnNhd`. -/
theorem AnalyticOnNhd.integral_bilin (B : E →L[𝕜] F →L[𝕜] G)
    {f : W → C(X, E)} {s : Set W} (hf : AnalyticOnNhd 𝕜 f s)
    {g : X → F} (hg : Integrable g μ) :
    AnalyticOnNhd 𝕜 (fun w ↦ ∫ x, B (f w x) (g x) ∂μ) s := by
  simpa [Function.comp_def] using (B.continuousMapIntegralCLM hg).comp_analyticOnNhd hf

end Bilinear

section Algebra

variable {X W 𝕜 A : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra 𝕜 A] [SMulCommClass ℝ 𝕜 A]

/-- Integrating a `C(X, A)` power series multiplied on the right by an integrable weight in a
(possibly noncommutative) normed `𝕜`-algebra preserves the parameter ball. -/
theorem HasFPowerSeriesOnBall.integral_mul_of_integrable_right
    {f : W → C(X, A)} {p : FormalMultilinearSeries 𝕜 W C(X, A)} {a : W} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p a r) {g : X → A} (hg : Integrable g μ) :
    HasFPowerSeriesOnBall (fun w ↦ ∫ x, f w x * g x ∂μ)
      (((ContinuousLinearMap.mul 𝕜 A).continuousMapIntegralCLM hg).compFormalMultilinearSeries p)
      a r :=
  hf.integral_bilin (ContinuousLinearMap.mul 𝕜 A) hg

/-- Integrating a `C(X, A)` power series multiplied on the left by an integrable weight in a
(possibly noncommutative) normed `𝕜`-algebra preserves the parameter ball. -/
theorem HasFPowerSeriesOnBall.integral_mul_of_integrable_left
    {f : W → C(X, A)} {p : FormalMultilinearSeries 𝕜 W C(X, A)} {a : W} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p a r) {g : X → A} (hg : Integrable g μ) :
    HasFPowerSeriesOnBall (fun w ↦ ∫ x, g x * f w x ∂μ)
      (((ContinuousLinearMap.mul 𝕜 A).flip.continuousMapIntegralCLM
        hg).compFormalMultilinearSeries p) a r :=
  hf.integral_bilin (ContinuousLinearMap.mul 𝕜 A).flip hg

/-- Right-weighted Bochner integration in a normed `𝕜`-algebra preserves `AnalyticAt`. -/
theorem AnalyticAt.integral_mul_of_integrable_right
    {f : W → C(X, A)} {a : W} (hf : AnalyticAt 𝕜 f a) {g : X → A} (hg : Integrable g μ) :
    AnalyticAt 𝕜 (fun w ↦ ∫ x, f w x * g x ∂μ) a :=
  hf.integral_bilin (ContinuousLinearMap.mul 𝕜 A) hg

/-- Left-weighted Bochner integration in a normed `𝕜`-algebra preserves `AnalyticAt`. -/
theorem AnalyticAt.integral_mul_of_integrable_left
    {f : W → C(X, A)} {a : W} (hf : AnalyticAt 𝕜 f a) {g : X → A} (hg : Integrable g μ) :
    AnalyticAt 𝕜 (fun w ↦ ∫ x, g x * f w x ∂μ) a :=
  hf.integral_bilin (ContinuousLinearMap.mul 𝕜 A).flip hg

/-- Right-weighted Bochner integration in a normed `𝕜`-algebra preserves `AnalyticOnNhd`. -/
theorem AnalyticOnNhd.integral_mul_of_integrable_right
    {f : W → C(X, A)} {s : Set W} (hf : AnalyticOnNhd 𝕜 f s) {g : X → A} (hg : Integrable g μ) :
    AnalyticOnNhd 𝕜 (fun w ↦ ∫ x, f w x * g x ∂μ) s :=
  hf.integral_bilin (ContinuousLinearMap.mul 𝕜 A) hg

/-- Left-weighted Bochner integration in a normed `𝕜`-algebra preserves `AnalyticOnNhd`. -/
theorem AnalyticOnNhd.integral_mul_of_integrable_left
    {f : W → C(X, A)} {s : Set W} (hf : AnalyticOnNhd 𝕜 f s) {g : X → A} (hg : Integrable g μ) :
    AnalyticOnNhd 𝕜 (fun w ↦ ∫ x, g x * f w x ∂μ) s :=
  hf.integral_bilin (ContinuousLinearMap.mul 𝕜 A).flip hg

end Algebra
