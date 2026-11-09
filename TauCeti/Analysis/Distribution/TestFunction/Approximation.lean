/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Uniform approximation of continuous and `C¹` functions by test functions

Let `Ω` be an open set of a finite-dimensional real normed space `E`. Mollifying a continuous
function supported in a compact set `K` by normalized bumps of small radius gives test functions
on `Ω` supported in a fixed closed thickening of `K` that converge to it uniformly, as long as that
thickening lies in `Ω`. For a `C¹` function the derivatives of the mollifications are the
mollifications of its derivative (Mathlib's `HasCompactSupport.hasFDerivAt_convolution_right`), so
they converge uniformly as well. The construction follows Mathlib's
`MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dist_le` and
`UniformContinuous.exists_contDiff_dist_le` (in
`Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox`), with added control of the support; the
error estimate is Mathlib's `ContDiffBump.dist_normed_convolution_le`.

## Main results

* `Continuous.exists_testFunction_dist_le`: a continuous function supported in a compact set `K`
  is uniformly approximated by test functions supported in any closed thickening of `K` that lies
  in `Ω`.
* `ContDiff.exists_testFunction_dist_le_and_dist_fderiv_le`: a `C¹` function supported in a
  compact set `K` is approximated in the same way, uniformly together with its derivative.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Chapter I
  (regularization by convolution).
-/

public section

open MeasureTheory TopologicalSpace Metric Set
open scoped Distributions Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Mollifying a continuous function supported in a compact set `K` by a normalized bump of outer
radius at most `δ` gives a test function on `Ω` supported in `cthickening δ K`, as long as that
thickening lies in `Ω`. -/
private theorem exists_testFunction_eq_normed_convolution [MeasurableSpace E] [BorelSpace E]
    {f : E → F} (hf : Continuous f) {K : Set E} (hK : IsCompact K) (hfK : tsupport f ⊆ K)
    {δ : ℝ} (hKΩ : cthickening δ K ⊆ Ω) (ρ : ContDiffBump (0 : E)) (hρ : ρ.rOut ≤ δ) :
    ∃ φ : 𝓓(Ω, F),
      ⇑φ = ρ.normed Measure.addHaar ⋆[ContinuousLinearMap.lsmul ℝ ℝ, Measure.addHaar] f ∧
        tsupport φ ⊆ cthickening δ K := by
  set g := ρ.normed Measure.addHaar ⋆[ContinuousLinearMap.lsmul ℝ ℝ, Measure.addHaar] f
  have hgs : tsupport g ⊆ cthickening δ K := by
    have hsupp : Function.support g ⊆ thickening ρ.rOut K := by
      refine (support_convolution_subset _).trans ?_
      rw [ρ.support_normed_eq, ← ball_add_zero]
      exact add_subset_add_left ((subset_tsupport f).trans hfK)
    exact (closure_mono hsupp).trans <| (closure_thickening_subset_cthickening _ _).trans <|
      cthickening_mono hρ K
  exact ⟨⟨g, ρ.hasCompactSupport_normed.contDiff_convolution_left _ ρ.contDiff_normed
      hf.locallyIntegrable, hK.cthickening.of_isClosed_subset (isClosed_tsupport _) hgs,
      hgs.trans hKΩ⟩, rfl, hgs⟩

/-- A continuous function supported in a compact set `K` is uniformly approximated by test
functions on `Ω`, as long as a closed thickening `cthickening δ K` lies in `Ω`: for every `ε > 0`
there is a test function on `Ω`, supported in `cthickening δ K`, within `ε` of `f` everywhere. -/
theorem Continuous.exists_testFunction_dist_le {f : E → F} (hf : Continuous f) {K : Set E}
    (hK : IsCompact K) (hfK : tsupport f ⊆ K) {δ : ℝ} (hδ : 0 < δ)
    (hKΩ : cthickening δ K ⊆ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓓(Ω, F), tsupport φ ⊆ cthickening δ K ∧ ∀ x, dist (φ x) (f x) ≤ ε := by
  borelize E
  have hfc : HasCompactSupport f := hK.of_isClosed_subset (isClosed_tsupport f) hfK
  obtain ⟨η, hη, hfη⟩ :=
    Metric.uniformContinuous_iff.mp (hfc.uniformContinuous_of_continuous hf) ε hε
  -- Mollify `f` by a normalized bump of outer radius `min η δ`.
  have hr : 0 < min η δ := lt_min hη hδ
  let ρ : ContDiffBump (0 : E) := ⟨min η δ / 2, min η δ, half_pos hr, half_lt_self hr⟩
  obtain ⟨φ, hφ, hφs⟩ :=
    exists_testFunction_eq_normed_convolution hf hK hfK hKΩ ρ (min_le_right _ _)
  refine ⟨φ, hφs, fun x => ?_⟩
  rw [hφ]
  exact ρ.dist_normed_convolution_le hf.aestronglyMeasurable fun y hy =>
    (hfη ((mem_ball.mp hy).trans_le (min_le_left _ _))).le

omit [FiniteDimensional ℝ E] in
/-- A `C¹` function supported in a compact set `K` is approximated by test functions on `Ω`
uniformly together with its derivative, as long as a closed thickening `cthickening δ K` lies in
`Ω`: for every `ε > 0` there is a test function on `Ω`, supported in `cthickening δ K`, within `ε`
of `f` everywhere and whose derivative is within `ε` of `fderiv ℝ f` everywhere. -/
theorem ContDiff.exists_testFunction_dist_le_and_dist_fderiv_le {f : E → F}
    (hf : ContDiff ℝ 1 f) {K : Set E} (hK : IsCompact K) (hfK : tsupport f ⊆ K) {δ : ℝ}
    (hδ : 0 < δ) (hKΩ : cthickening δ K ⊆ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓓(Ω, F), tsupport φ ⊆ cthickening δ K ∧
      ∀ x, dist (φ x) (f x) ≤ ε ∧ dist (fderiv ℝ φ x) (fderiv ℝ f x) ≤ ε := by
  by_cases hfd : FiniteDimensional ℝ E
  swap
  · -- In infinite dimensions a compactly supported continuous function vanishes.
    have hf0 : f = 0 := by
      funext x
      by_contra hx
      obtain ⟨r, hr, hball⟩ :=
        Metric.isOpen_iff.1 (isOpen_ne_fun hf.continuous continuous_const) x hx
      have hsub : closedBall x (r / 2) ⊆ tsupport f := fun y hy ↦
        subset_closure (hball (mem_ball.2 ((mem_closedBall.1 hy).trans_lt (half_lt_self hr))))
      exact hfd (.of_isCompact_closedBall ℝ (half_pos hr)
        (hK.of_isClosed_subset isClosed_closedBall (hsub.trans hfK)))
    subst hf0
    exact ⟨0, by simp, fun x ↦ by simp [hε.le]⟩
  borelize E
  have hfc : HasCompactSupport f := hK.of_isClosed_subset (isClosed_tsupport f) hfK
  have hDf : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  obtain ⟨η₁, hη₁, hfη⟩ :=
    Metric.uniformContinuous_iff.mp (hfc.uniformContinuous_of_continuous hf.continuous) ε hε
  obtain ⟨η₂, hη₂, hDfη⟩ :=
    Metric.uniformContinuous_iff.mp ((hfc.fderiv ℝ).uniformContinuous_of_continuous hDf) ε hε
  -- Mollify `f` by a normalized bump of outer radius `r = min (min η₁ η₂) δ`.
  set r := min (min η₁ η₂) δ
  have hr : 0 < r := lt_min (lt_min hη₁ hη₂) hδ
  let ρ : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  obtain ⟨φ, hφ, hφs⟩ :=
    exists_testFunction_eq_normed_convolution hf.continuous hK hfK hKΩ ρ (min_le_right _ _)
  refine ⟨φ, hφs, fun x => ⟨?_, ?_⟩⟩
  · rw [hφ]
    exact ρ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable fun y hy =>
      (hfη ((mem_ball.mp hy).trans_le ((min_le_left _ _).trans (min_le_left _ _)))).le
  · -- The derivative of the mollification is the mollification of the derivative.
    have hD : fderiv ℝ φ x =
        (ρ.normed Measure.addHaar ⋆[ContinuousLinearMap.lsmul ℝ ℝ, Measure.addHaar]
          fderiv ℝ f) x := by
      rw [hφ, (hfc.hasFDerivAt_convolution_right _
        ρ.continuous_normed.locallyIntegrable hf x).fderiv, convolution_def, convolution_def]
      -- Both kernels multiply `fderiv ℝ f (x - t) v` by the bump value at `t`.
      refine congrArg _ (funext fun t => ContinuousLinearMap.ext fun v => ?_)
      simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.lsmul_apply,
        smul_apply]
    rw [hD]
    exact ρ.dist_normed_convolution_le hDf.aestronglyMeasurable fun y hy =>
      (hDfη ((mem_ball.mp hy).trans_le ((min_le_left _ _).trans (min_le_right _ _)))).le
