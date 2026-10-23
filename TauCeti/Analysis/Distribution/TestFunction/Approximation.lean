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
# Uniform approximation of continuous functions by test functions

Let `Ω` be an open set of a finite-dimensional real normed space `E`. Mollifying a continuous
function supported in a compact set `K` by normalized bumps of small radius gives test functions
on `Ω` supported in a fixed closed thickening of `K` that converge to it uniformly, as long as that
thickening lies in `Ω`. The construction follows Mathlib's
`MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dist_le` and
`UniformContinuous.exists_contDiff_dist_le` (in
`Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox`), with added control of the support; the
error estimate is Mathlib's `ContDiffBump.dist_normed_convolution_le`.

## Main results

* `Continuous.exists_testFunction_dist_le`: a continuous function supported in a compact set `K`
  is uniformly approximated by test functions supported in any closed thickening of `K` that lies
  in `Ω`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Chapter I
  (regularization by convolution).
-/

public section

open MeasureTheory TopologicalSpace Metric Set
open scoped Distributions Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

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
  set g := ρ.normed Measure.addHaar ⋆[ContinuousLinearMap.lsmul ℝ ℝ, Measure.addHaar] f
  have hgs : tsupport g ⊆ cthickening δ K := by
    have hsupp : Function.support g ⊆ thickening (min η δ) K := by
      refine (support_convolution_subset _).trans ?_
      rw [ρ.support_normed_eq, ← ball_add_zero]
      exact add_subset_add_left ((subset_tsupport f).trans hfK)
    exact (closure_mono hsupp).trans <| (closure_thickening_subset_cthickening _ _).trans <|
      cthickening_mono (min_le_right _ _) K
  refine ⟨⟨g, ρ.hasCompactSupport_normed.contDiff_convolution_left _ ρ.contDiff_normed
      hf.locallyIntegrable, hK.cthickening.of_isClosed_subset (isClosed_tsupport _) hgs,
      hgs.trans hKΩ⟩, hgs, fun x => ?_⟩
  exact ρ.dist_normed_convolution_le hf.aestronglyMeasurable fun y hy =>
    (hfη ((mem_ball.mp hy).trans_le (min_le_left _ _))).le

