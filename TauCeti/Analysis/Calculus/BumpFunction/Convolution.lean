/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Uniform approximation by normalized bumps

Convolution with normalized smooth bumps whose radii tend to zero converges uniformly to
any uniformly continuous Banach-valued function. This strengthens Mathlib's pointwise
`ContDiffBump.convolution_tendsto_right_of_continuous` and allows simultaneous approximation
of the derivatives of a compactly supported smooth function.
-/

public section

open ContinuousLinearMap MeasureTheory Filter Metric
open scoped Convolution Topology Pointwise

namespace ContDiffBump

variable {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {g : G → F}

/-- The support of a normalized-bump convolution lies in the closed radius-neighborhood
of the support of the other factor, expressed as a Minkowski sum. -/
theorem tsupport_normed_convolution_subset [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (ρ : ContDiffBump (0 : G)) :
    tsupport (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) ⊆ closedBall 0 ρ.rOut + tsupport g := by
  apply closure_minimal
  · exact (support_convolution_subset _).trans
      (Set.add_subset_add (ρ.support_normed_eq.subset.trans ball_subset_closedBall) subset_closure)
  · exact (isClosed_tsupport g).add_left_of_isCompact (isCompact_closedBall _ _)

variable [μ.IsAddHaarMeasure] [CompleteSpace F]

/-- Normalized bumps of shrinking radius approximate a uniformly continuous function
uniformly on the whole space. -/
theorem tendstoUniformly_normed_convolution {ι : Type*} {l : Filter ι}
    {ρ : ι → ContDiffBump (0 : G)} (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0))
    (hg : UniformContinuous g) :
    TendstoUniformly (fun i => (ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) g l := by
  refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuous_iff.1 hg (ε / 2) (by positivity)
  filter_upwards [hρ.eventually (gt_mem_nhds hδ)] with i hi x
  rw [dist_comm]
  refine ((ρ i).dist_normed_convolution_le (μ := μ) hg.continuous.aestronglyMeasurable
    (fun y hy => (hgδ ((mem_ball.1 hy).trans hi)).le)).trans_lt ?_
  exact half_lt_self hε

end ContDiffBump
