/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Uniform approximation by normalized bumps

Convolution with normalized smooth bumps whose radii tend to zero converges uniformly to
any uniformly continuous Banach-valued function. For uniformly continuous functions, this
upgrades the pointwise convergence of Mathlib's
`ContDiffBump.convolution_tendsto_right_of_continuous` to uniform convergence, and allows
simultaneous approximation of the derivatives of a compactly supported smooth function.
Normalized-bump convolution also preserves a function's Lipschitz constant.

The file also bounds the topological support of `ρ.normed μ ⋆ g` by the Minkowski sum
`closedBall 0 ρ.rOut + tsupport g`, and provides the standard shrinking sequence of bumps
`ContDiffBump.shrinking`, of radii `R / (n + 1)` and `R / (2 * (n + 1))`.
-/

public section

open ContinuousLinearMap MeasureTheory Filter Metric
open scoped Convolution Topology Pointwise NNReal

namespace ContDiffBump

section Shrinking

variable {X : Type*} {c : X} {R : ℝ}

/-- The bumps of outer radius `R / (n + 1)` and inner radius half of that. Their radii shrink to
zero while the outer radius stays twice the inner one, as Lebesgue differentiation along
normalized bump convolutions requires. -/
noncomputable def shrinking (hR : 0 < R) (n : ℕ) : ContDiffBump c where
  rIn := R / (2 * (n + 1))
  rOut := R / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := div_lt_div_of_pos_left hR (by positivity) (by linarith)

/-- The inner radius of `ContDiffBump.shrinking`. -/
@[simp]
theorem rIn_shrinking (hR : 0 < R) (n : ℕ) :
    (shrinking hR n : ContDiffBump c).rIn = R / (2 * (n + 1)) :=
  (rfl)

/-- The outer radius of `ContDiffBump.shrinking`. -/
@[simp]
theorem rOut_shrinking (hR : 0 < R) (n : ℕ) :
    (shrinking hR n : ContDiffBump c).rOut = R / (n + 1) :=
  (rfl)

/-- The outer radius of `ContDiffBump.shrinking` is twice its inner radius. -/
theorem rOut_shrinking_eq_two_mul_rIn (hR : 0 < R) (n : ℕ) :
    (shrinking hR n : ContDiffBump c).rOut = 2 * (shrinking hR n : ContDiffBump c).rIn := by
  simp only [rOut_shrinking, rIn_shrinking]
  field_simp

/-- The radii of `ContDiffBump.shrinking` tend to zero. -/
theorem tendsto_rOut_shrinking (hR : 0 < R) :
    Tendsto (fun n : ℕ => (shrinking hR n : ContDiffBump c).rOut) atTop (𝓝 0) := by
  simp only [rOut_shrinking]
  exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

end Shrinking

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

/-- Convolution with a nonnegative normalized bump preserves the Lipschitz constant,
including for Banach-valued functions. -/
theorem LipschitzWith.normed_convolution {G F : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : G → F} {K : ℝ≥0} (hg : LipschitzWith K g)
    (ρ : ContDiffBump (0 : G)) :
    LipschitzWith K (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) := by
  have hi : ConvolutionExists (ρ.normed μ) g (lsmul ℝ ℝ) μ :=
    ρ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) ρ.integrable_normed.locallyIntegrable hg.continuous
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, convolution_def, convolution_def, ← integral_sub (hi x).integrable
    (hi y).integrable]
  calc
    ‖∫ t, lsmul ℝ ℝ (ρ.normed μ t) (g (x - t)) -
        lsmul ℝ ℝ (ρ.normed μ t) (g (y - t)) ∂μ‖
      ≤ ∫ t, ρ.normed μ t * (K * dist x y) ∂μ := by
        apply norm_integral_le_of_norm_le (ρ.integrable_normed.mul_const _)
        filter_upwards with t
        simp only [lsmul_apply, ← smul_sub, norm_smul,
          Real.norm_of_nonneg (ρ.nonneg_normed t)]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using
            hg.dist_le_mul (x - t) (y - t)) (ρ.nonneg_normed t)
    _ = K * dist x y := by rw [integral_mul_const, ρ.integral_normed, one_mul]
