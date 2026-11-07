/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Topology.MetricSpace.Lipschitz

import TauCeti.Analysis.Convolution.Basic

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
`ContDiffBump.shrinking`, of radii `R / (n + 1)` and `R / (2 * (n + 1))`. These bumps are all
rescalings of the first one (`ContDiffBump.shrinking_apply_eq`), so integrals against their
normalized forms reduce to one kernel (`ContDiffBump.integral_shrinking_normed_mul`).
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

/-- On a relatively compact open subdomain, a shrinking sequence of normalized bump kernels
has every translated support inside the ambient open domain. -/
theorem exists_seq_sub_tsupport_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {W Ω : TopologicalSpace.Opens E}
    (hWc : IsCompact (closure (W : Set E))) (hWΩ : closure (W : Set E) ⊆ Ω) :
    ∃ φ : ℕ → ContDiffBump (0 : E),
      Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) ∧
      ∀ n x, x ∈ (W : Set E) → ∀ y ∈ tsupport ((φ n).normed μ), x - y ∈ Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hWc.exists_cthickening_subset_open Ω.isOpen hWΩ
  refine ⟨shrinking hδ, tendsto_rOut_shrinking hδ, ?_⟩
  intro n x hx y hy
  rw [(shrinking hδ n).tsupport_normed_eq, mem_closedBall, dist_zero_right,
    rOut_shrinking] at hy
  refine hδΩ (mem_cthickening_of_dist_le _ x δ _ (subset_closure hx) ?_)
  rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
  exact hy.trans (div_le_self hδ.le (by simp))

/-- `ContDiffBump.shrinking hR n` is `ContDiffBump.shrinking hR 0` rescaled by the factor `n + 1`,
so all the bumps of the sequence are rescalings of one kernel. -/
theorem shrinking_apply_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] (hR : 0 < R) (n : ℕ) (x : E) :
    (shrinking hR n : ContDiffBump (0 : E)) x =
      (shrinking hR 0 : ContDiffBump (0 : E)) (((n : ℝ) + 1) • x) := by
  have hratio : (R / ((n : ℝ) + 1)) / (R / (2 * ((n : ℝ) + 1))) =
      (R / ((0 : ℕ) + 1 : ℝ)) / (R / (2 * ((0 : ℕ) + 1 : ℝ))) := by
    field_simp
  have hscale : (R / (2 * ((n : ℝ) + 1)))⁻¹ • x =
      (R / (2 * ((0 : ℕ) + 1 : ℝ)))⁻¹ • (((n : ℝ) + 1) • x) := by
    rw [smul_smul]
    congr 1
    field_simp
    norm_num
  simp only [ContDiffBump.apply, sub_zero, rIn_shrinking, rOut_shrinking]
  rw [hratio, hscale]

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

/-- Integrating against the normalized bump `ContDiffBump.shrinking hR n` is integrating against
the normalized bump `ContDiffBump.shrinking hR 0` after rescaling the variable by `(n + 1)⁻¹`. -/
theorem integral_shrinking_normed_mul {R : ℝ} (hR : 0 < R) (n : ℕ) (f : G → ℝ) :
    ∫ t, (shrinking (c := (0 : G)) hR n).normed μ t * f t ∂μ =
      ∫ s, (shrinking (c := (0 : G)) hR 0).normed μ s * f (((n : ℝ) + 1)⁻¹ • s) ∂μ := by
  set S : ℝ := (n : ℝ) + 1
  have hS : 0 < S := by positivity
  set d := Module.finrank ℝ G
  have hI : ∫ t, (shrinking (c := (0 : G)) hR n) t ∂μ =
      (S ^ d)⁻¹ * ∫ s, (shrinking (c := (0 : G)) hR 0) s ∂μ := by
    simp_rw [shrinking_apply_eq hR n]
    rw [Measure.integral_comp_smul_of_nonneg μ _ S (hR := hS.le), smul_eq_mul]
  have hI0 : ∫ s, (shrinking (c := (0 : G)) hR 0) s ∂μ ≠ 0 := (integral_pos _).ne'
  have hSd : S ^ d ≠ 0 := pow_ne_zero _ hS.ne'
  set g : G → ℝ := fun s => (shrinking (c := (0 : G)) hR 0).normed μ s * f (S⁻¹ • s) * S ^ d
  have hg (t : G) : (shrinking (c := (0 : G)) hR n).normed μ t * f t = g (S • t) := by
    simp only [g, normed_def]
    rw [hI, shrinking_apply_eq hR n, inv_smul_smul₀ hS.ne']
    field_simp
    exact mul_comm _ _
  calc ∫ t, (shrinking (c := (0 : G)) hR n).normed μ t * f t ∂μ = ∫ t, g (S • t) ∂μ :=
        integral_congr_ae (.of_forall hg)
    _ = (S ^ d)⁻¹ • ∫ s, g s ∂μ := Measure.integral_comp_smul_of_nonneg μ g S (hR := hS.le)
    _ = _ := by
        simp only [g, smul_eq_mul, integral_mul_const]
        field_simp

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

/-- Mollifying a locally integrable function with values in `[a, b]` by a normalized bump keeps
its values in `[a, b]`. -/
theorem normed_convolution_mem_Icc (φ : ContDiffBump (0 : G)) {w : G → ℝ} {a b : ℝ}
    (hw : LocallyIntegrable w μ) (hwab : ∀ x, w x ∈ Set.Icc a b) (x : G) :
    (φ.normed μ ⋆[lsmul ℝ ℝ, μ] w) x ∈ Set.Icc a b := by
  have hexists := (φ.hasCompactSupport_normed (μ := μ)).convolutionExists_left
    (lsmul ℝ ℝ) φ.continuous_normed hw x
  exact ⟨le_convolution_lsmul_of_forall_le (μ := μ) φ.support_normed_eq.subset
    φ.nonneg_normed φ.integral_normed hexists fun y _ => (hwab y).1,
    convolution_lsmul_le_of_forall_le (μ := μ) φ.support_normed_eq.subset
    φ.nonneg_normed φ.integral_normed hexists fun y _ => (hwab y).2⟩

open Set in
/-- Mollifying a function that is continuous on a ball by bumps with radii tending to `0`
converges uniformly on the half-radius ball. -/
theorem tendstoUniformlyOn_convolution_indicator_ball {x : G} {r : ℝ} (hr : 0 < r) {V : G → F}
    (hVc : ContinuousOn V (ball x r))
    {phi : ℕ → ContDiffBump (0 : G)} (hphi : Tendsto (fun n => (phi n).rOut) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => (ball x r).indicator V ⋆[
      (ContinuousLinearMap.lsmul ℝ ℝ).flip, μ] (phi n).normed μ)
      ((ball x r).indicator V) atTop (ball x (r / 2)) := by
  let Fn := fun n => (ball x r).indicator V ⋆[
    (ContinuousLinearMap.lsmul ℝ ℝ).flip, μ] (phi n).normed μ
  -- Continuity on the ball makes the truncation measurable.
  have hVm : AEStronglyMeasurable ((ball x r).indicator V) μ :=
    (aestronglyMeasurable_indicator_iff measurableSet_ball).2
      (hVc.aestronglyMeasurable measurableSet_ball)
  -- The mollifications converge locally uniformly throughout the larger ball.
  have hlocal : TendstoLocallyUniformlyOn Fn ((ball x r).indicator V) atTop (ball x r) := by
    rw [isOpen_ball.tendstoLocallyUniformlyOn_iff_forall_tendsto]
    intro y hy
    have hcont : ContinuousAt ((ball x r).indicator V) y :=
      (hVc.congr fun z hz => indicator_of_mem hz V).continuousAt (isOpen_ball.mem_nhds hy)
    have hconv : Tendsto (fun p : ℕ × G => Fn p.1 p.2) (atTop ×ˢ 𝓝 y)
        (𝓝 (((ball x r).indicator V) y)) := by
      simp only [Fn, convolution_flip]
      exact ContDiffBump.convolution_tendsto_right (hphi.comp tendsto_fst)
        (Eventually.of_forall fun _ => hVm) (hcont.tendsto.comp tendsto_snd) tendsto_snd
    apply tendsto_uniformity_iff_dist_tendsto_zero.2
    simpa only [dist_self, Function.comp_apply] using
      (hcont.tendsto.comp tendsto_snd).dist hconv
  have hsub : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (half_lt_self hr)
  exact ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_closedBall x (r / 2))).1 (hlocal.mono hsub)).mono ball_subset_closedBall

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
