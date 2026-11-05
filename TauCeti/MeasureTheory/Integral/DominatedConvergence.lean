/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Dominated convergence away from one point

This file packages the common application of dominated convergence in which a parameterized
family is controlled and converges pointwise away from one exceptional point. When that point has
measure zero, the pointwise hypotheses supply the almost-everywhere hypotheses of the dominated
convergence theorem. It also records the convergence of integrals against cutoffs
which equal one on a closed ball and are supported in shrinking larger balls, and against cutoffs
which equal one on balls exhausting a normed space.

## Main declarations

* `TauCeti.tendsto_integral_mul_of_dominated_away`: dominated convergence for a family multiplied
  by a fixed weight, with domination and convergence away from a null point.
* `TauCeti.tendsto_integral_smul_of_cutoff`: integrals against cutoffs equal to one on
  `closedBall x r` and vanishing off `ball x (r + h)` tend to the integral over `closedBall x r` as
  `h → 0⁺`.
* `TauCeti.tendsto_integral_smul_of_eq_one_ball`: integrals against `[0, 1]`-valued cutoffs equal
  to one on `ball 0 (R i)` with `R i → ∞` tend to the integral over the whole space.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology Set Metric Function

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Dominated convergence away from one point.** Suppose `K i` is eventually a.e.-strongly
measurable, `w` is a.e.-strongly measurable, and `K i` is eventually dominated by `K₀` and
converges to it away from a point `x₀` with `μ {x₀} = 0`. If `K₀ * w` is integrable, then the
integrals of `K i * w` converge to the integral of `K₀ * w`.

The exceptional point is useful for regularizations of singular kernels. The statement is for an
arbitrary countably generated filter and an arbitrary measure space.
-/
theorem tendsto_integral_mul_of_dominated_away {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {x₀ : α} (hx₀ : μ {x₀} = 0) {K : ι → α → ℝ} {K₀ w : α → ℝ}
    (hw : AEStronglyMeasurable w μ) (hK : ∀ᶠ i in l, AEStronglyMeasurable (K i) μ)
    (hint : Integrable (fun x ↦ K₀ x * w x) μ)
    (hle : ∀ᶠ i in l, ∀ x ≠ x₀, |K i x| ≤ |K₀ x|)
    (hlim : ∀ x ≠ x₀, Tendsto (fun i ↦ K i x) l (𝓝 (K₀ x))) :
    Tendsto (fun i ↦ ∫ x, K i x * w x ∂μ) l (𝓝 (∫ x, K₀ x * w x ∂μ)) := by
  have hae : ∀ᵐ x ∂μ, x ≠ x₀ := compl_mem_ae_iff.2 hx₀
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖K₀ x * w x‖)
    (hK.mono fun _ hi ↦ hi.mul hw) ?_ hint.norm ?_
  · filter_upwards [hle] with i hi
    filter_upwards [hae] with x hx
    simp only [norm_mul, Real.norm_eq_abs]
    gcongr ?_ * _
    exact hi x hx
  · filter_upwards [hae] with x hx
    exact (hlim x hx).mul_const _

/-- **Dominated convergence for shrinking cutoffs.** Let `f : α → E` be measurable, and let the
cutoffs `ψ h : E → ℝ`, for `h > 0`, be measurable with absolute value at most one, equal to one
on `closedBall x r` and vanishing off `ball x (r + h)`. If `g` is integrable on
`f ⁻¹' closedBall x (r + δ)` for some `δ > 0`, then the integrals of `ψ h (f y) • g y` tend to the
integral of `g` over `f ⁻¹' closedBall x r` as `h → 0⁺`. -/
theorem tendsto_integral_smul_of_cutoff {E G : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : α → E}
    (hf : Measurable f) {g : α → G} (hg : AEStronglyMeasurable g μ) {x : E} {r δ : ℝ}
    (hδ : 0 < δ) (hint : IntegrableOn g (f ⁻¹' closedBall x (r + δ)) μ)
    {ψ : ℝ → E → ℝ} (hψm : ∀ h, 0 < h → Measurable (ψ h))
    (hψle : ∀ h, 0 < h → ∀ y, |ψ h y| ≤ 1)
    (hψ1 : ∀ h, 0 < h → EqOn (ψ h) 1 (closedBall x r))
    (hψR : ∀ h, 0 < h → support (ψ h) ⊆ ball x (r + h)) :
    Tendsto (fun h => ∫ y, ψ h (f y) • g y ∂μ) (𝓝[>] 0)
      (𝓝 (∫ y in f ⁻¹' closedBall x r, g y ∂μ)) := by
  have hψ0 (h : ℝ) (hh : 0 < h) : ∀ y ∉ ball x (r + h), ψ h y = 0 :=
    support_subset_iff'.1 (hψR h hh)
  rw [← integral_indicator (measurableSet_closedBall.preimage hf)]
  refine tendsto_integral_filter_of_dominated_convergence
    ((f ⁻¹' closedBall x (r + δ)).indicator fun y => ‖g y‖) ?_ ?_
    (IntegrableOn.integrable_indicator hint.norm (measurableSet_closedBall.preimage hf)) ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact ((hψm h hh).comp hf).aestronglyMeasurable.smul hg
  -- The cutoffs are bounded by one and vanish off `closedBall x (r + δ)` once `h ≤ δ`.
  · filter_upwards [Ioc_mem_nhdsGT hδ] with h hh
    refine .of_forall fun y => ?_
    by_cases hy : f y ∈ closedBall x (r + δ)
    · rw [indicator_of_mem (mem_preimage.2 hy), norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hψle h hh.1 _)
    · rw [indicator_of_notMem (mt mem_preimage.1 hy),
        hψ0 h hh.1 (f y) fun h' => hy (ball_subset_closedBall
          (ball_subset_ball (by linarith [hh.2]) h')), zero_smul, norm_zero]
  -- Pointwise, the cutoffs tend to the indicator of `closedBall x r`.
  · refine .of_forall fun y => tendsto_const_nhds.congr' ?_
    by_cases hy : f y ∈ closedBall x r
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simp [indicator_of_mem (mem_preimage.2 hy), hψ1 h hh hy]
    · filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 (not_le.1 hy))] with h hh
      simp [indicator_of_notMem (mt mem_preimage.1 hy),
        hψ0 h hh.1 (f y) fun h' => (mem_ball.1 h').not_ge (by linarith [hh.2])]

/-- **Integrals against cutoffs exhaust the space.** If the cutoffs `χ i` take values in `[0, 1]`
and equal `1` on `ball 0 (R i)` with `R i → ∞`, then `∫ χ i • f → ∫ f` for integrable `f`. -/
theorem tendsto_integral_smul_of_eq_one_ball {E F : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {χ : ι → E → ℝ} {R : ι → ℝ} {μ : Measure E}
    (hR : Tendsto R l atTop) (hχm : ∀ i, AEStronglyMeasurable (χ i) μ)
    (hχ1 : ∀ i x, ‖x‖ < R i → χ i x = 1) (hχI : ∀ i x, χ i x ∈ Set.Icc (0 : ℝ) 1)
    {f : E → F} (hf : Integrable f μ) :
    Tendsto (fun i ↦ ∫ x, χ i x • f x ∂μ) l (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖)
    (.of_forall fun i ↦ (hχm i).smul hf.aestronglyMeasurable)
    (.of_forall fun i ↦ .of_forall fun x ↦ ?_) hf.norm (.of_forall fun x ↦ ?_)
  · rw [norm_smul, Real.norm_of_nonneg (hχI i x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχI i x).2
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hR.eventually_gt_atTop ‖x‖] with i hi
    rw [hχ1 i x hi, one_smul]

end TauCeti
