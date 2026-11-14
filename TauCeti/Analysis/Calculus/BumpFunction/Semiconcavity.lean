/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox
public import TauCeti.Analysis.Convex.Semiconcavity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Smooth approximation preserving semiconcavity

Positive normalized convolution preserves a quadratic concavity bound. On smaller balls,
smooth approximations retain both the original Lipschitz constant and the Hessian upper bound.

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set ContinuousLinearMap MeasureTheory
open scoped Convolution NNReal ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Normalized positive convolution preserves a local semiconcavity constant
where all translated arguments in its support lie in the original domain. -/
theorem concaveOn_sub_norm_sq_normed_convolution_on
    {f : E → ℝ} {C : ℝ} {s T : Set E} (hs : Convex ℝ s)
    (hf : Continuous f)
    (hconc : ConcaveOn ℝ T (fun x ↦ f x - C * ‖x‖ ^ 2 / 2))
    (φ : ContDiffBump (0 : E))
    (hsub : ∀ t ∈ Metric.ball (0 : E) φ.rOut, ∀ x ∈ s, x - t ∈ T) :
    ConcaveOn ℝ s
      (fun x ↦ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x - C * ‖x‖ ^ 2 / 2) := by
  have hi : ConvolutionExists (φ.normed μ) f (lsmul ℝ ℝ) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) (φ.contDiff_normed (n := 0)).continuous.locallyIntegrable hf
  simp only [ConvolutionExists, ConvolutionExistsAt, lsmul_apply, smul_eq_mul] at hi
  have hc : ConcaveOn ℝ s
      (fun x ↦ ∫ t, φ.normed μ t * (f (x - t) - C * ‖x‖ ^ 2 / 2) ∂μ) := by
    apply integral_concaveOn_of_integrand_ae hs
    · exact Filter.Eventually.of_forall fun t ↦ by
        by_cases ht : t ∈ Metric.ball (0 : E) φ.rOut
        · simpa only [smul_eq_mul] using
            (concaveOn_sub_norm_sq_translate hconc hs t (hsub t ht)).smul
              (φ.nonneg_normed t)
        · have hz : φ.normed μ t = 0 := by
            by_contra hn
            apply ht
            rw [← φ.support_normed_eq (μ := μ)]
            exact hn
          simpa only [hz, zero_mul] using concaveOn_const (0 : ℝ) hs
    · intro x _
      simp_rw [mul_sub]
      exact (hi x).sub (φ.integrable_normed.mul_const _)
  convert hc using 1
  ext x
  simp only [convolution_def, lsmul_apply, smul_eq_mul, mul_sub]
  rw [integral_sub (hi x) (φ.integrable_normed.mul_const _),
    integral_mul_const, φ.integral_normed, one_mul]

/-- Normalized positive convolution preserves the global semiconcavity constant. -/
theorem concaveOn_sub_norm_sq_normed_convolution {f : E → ℝ} {C : ℝ}
    (hf : Continuous f)
    (hconc : ConcaveOn ℝ univ (fun x ↦ f x - C * ‖x‖ ^ 2 / 2))
    (φ : ContDiffBump (0 : E)) :
    ConcaveOn ℝ univ
      (fun x ↦ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x - C * ‖x‖ ^ 2 / 2) :=
  concaveOn_sub_norm_sq_normed_convolution_on μ convex_univ hf hconc φ
    (fun _ _ _ _ ↦ mem_univ _)

end TauCeti

namespace TauCeti

/-- Euclidean smoothing with the original Lipschitz and semiconcavity constants. -/
theorem exists_contDiff_lipschitz_semiconcave_approx
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0} {C : ℝ}
    (hf : LipschitzWith K f)
    (hconc : ConcaveOn ℝ univ (fun x ↦ f x - C * ‖x‖ ^ 2 / 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x, dist (u x) (f x) ≤ ε) ∧
      ConcaveOn ℝ univ (fun x ↦ u x - C * ‖x‖ ^ 2 / 2) := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let r : ℝ := ε / (K + 1)
  have hr : 0 < r := div_pos hε (by positivity)
  let φ : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨φ.normed μ ⋆[lsmul ℝ ℝ, μ] f, ?_,
    hf.normed_convolution φ, ?_,
    concaveOn_sub_norm_sq_normed_convolution μ hf.continuous hconc φ⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _
      φ.contDiff_normed hf.continuous.locallyIntegrable
  · intro x
    apply (φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
      (fun y hy ↦ (hf.dist_le_mul y x).trans
        (mul_le_mul_of_nonneg_left (Metric.mem_ball.1 hy).le K.coe_nonneg))).trans
    change (K : ℝ) * r ≤ ε
    have heq : r * (K + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith

/-- On a smaller ball, smoothing preserves a local Hessian upper bound as
well as a global Lipschitz bound and any prescribed uniform error. -/
theorem exists_contDiff_lipschitz_hessian_approx_on_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0} {C : ℝ}
    (hf : LipschitzWith K f) {x₀ : E} {r R : ℝ} (hrR : r < R)
    (hconc : ConcaveOn ℝ (Metric.ball x₀ R) (fun x ↦ f x - C * ‖x‖ ^ 2 / 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x, dist (u x) (f x) ≤ ε) ∧
      ∀ x ∈ Metric.ball x₀ r, ∀ v : E,
        fderiv ℝ (fderiv ℝ u) x v v ≤ C * ‖v‖ ^ 2 := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let ρ : ℝ := min (R - r) (ε / (K + 1))
  have hρ : 0 < ρ := lt_min (sub_pos.mpr hrR) (div_pos hε (by positivity))
  let φ : ContDiffBump (0 : E) := ⟨ρ / 2, ρ, half_pos hρ, half_lt_self hρ⟩
  let u := φ.normed μ ⋆[lsmul ℝ ℝ, μ] f
  have hu : ContDiff ℝ ∞ u := φ.hasCompactSupport_normed.contDiff_convolution_left _
    φ.contDiff_normed hf.continuous.locallyIntegrable
  refine ⟨u, hu, hf.normed_convolution φ, ?_, ?_⟩
  · intro x
    apply (φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
      (fun y hy ↦ (hf.dist_le_mul y x).trans
        (mul_le_mul_of_nonneg_left (Metric.mem_ball.1 hy).le K.coe_nonneg))).trans
    change (K : ℝ) * ρ ≤ ε
    have hsmall : ρ ≤ ε / (K + 1) := min_le_right _ _
    have hbound := (le_div_iff₀ (show 0 < (K : ℝ) + 1 by positivity)).mp hsmall
    nlinarith [K.coe_nonneg]
  · have hc : ConcaveOn ℝ (Metric.ball x₀ r) (fun x ↦ u x - C * ‖x‖ ^ 2 / 2) := by
      apply concaveOn_sub_norm_sq_normed_convolution_on μ (convex_ball x₀ r)
        hf.continuous hconc φ
      intro t ht x hx
      have ht' : ‖t‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using ht
      have hx' : ‖x - x₀‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
      have hsmall : ρ ≤ R - r := min_le_left _ _
      rw [Metric.mem_ball, dist_eq_norm]
      have heq : x - t - x₀ = (x - x₀) - t := by abel
      rw [heq]
      exact (norm_sub_le _ _).trans_lt (by linarith)
    intro x hx v
    exact fderiv_fderiv_le_of_concaveOn_sub_norm_sq
      Metric.isOpen_ball (hu.of_le (by simp)).contDiffOn hc hx v

/-- A Lipschitz function on a ball admits smooth approximations with its
original Hessian upper bound on every strictly smaller concentric ball. -/
theorem exists_contDiff_hessian_approx_of_lipschitzOn_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0} {C : ℝ}
    {x₀ : E} {r R : ℝ} (hrR : r < R)
    (hf : LipschitzOnWith K f (Metric.ball x₀ R))
    (hconc : ConcaveOn ℝ (Metric.ball x₀ R) (fun x ↦ f x - C * ‖x‖ ^ 2 / 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x ∈ Metric.ball x₀ R, dist (u x) (f x) ≤ ε) ∧
      ∀ x ∈ Metric.ball x₀ r, ∀ v : E,
        fderiv ℝ (fderiv ℝ u) x v v ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  have hc : ConcaveOn ℝ (Metric.ball x₀ R)
      (fun x ↦ F x - C * ‖x‖ ^ 2 / 2) :=
    hconc.congr (fun x hx ↦ congrArg (fun z ↦ z - C * ‖x‖ ^ 2 / 2) (heq hx))
  obtain ⟨u, hu, hLu, herr, hess⟩ :=
    exists_contDiff_lipschitz_hessian_approx_on_ball hF hrR hc hε
  exact ⟨u, hu, hLu, fun x hx ↦ by simpa only [heq hx] using herr x, hess⟩

end TauCeti
