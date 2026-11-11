/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Images of circles under differentiable maps

The loop `θ ↦ u(z₀ + ρ e^{iθ})` traced by a map `u : ℂ → E` along the circle of radius `ρ` about
`z₀` has speed at most `ρ ‖du‖`. Since any two points of the circle are joined by an arc of
angle at most `π`, the image of the circle has diameter at most `π ρ` times a bound on `‖du‖`
along it. Consequently, if `|z - z₀| ‖du(z)‖ → 0` as `z → z₀`, the images of the
circles about `z₀` shrink to points as their radius tends to `0`.

## Main results

* `TauCeti.diam_image_sphere_le_of_norm_fderiv_le`: if `‖du‖ ≤ M` on the circle of radius `ρ`
  about `z₀`, then the image of that circle has diameter at most `π ρ M`.
* `TauCeti.tendsto_diam_image_sphere_nhdsGT_zero_of_tendsto`: if `u` is differentiable near
  `z₀` (except possibly at `z₀`) and `|z - z₀| ‖du(z)‖ → 0` as `z → z₀`, then the diameter of
  the image of the circle of radius `ρ` about `z₀` tends to `0` as `ρ → 0`.
-/

public section

namespace TauCeti

open Complex Metric Set Filter Topology
open scoped Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℂ → E} {z₀ : ℂ}

/-- If `u : ℂ → E` is differentiable on the circle of radius `ρ ≥ 0` about `z₀`, with
`‖du‖ ≤ M` there, then the image of that circle has diameter at most `π ρ M`. -/
theorem diam_image_sphere_le_of_norm_fderiv_le {ρ M : ℝ} (hρ : 0 ≤ ρ)
    (hu : ∀ z ∈ sphere z₀ ρ, DifferentiableAt ℝ u z)
    (hM : ∀ z ∈ sphere z₀ ρ, ‖fderiv ℝ u z‖ ≤ M) :
    diam (u '' sphere z₀ ρ) ≤ π * ρ * M := by
  have hcmem (θ : ℝ) : circleMap z₀ ρ θ ∈ sphere z₀ ρ := circleMap_mem_sphere z₀ hρ θ
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM _ (hcmem 0))
  -- The loop `θ ↦ u (circleMap z₀ ρ θ)` has speed at most `ρ M`.
  have hlip (θ φ : ℝ) :
      ‖u (circleMap z₀ ρ φ) - u (circleMap z₀ ρ θ)‖ ≤ ρ * M * ‖φ - θ‖ := by
    refine convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le (f := u ∘ circleMap z₀ ρ)
      (fun x _ ↦ ((hu _ (hcmem x)).hasFDerivAt.comp_hasDerivAt x
        (hasDerivAt_circleMap z₀ ρ x)).hasDerivWithinAt) (fun x _ ↦ ?_) (mem_univ θ) (mem_univ φ)
    refine ((fderiv ℝ u _).le_opNorm _).trans ?_
    simpa [norm_circleMap_zero, abs_of_nonneg hρ, mul_comm] using
      mul_le_mul_of_nonneg_left (hM _ (hcmem x)) hρ
  refine diam_le_of_forall_dist_le (by positivity) ?_
  have hsph : range (circleMap z₀ ρ) = sphere z₀ ρ := by
    rw [range_circleMap, abs_of_nonneg hρ]
  rw [← hsph]
  rintro _ ⟨_, ⟨θ, rfl⟩, rfl⟩ _ ⟨_, ⟨φ, rfl⟩, rfl⟩
  -- Any two points of the circle are joined by an arc of angle at most `π`.
  obtain ⟨ψ, hψ, hφψ⟩ := (periodic_circleMap z₀ ρ).exists_mem_Ico Real.two_pi_pos φ (θ - π)
  rw [dist_eq_norm', hφψ]
  have h : ‖ψ - θ‖ ≤ π := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hψ.1, hψ.2]
  calc ‖u (circleMap z₀ ρ ψ) - u (circleMap z₀ ρ θ)‖ ≤ ρ * M * ‖ψ - θ‖ := hlip θ ψ
    _ ≤ ρ * M * π := mul_le_mul_of_nonneg_left h (mul_nonneg hρ hM₀)
    _ = π * ρ * M := by ring

/-- If `u : ℂ → E` is differentiable near `z₀`, except possibly at `z₀`, and
`|z - z₀| ‖du(z)‖ → 0` as `z → z₀`, then the image of the circle of radius `ρ` about `z₀` has
diameter tending to `0` as `ρ → 0⁺`. -/
theorem tendsto_diam_image_sphere_nhdsGT_zero_of_tendsto
    (hu : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℝ u z)
    (hd : Tendsto (fun z ↦ ‖z - z₀‖ * ‖fderiv ℝ u z‖) (𝓝[≠] z₀) (𝓝 0)) :
    Tendsto (fun ρ ↦ diam (u '' sphere z₀ ρ)) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨r₀, hr₀, hsub⟩ := Metric.mem_nhdsWithin_iff.1
    (hu.and (hd.eventually (gt_mem_nhds (by positivity : 0 < η / 8))))
  filter_upwards [Ioo_mem_nhdsGT hr₀] with ρ ⟨hρ₀, hρ₁⟩
  -- On the circle of radius `ρ`, `u` is differentiable with `ρ ‖du‖ < η / 8`.
  have hcirc (z : ℂ) (hz : z ∈ sphere z₀ ρ) :
      DifferentiableAt ℝ u z ∧ ρ * ‖fderiv ℝ u z‖ < η / 8 := by
    rw [← mem_sphere_iff_norm.1 hz]
    exact hsub ⟨sphere_subset_ball hρ₁ hz, ne_of_mem_sphere hz hρ₀.ne'⟩
  have hdiam := diam_image_sphere_le_of_norm_fderiv_le hρ₀.le (M := η / 8 / ρ)
    (fun z hz ↦ (hcirc z hz).1) fun z hz ↦ by
      rw [le_div_iff₀ hρ₀, mul_comm]
      exact (hcirc z hz).2.le
  rw [dist_zero_right, Real.norm_of_nonneg diam_nonneg]
  calc diam (u '' sphere z₀ ρ) ≤ π * ρ * (η / 8 / ρ) := hdiam
    _ = π / 8 * η := by field_simp
    _ < η := by nlinarith [Real.pi_le_four]

end TauCeti
