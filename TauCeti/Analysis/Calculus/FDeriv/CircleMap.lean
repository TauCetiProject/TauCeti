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
`z₀` has speed at most `ρ ‖du‖`, so the image of the circle has diameter at most `2π ρ` times a
bound on `‖du‖` along it. Consequently, if `|z - z₀| ‖du(z)‖ → 0` as `z → z₀`, the images of the
circles about `z₀` shrink to points as their radius tends to `0`.

## Main results

* `TauCeti.diam_image_sphere_le_of_norm_fderiv_le`: if `‖du‖ ≤ M` on the circle of radius `ρ`
  about `z₀`, then the image of that circle has diameter at most `2π ρ M`.
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
`‖du‖ ≤ M` there, then the image of that circle has diameter at most `2π ρ M`. -/
theorem diam_image_sphere_le_of_norm_fderiv_le {ρ M : ℝ} (hρ : 0 ≤ ρ)
    (hu : ∀ z ∈ sphere z₀ ρ, DifferentiableAt ℝ u z)
    (hM : ∀ z ∈ sphere z₀ ρ, ‖fderiv ℝ u z‖ ≤ M) :
    diam (u '' sphere z₀ ρ) ≤ 2 * π * ρ * M := by
  have hcmem (θ : ℝ) : circleMap z₀ ρ θ ∈ sphere z₀ ρ := circleMap_mem_sphere z₀ hρ θ
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM _ (hcmem 0))
  -- The loop `θ ↦ u (circleMap z₀ ρ θ)` has speed at most `ρ M`.
  have hlip (θ φ : ℝ) :
      ‖u (circleMap z₀ ρ φ) - u (circleMap z₀ ρ θ)‖ ≤ ρ * M * ‖φ - θ‖ := by
    refine convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le (f := u ∘ circleMap z₀ ρ)
      (fun x _ ↦ ((hu _ (hcmem x)).hasFDerivAt.comp_hasDerivAt x
        (hasDerivAt_circleMap z₀ ρ x)).hasDerivWithinAt) (fun x _ ↦ ?_) (mem_univ θ) (mem_univ φ)
    refine ((fderiv ℝ u _).le_opNorm _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_nonneg hρ, mul_comm]
    exact mul_le_mul_of_nonneg_left (hM _ (hcmem x)) hρ
  refine diam_le_of_forall_dist_le (mul_nonneg (mul_nonneg (by positivity) hρ) hM₀) ?_
  have hsph : circleMap z₀ ρ '' Ioc 0 (2 * π) = sphere z₀ ρ := by
    rw [image_circleMap_Ioc, abs_of_nonneg hρ]
  rw [← hsph, ← image_comp]
  rintro _ ⟨θ, hθ, rfl⟩ _ ⟨φ, hφ, rfl⟩
  rw [dist_eq_norm]
  refine (hlip φ θ).trans ?_
  have h : ‖θ - φ‖ ≤ 2 * π := by
    rw [Real.norm_eq_abs, abs_sub_le_iff]
    constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2]
  calc ρ * M * ‖θ - φ‖ ≤ ρ * M * (2 * π) := mul_le_mul_of_nonneg_left h (mul_nonneg hρ hM₀)
    _ = 2 * π * ρ * M := by ring

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
    (hu.and (hd.eventually (gt_mem_nhds (by positivity : 0 < η / 16))))
  filter_upwards [Ioo_mem_nhdsGT hr₀] with ρ ⟨hρ₀, hρ₁⟩
  -- On the circle of radius `ρ`, `u` is differentiable with `ρ ‖du‖ < η / 16`.
  have hcirc (z : ℂ) (hz : z ∈ sphere z₀ ρ) :
      DifferentiableAt ℝ u z ∧ ‖z - z₀‖ * ‖fderiv ℝ u z‖ < η / 16 := by
    rw [mem_sphere] at hz
    refine hsub ⟨?_, ?_⟩
    · rw [mem_ball, hz]
      exact hρ₁
    · rintro rfl
      rw [dist_self] at hz
      exact hρ₀.ne hz
  have hdiam := diam_image_sphere_le_of_norm_fderiv_le hρ₀.le (M := η / 16 / ρ)
    (fun z hz ↦ (hcirc z hz).1) fun z hz ↦ by
      have h := (hcirc z hz).2
      rw [← dist_eq_norm, mem_sphere.1 hz] at h
      rw [le_div_iff₀ hρ₀, mul_comm]
      exact h.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg diam_nonneg]
  calc diam (u '' sphere z₀ ρ) ≤ 2 * π * ρ * (η / 16 / ρ) := hdiam
    _ = π / 8 * η := by field_simp; ring
    _ < η := by nlinarith [Real.pi_le_four]

end TauCeti
