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

The same holds for the upper half of a circle about a point `z₀` of the real axis: its points
are joined by arcs of angle at most `π` inside the half-circle, along which only derivatives
within the closed upper half-plane are needed.

## Main results

* `TauCeti.diam_image_sphere_le_of_norm_fderiv_le`: if `‖du‖ ≤ M` on the circle of radius `ρ`
  about `z₀`, then the image of that circle has diameter at most `π ρ M`.
* `TauCeti.tendsto_diam_image_sphere_nhdsGT_zero_of_tendsto`: if `u` is differentiable near
  `z₀` (except possibly at `z₀`) and `|z - z₀| ‖du(z)‖ → 0` as `z → z₀`, then the diameter of
  the image of the circle of radius `ρ` about `z₀` tends to `0` as `ρ → 0`.
* `TauCeti.diam_image_inter_sphere_le_of_norm_fderivWithin_le` and
  `TauCeti.tendsto_diam_image_inter_sphere_nhdsGT_zero_of_tendsto`: the same for the upper half
  of the circle about a point `z₀` of the real axis, for maps differentiable only within the
  closed upper half-plane. These are the half-circles about a boundary puncture of a half-disc.
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

/-- A point of the upper half of the circle of radius `ρ` about a point `z₀` of the real axis is
`circleMap z₀ ρ θ` for an angle `θ ∈ [0, π]`, namely the argument of `z - z₀`. -/
theorem exists_mem_Icc_circleMap_eq_of_mem_inter_sphere (hz₀ : z₀.im = 0) {ρ : ℝ} {z : ℂ}
    (hz : z ∈ {z : ℂ | 0 ≤ z.im} ∩ sphere z₀ ρ) :
    ∃ θ ∈ Icc 0 π, circleMap z₀ ρ θ = z := by
  refine ⟨arg (z - z₀), ⟨arg_nonneg_iff.2 (by simpa [hz₀] using hz.1), arg_le_pi _⟩, ?_⟩
  rw [circleMap, ← mem_sphere_iff_norm.1 hz.2, norm_mul_exp_arg_mul_I, add_sub_cancel]

/-- If `u : ℂ → E` is differentiable within the closed upper half-plane at the points of the
upper half of the circle of radius `ρ ≥ 0` about a point `z₀` of the real axis, with
`‖du‖ ≤ M` there, then the image of that half-circle has diameter at most `π ρ M`. -/
theorem diam_image_inter_sphere_le_of_norm_fderivWithin_le {ρ M : ℝ} (hz₀ : z₀.im = 0)
    (hρ : 0 ≤ ρ)
    (hu : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ sphere z₀ ρ, DifferentiableWithinAt ℝ u {z | 0 ≤ z.im} z)
    (hM : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ sphere z₀ ρ, ‖fderivWithin ℝ u {z | 0 ≤ z.im} z‖ ≤ M) :
    diam (u '' ({z : ℂ | 0 ≤ z.im} ∩ sphere z₀ ρ)) ≤ π * ρ * M := by
  set H : Set ℂ := {z | 0 ≤ z.im}
  have hcmem (θ : ℝ) (hθ : θ ∈ Icc 0 π) : circleMap z₀ ρ θ ∈ H ∩ sphere z₀ ρ :=
    ⟨by simpa [H, circleMap, hz₀] using
        mul_nonneg hρ (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2),
      circleMap_mem_sphere z₀ hρ θ⟩
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM _ (hcmem 0 ⟨le_rfl, Real.pi_pos.le⟩))
  -- On `[0, π]` the arc `θ ↦ u (circleMap z₀ ρ θ)` has speed at most `ρ M`.
  have hlip (θ φ : ℝ) (hθ : θ ∈ Icc 0 π) (hφ : φ ∈ Icc 0 π) :
      ‖u (circleMap z₀ ρ φ) - u (circleMap z₀ ρ θ)‖ ≤ ρ * M * ‖φ - θ‖ := by
    refine (convex_Icc 0 π).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := u ∘ circleMap z₀ ρ)
      (fun x hx ↦ (hu _ (hcmem x hx)).hasFDerivWithinAt.comp_hasDerivWithinAt x
        (hasDerivAt_circleMap z₀ ρ x).hasDerivWithinAt fun y hy ↦ (hcmem y hy).1)
      (fun x hx ↦ ?_) hθ hφ
    refine ((fderivWithin ℝ u H _).le_opNorm _).trans ?_
    simpa [norm_circleMap_zero, abs_of_nonneg hρ, mul_comm] using
      mul_le_mul_of_nonneg_left (hM _ (hcmem x hx)) hρ
  refine diam_le_of_forall_dist_le (by positivity) ?_
  rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
  obtain ⟨θ, hθ, rfl⟩ := exists_mem_Icc_circleMap_eq_of_mem_inter_sphere hz₀ hz
  obtain ⟨φ, hφ, rfl⟩ := exists_mem_Icc_circleMap_eq_of_mem_inter_sphere hz₀ hz'
  rw [dist_eq_norm']
  have h : ‖φ - θ‖ ≤ π := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2]
  calc ‖u (circleMap z₀ ρ φ) - u (circleMap z₀ ρ θ)‖ ≤ ρ * M * ‖φ - θ‖ := hlip θ φ hθ hφ
    _ ≤ ρ * M * π := mul_le_mul_of_nonneg_left h (mul_nonneg hρ hM₀)
    _ = π * ρ * M := by ring

/-- If `u : ℂ → E` is differentiable within the closed upper half-plane near a point `z₀` of the
real axis (except possibly at `z₀`), and `|z - z₀| ‖du(z)‖ → 0` as `z → z₀` in the closed upper
half-plane, then the diameter of the image of the upper half of the circle of radius `ρ` about
`z₀` tends to `0` as `ρ → 0`. -/
theorem tendsto_diam_image_inter_sphere_nhdsGT_zero_of_tendsto (hz₀ : z₀.im = 0)
    (hu : ∀ᶠ z in 𝓝[{z | 0 ≤ z.im} \ {z₀}] z₀, DifferentiableWithinAt ℝ u {z | 0 ≤ z.im} z)
    (hd : Tendsto (fun z ↦ ‖z - z₀‖ * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z‖)
      (𝓝[{z | 0 ≤ z.im} \ {z₀}] z₀) (𝓝 0)) :
    Tendsto (fun ρ ↦ diam (u '' ({z : ℂ | 0 ≤ z.im} ∩ sphere z₀ ρ))) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨r₀, hr₀, hsub⟩ := Metric.mem_nhdsWithin_iff.1
    (hu.and (hd.eventually (gt_mem_nhds (by positivity : 0 < η / 8))))
  filter_upwards [Ioo_mem_nhdsGT hr₀] with ρ ⟨hρ₀, hρ₁⟩
  -- On the half-circle of radius `ρ`, `u` is differentiable with `ρ ‖du‖ < η / 8`.
  have harc (z : ℂ) (hz : z ∈ {z : ℂ | 0 ≤ z.im} ∩ sphere z₀ ρ) :
      DifferentiableWithinAt ℝ u {z | 0 ≤ z.im} z ∧
        ρ * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z‖ < η / 8 := by
    rw [← mem_sphere_iff_norm.1 hz.2]
    exact hsub ⟨sphere_subset_ball hρ₁ hz.2, hz.1, ne_of_mem_sphere hz.2 hρ₀.ne'⟩
  have hdiam := diam_image_inter_sphere_le_of_norm_fderivWithin_le hz₀ hρ₀.le (M := η / 8 / ρ)
    (fun z hz ↦ (harc z hz).1) fun z hz ↦ by
      rw [le_div_iff₀ hρ₀, mul_comm]
      exact (harc z hz).2.le
  rw [dist_zero_right, Real.norm_of_nonneg diam_nonneg]
  calc diam (u '' ({z : ℂ | 0 ≤ z.im} ∩ sphere z₀ ρ)) ≤ π * ρ * (η / 8 / ρ) := hdiam
    _ = π / 8 * η := by field_simp
    _ < η := by nlinarith [Real.pi_le_four]

end TauCeti
