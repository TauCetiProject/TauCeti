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

* `TauCeti.norm_sub_le_of_norm_fderiv_le_circle`: if `‖du‖ ≤ L` along the arc of the circle of
  radius `ρ` about `z₀` between the angles `θ₁` and `θ₂`, then the images of its endpoints are at
  distance at most `L ρ |θ₂ - θ₁|`.
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

/-- If `u : ℂ → E` is differentiable with `‖du‖ ≤ L` along the arc of the circle of radius
`ρ ≥ 0` about `z₀` between the angles `θ₁` and `θ₂`, then the images of the endpoints of the arc
are at distance at most `L ρ |θ₂ - θ₁|`. -/
theorem norm_sub_le_of_norm_fderiv_le_circle {ρ L θ₁ θ₂ : ℝ} (hρ : 0 ≤ ρ)
    (hu : ∀ θ ∈ uIcc θ₁ θ₂, DifferentiableAt ℝ u (circleMap z₀ ρ θ))
    (hL : ∀ θ ∈ uIcc θ₁ θ₂, ‖fderiv ℝ u (circleMap z₀ ρ θ)‖ ≤ L) :
    ‖u (circleMap z₀ ρ θ₂) - u (circleMap z₀ ρ θ₁)‖ ≤ L * ρ * |θ₂ - θ₁| := by
  refine (convex_uIcc θ₁ θ₂).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun θ ↦ u (circleMap z₀ ρ θ))
    (fun θ hθ ↦ ((hu θ hθ).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_circleMap z₀ ρ θ)).hasDerivWithinAt) (fun θ hθ ↦ ?_) left_mem_uIcc
    right_mem_uIcc |>.trans_eq (by rw [Real.norm_eq_abs])
  calc _ ≤ ‖fderiv ℝ u (circleMap z₀ ρ θ)‖ * ‖circleMap 0 ρ θ * I‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ L * ρ := by
      rw [norm_mul, norm_I, mul_one, norm_circleMap_zero, abs_of_nonneg hρ]
      gcongr
      exact hL θ hθ

/-- Along a convex set `T` of angles, on which the arc `θ ↦ circleMap z₀ ρ θ` stays in `s` and
`u : ℂ → E` is differentiable within `s` with `‖du‖ ≤ M`, the points of the arc at angles at most
`π` apart have images at distance at most `π ρ M`. -/
private theorem norm_sub_circleMap_le_pi_mul {s : Set ℂ} {T : Set ℝ} {ρ M θ φ : ℝ}
    (hT : Convex ℝ T) (hρ : 0 ≤ ρ) (hTs : MapsTo (circleMap z₀ ρ) T s)
    (hu : ∀ ψ ∈ T, DifferentiableWithinAt ℝ u s (circleMap z₀ ρ ψ))
    (hM : ∀ ψ ∈ T, ‖fderivWithin ℝ u s (circleMap z₀ ρ ψ)‖ ≤ M)
    (hθ : θ ∈ T) (hφ : φ ∈ T) (hθφ : ‖φ - θ‖ ≤ π) :
    ‖u (circleMap z₀ ρ φ) - u (circleMap z₀ ρ θ)‖ ≤ π * ρ * M := by
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM θ hθ)
  -- On `T` the arc `θ ↦ u (circleMap z₀ ρ θ)` has speed at most `ρ M`.
  calc ‖u (circleMap z₀ ρ φ) - u (circleMap z₀ ρ θ)‖ ≤ ρ * M * ‖φ - θ‖ := by
        refine hT.norm_image_sub_le_of_norm_hasDerivWithin_le (f := u ∘ circleMap z₀ ρ)
          (fun x hx ↦ (hu x hx).hasFDerivWithinAt.comp_hasDerivWithinAt x
            (hasDerivAt_circleMap z₀ ρ x).hasDerivWithinAt hTs) (fun x hx ↦ ?_) hθ hφ
        refine ((fderivWithin ℝ u s _).le_opNorm _).trans ?_
        simpa [norm_circleMap_zero, abs_of_nonneg hρ, mul_comm] using
          mul_le_mul_of_nonneg_left (hM x hx) hρ
    _ ≤ ρ * M * π := mul_le_mul_of_nonneg_left hθφ (mul_nonneg hρ hM₀)
    _ = π * ρ * M := by ring

/-- Let `s ∩ sphere z₀ ρ` be pieces of circles about `z₀` whose images have diameter at most
`π ρ M` whenever `u` is differentiable within `s` on them with `‖du‖ ≤ M`. If `u` is
differentiable within `s` near `z₀` (except possibly at `z₀`) and `|z - z₀| ‖du(z)‖ → 0` as
`z → z₀` in `s`, then these diameters tend to `0` as `ρ → 0`. -/
private theorem tendsto_diam_image_inter_sphere_nhdsGT_zero_of_diam_le {s : Set ℂ}
    (hdiam : ∀ ⦃ρ M : ℝ⦄, 0 < ρ → (∀ z ∈ s ∩ sphere z₀ ρ, DifferentiableWithinAt ℝ u s z) →
      (∀ z ∈ s ∩ sphere z₀ ρ, ‖fderivWithin ℝ u s z‖ ≤ M) →
      diam (u '' (s ∩ sphere z₀ ρ)) ≤ π * ρ * M)
    (hu : ∀ᶠ z in 𝓝[s \ {z₀}] z₀, DifferentiableWithinAt ℝ u s z)
    (hd : Tendsto (fun z ↦ ‖z - z₀‖ * ‖fderivWithin ℝ u s z‖) (𝓝[s \ {z₀}] z₀) (𝓝 0)) :
    Tendsto (fun ρ ↦ diam (u '' (s ∩ sphere z₀ ρ))) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨r₀, hr₀, hsub⟩ := Metric.mem_nhdsWithin_iff.1
    (hu.and (hd.eventually (gt_mem_nhds (by positivity : 0 < η / 8))))
  filter_upwards [Ioo_mem_nhdsGT hr₀] with ρ ⟨hρ₀, hρ₁⟩
  -- On `s ∩ sphere z₀ ρ`, `u` is differentiable within `s` with `ρ ‖du‖ < η / 8`.
  have harc (z : ℂ) (hz : z ∈ s ∩ sphere z₀ ρ) :
      DifferentiableWithinAt ℝ u s z ∧ ρ * ‖fderivWithin ℝ u s z‖ < η / 8 := by
    rw [← mem_sphere_iff_norm.1 hz.2]
    exact hsub ⟨sphere_subset_ball hρ₁ hz.2, hz.1, ne_of_mem_sphere hz.2 hρ₀.ne'⟩
  have h := hdiam (M := η / 8 / ρ) hρ₀ (fun z hz ↦ (harc z hz).1) fun z hz ↦ by
    rw [le_div_iff₀ hρ₀, mul_comm]
    exact (harc z hz).2.le
  rw [dist_zero_right, Real.norm_of_nonneg diam_nonneg]
  calc diam (u '' (s ∩ sphere z₀ ρ)) ≤ π * ρ * (η / 8 / ρ) := h
    _ = π / 8 * η := by field_simp
    _ < η := by nlinarith [Real.pi_le_four]

/-- If `u : ℂ → E` is differentiable on the circle of radius `ρ ≥ 0` about `z₀`, with
`‖du‖ ≤ M` there, then the image of that circle has diameter at most `π ρ M`. -/
theorem diam_image_sphere_le_of_norm_fderiv_le {ρ M : ℝ} (hρ : 0 ≤ ρ)
    (hu : ∀ z ∈ sphere z₀ ρ, DifferentiableAt ℝ u z)
    (hM : ∀ z ∈ sphere z₀ ρ, ‖fderiv ℝ u z‖ ≤ M) :
    diam (u '' sphere z₀ ρ) ≤ π * ρ * M := by
  have hcmem (θ : ℝ) : circleMap z₀ ρ θ ∈ sphere z₀ ρ := circleMap_mem_sphere z₀ hρ θ
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM _ (hcmem 0))
  refine diam_le_of_forall_dist_le (by positivity) ?_
  have hsph : range (circleMap z₀ ρ) = sphere z₀ ρ := by
    rw [range_circleMap, abs_of_nonneg hρ]
  rw [← hsph]
  rintro _ ⟨_, ⟨θ, rfl⟩, rfl⟩ _ ⟨_, ⟨φ, rfl⟩, rfl⟩
  -- Any two points of the circle are joined by an arc of angle at most `π`.
  obtain ⟨ψ, hψ, hφψ⟩ := (periodic_circleMap z₀ ρ).exists_mem_Ico Real.two_pi_pos φ (θ - π)
  rw [dist_eq_norm', hφψ]
  have h : |ψ - θ| ≤ π := by
    rw [abs_le]
    constructor <;> linarith [hψ.1, hψ.2]
  calc ‖u (circleMap z₀ ρ ψ) - u (circleMap z₀ ρ θ)‖ ≤ M * ρ * |ψ - θ| :=
      norm_sub_le_of_norm_fderiv_le_circle hρ (fun x _ ↦ hu _ (hcmem x)) fun x _ ↦ hM _ (hcmem x)
    _ ≤ M * ρ * π := mul_le_mul_of_nonneg_left h (mul_nonneg hM₀ hρ)
    _ = π * ρ * M := by ring

/-- If `u : ℂ → E` is differentiable near `z₀`, except possibly at `z₀`, and
`|z - z₀| ‖du(z)‖ → 0` as `z → z₀`, then the image of the circle of radius `ρ` about `z₀` has
diameter tending to `0` as `ρ → 0⁺`. -/
theorem tendsto_diam_image_sphere_nhdsGT_zero_of_tendsto
    (hu : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℝ u z)
    (hd : Tendsto (fun z ↦ ‖z - z₀‖ * ‖fderiv ℝ u z‖) (𝓝[≠] z₀) (𝓝 0)) :
    Tendsto (fun ρ ↦ diam (u '' sphere z₀ ρ)) (𝓝[>] 0) (𝓝 0) := by
  simpa only [univ_inter] using tendsto_diam_image_inter_sphere_nhdsGT_zero_of_diam_le
    (s := univ) (fun ρ M hρ hu hM ↦ by
      simp only [univ_inter, differentiableWithinAt_univ, fderivWithin_univ] at hu hM ⊢
      exact diam_image_sphere_le_of_norm_fderiv_le hρ.le hu hM)
    (by simpa only [← compl_eq_univ_sdiff, differentiableWithinAt_univ] using hu)
    (by simpa only [← compl_eq_univ_sdiff, fderivWithin_univ] using hd)

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
  refine diam_le_of_forall_dist_le (by positivity) ?_
  rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
  obtain ⟨θ, hθ, rfl⟩ := exists_mem_Icc_circleMap_eq_of_mem_inter_sphere hz₀ hz
  obtain ⟨φ, hφ, rfl⟩ := exists_mem_Icc_circleMap_eq_of_mem_inter_sphere hz₀ hz'
  rw [dist_eq_norm']
  refine norm_sub_circleMap_le_pi_mul (convex_Icc 0 π) hρ (fun x hx ↦ (hcmem x hx).1)
    (fun x hx ↦ hu _ (hcmem x hx)) (fun x hx ↦ hM _ (hcmem x hx)) hθ hφ ?_
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2]

/-- If `u : ℂ → E` is differentiable within the closed upper half-plane near a point `z₀` of the
real axis (except possibly at `z₀`), and `|z - z₀| ‖du(z)‖ → 0` as `z → z₀` in the closed upper
half-plane, then the diameter of the image of the upper half of the circle of radius `ρ` about
`z₀` tends to `0` as `ρ → 0`. -/
theorem tendsto_diam_image_inter_sphere_nhdsGT_zero_of_tendsto (hz₀ : z₀.im = 0)
    (hu : ∀ᶠ z in 𝓝[{z | 0 ≤ z.im} \ {z₀}] z₀, DifferentiableWithinAt ℝ u {z | 0 ≤ z.im} z)
    (hd : Tendsto (fun z ↦ ‖z - z₀‖ * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z‖)
      (𝓝[{z | 0 ≤ z.im} \ {z₀}] z₀) (𝓝 0)) :
    Tendsto (fun ρ ↦ diam (u '' ({z : ℂ | 0 ≤ z.im} ∩ sphere z₀ ρ))) (𝓝[>] 0) (𝓝 0) :=
  tendsto_diam_image_inter_sphere_nhdsGT_zero_of_diam_le
    (fun _ _ hρ ↦ diam_image_inter_sphere_le_of_norm_fderivWithin_le hz₀ hρ.le) hu hd

end TauCeti
