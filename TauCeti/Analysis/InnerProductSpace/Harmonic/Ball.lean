/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Dilation

/-!
# Ball and sphere normalizations for harmonic functions

The PDE roadmap's Lane C uses translations and dilations to reduce local arguments on a ball
`Metric.ball x r` to arguments on the unit ball.  The files
`TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry` and
`TauCeti.Analysis.InnerProductSpace.Harmonic.Dilation` prove the underlying invariance of
harmonicity under translations and nonzero dilations.  This file packages the corresponding
consumer forms for metric balls.  It also records the corresponding set normalizations for
closed balls and spheres used in mean-value arguments.

The main statement is `harmonicOnNhd_comp_const_add_smul_ball_iff`: for `0 < r`, the
normalized function `y ↦ f (x + r • y)` is harmonic near the unit ball if and only if `f` is
harmonic near `Metric.ball x r`.

## Main declarations

* `TauCeti.preimage_const_add_smul_ball_norm`: affine normalization of an open ball over a
  normed division ring.
* `TauCeti.preimage_const_add_smul_ball`: the compatible real-scalar form.
* `TauCeti.preimage_const_add_smul_closedBall`: affine normalization of a closed ball.
* `TauCeti.preimage_const_add_smul_sphere`: affine normalization of a sphere.
* `TauCeti.harmonicOnNhd_comp_add_right_ball_zero_iff`: translation-normalized harmonicity
  on a ball.
* `TauCeti.harmonicOnNhd_comp_const_add_smul_ball_radius_iff`: ball-level affine normalization
  by `y ↦ x + c • y` for nonzero scale `c`.
* `TauCeti.harmonicOnNhd_comp_const_add_smul_ball_iff`: the unit-ball specialization.
-/

public section

namespace TauCeti

open InnerProductSpace

section Preimage

variable {𝕜 E : Type*} [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E]
  [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-- The affine normalization map `y ↦ x + c • y` pulls the ball `Metric.ball x (‖c‖ * r)` back
to `Metric.ball 0 r`, for nonzero scale `c`.  This is the characteristic ball rewrite underlying
the harmonic ball-normalization lemmas below. -/
@[simp]
theorem preimage_const_add_smul_ball_norm (x : E) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ x + c • y) ⁻¹' Metric.ball x (‖c‖ * r)) = Metric.ball 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero,
    norm_smul]
  exact mul_lt_mul_iff_right₀ (norm_pos_iff.2 hc)

/-- The affine map `y ↦ x + c • y` pulls the closed ball of radius `‖c‖ * r` about `x`
back to the closed ball of radius `r` about `0`. -/
@[simp]
theorem preimage_const_add_smul_closedBall (x : E) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ x + c • y) ⁻¹' Metric.closedBall x (‖c‖ * r)) =
      Metric.closedBall 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left,
    sub_zero, norm_smul]
  exact mul_le_mul_iff_right₀ (norm_pos_iff.2 hc)

/-- The affine map `y ↦ x + c • y` pulls the sphere of radius `‖c‖ * r` about `x`
back to the sphere of radius `r` about `0`. -/
@[simp]
theorem preimage_const_add_smul_sphere (x : E) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ x + c • y) ⁻¹' Metric.sphere x (‖c‖ * r)) = Metric.sphere 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, sub_zero,
    norm_smul]
  constructor
  · exact mul_left_cancel₀ (norm_pos_iff.2 hc).ne'
  · exact congrArg ((· * ·) ‖c‖)

/-- Membership form of `preimage_const_add_smul_ball_norm`. -/
@[simp]
theorem const_add_smul_mem_ball_iff (x y : E) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ‖c • y‖ < ‖c‖ * r ↔ y ∈ Metric.ball 0 r := by
  simpa only [Set.mem_preimage, Metric.mem_ball, dist_self_add_left] using
    Set.ext_iff.mp (preimage_const_add_smul_ball_norm x hc r) y

/-- Membership form of `preimage_const_add_smul_closedBall`. -/
@[simp]
theorem const_add_smul_mem_closedBall_iff (x y : E) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ‖c • y‖ ≤ ‖c‖ * r ↔ y ∈ Metric.closedBall 0 r := by
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_self_add_left] using
    Set.ext_iff.mp (preimage_const_add_smul_closedBall x hc r) y

/-- Membership form of `preimage_const_add_smul_sphere`. -/
@[simp]
theorem const_add_smul_mem_sphere_iff (x y : E) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ‖c • y‖ = ‖c‖ * r ↔ y ∈ Metric.sphere 0 r := by
  simpa only [Set.mem_preimage, mem_sphere_iff_norm, add_sub_cancel_left] using
    Set.ext_iff.mp (preimage_const_add_smul_sphere x hc r) y

end Preimage

/-- The real-scalar form of `preimage_const_add_smul_ball_norm`. -/
@[simp]
theorem preimage_const_add_smul_ball {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    [NormSMulClass ℝ E] (x : E) {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ x + c • y) ⁻¹' Metric.ball x (|c| * r)) = Metric.ball 0 r := by
  simpa [Real.norm_eq_abs] using preimage_const_add_smul_ball_norm x hc r

/-- Positive-radius affine normalization of membership in a ball to the unit ball. -/
@[simp]
theorem const_add_smul_mem_ball_unit_iff {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    [NormSMulClass ℝ E] (x y : E) {r : ℝ} (hr : 0 < r) :
    ‖r • y‖ < r ↔ y ∈ Metric.ball 0 1 := by
  simpa [Real.norm_of_nonneg hr.le] using const_add_smul_mem_ball_iff x y hr.ne' 1

/-- Positive-radius affine normalization of membership in a closed ball to the unit closed ball. -/
@[simp]
theorem const_add_smul_mem_closedBall_unit_iff {E : Type*} [SeminormedAddCommGroup E]
    [Module ℝ E] [NormSMulClass ℝ E] (x y : E) {r : ℝ} (hr : 0 < r) :
    ‖r • y‖ ≤ r ↔ y ∈ Metric.closedBall 0 1 := by
  simpa [Real.norm_of_nonneg hr.le] using const_add_smul_mem_closedBall_iff x y hr.ne' 1

/-- Positive-radius affine normalization of membership in a sphere to the unit sphere. -/
@[simp]
theorem const_add_smul_mem_sphere_unit_iff {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    [NormSMulClass ℝ E] (x y : E) {r : ℝ} (hr : 0 < r) :
    ‖r • y‖ = r ↔ y ∈ Metric.sphere 0 1 := by
  simpa [Real.norm_of_nonneg hr.le] using const_add_smul_mem_sphere_iff x y hr.ne' 1

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Harmonicity on a neighbourhood of `Metric.ball x (‖c‖ * r)` is equivalent to harmonicity
of `y ↦ f (x + c • y)` on a neighbourhood of `Metric.ball 0 r`, for nonzero scale `c`. -/
theorem harmonicOnNhd_comp_const_add_smul_ball_radius_iff (x : E) {c : ℝ} (hc : c ≠ 0)
    (r : ℝ) {f : E → F} :
    HarmonicOnNhd (fun y ↦ f (x + c • y)) (Metric.ball 0 r) ↔
      HarmonicOnNhd f (Metric.ball x (‖c‖ * r)) := by
  rw [← preimage_const_add_smul_ball_norm x hc r]
  exact harmonicOnNhd_comp_const_add_smul_iff x hc (f := f) (s := Metric.ball x (‖c‖ * r))

/-- Translation-normalized harmonicity on a ball.  The function `y ↦ f (y + x)` is harmonic
near the radius-`r` ball centered at `0` exactly when `f` is harmonic near the corresponding
ball centered at `x`. -/
theorem harmonicOnNhd_comp_add_right_ball_zero_iff (x : E) (r : ℝ) {f : E → F} :
    HarmonicOnNhd (fun y ↦ f (y + x)) (Metric.ball 0 r) ↔
      HarmonicOnNhd f (Metric.ball x r) := by
  simpa [one_smul, add_comm] using
    harmonicOnNhd_comp_const_add_smul_ball_radius_iff (x := x) (c := 1) one_ne_zero r (f := f)

/-- Harmonicity on a neighbourhood of `Metric.ball x r` is equivalent to harmonicity of the
normalized function `y ↦ f (x + r • y)` on a neighbourhood of the unit ball. -/
theorem harmonicOnNhd_comp_const_add_smul_ball_iff (x : E) {r : ℝ} (hr : 0 < r)
    {f : E → F} :
    HarmonicOnNhd (fun y ↦ f (x + r • y)) (Metric.ball 0 1) ↔
      HarmonicOnNhd f (Metric.ball x r) := by
  simpa [Real.norm_of_nonneg hr.le] using
    harmonicOnNhd_comp_const_add_smul_ball_radius_iff (x := x) hr.ne' 1 (f := f)

end TauCeti
