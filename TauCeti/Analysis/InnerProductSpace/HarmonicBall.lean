/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.InnerProductSpace.HarmonicDilation
public import TauCeti.Analysis.InnerProductSpace.HarmonicIsometry

/-!
# Ball normalizations for harmonic functions

The PDE roadmap's Lane C uses translations and dilations to reduce local arguments on a ball
`Metric.ball x r` to arguments on the unit ball.  The files
`TauCeti.Analysis.InnerProductSpace.HarmonicIsometry` and
`TauCeti.Analysis.InnerProductSpace.HarmonicDilation` prove the underlying invariance of
harmonicity under translations and nonzero dilations.  This file packages the corresponding
consumer forms for metric balls.

The main statement is `harmonicOnNhd_comp_center_add_smul_ball_iff`: for `0 < r`, the
normalized function `y ↦ f (x + r • y)` is harmonic near the unit ball if and only if `f` is
harmonic near `Metric.ball x r`.

## Main declarations

* `TauCeti.harmonicOnNhd_comp_add_right_ball_zero_iff`: translation-normalized harmonicity
  on a ball.
* `TauCeti.harmonicAt_comp_center_add_smul_iff` and
  `TauCeti.harmonicOnNhd_comp_center_add_smul_ball_radius_iff`: pointwise and ball-level
  affine normalization by `y ↦ x + c • y`.
* `TauCeti.harmonicOnNhd_comp_center_add_smul_ball_iff`: the unit-ball specialization.
-/

public section

namespace TauCeti

open InnerProductSpace

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Translation-normalized harmonicity on a ball.  The function `y ↦ f (y + x)` is harmonic
near the radius-`r` ball centered at `0` exactly when `f` is harmonic near the corresponding
ball centered at `x`. -/
theorem harmonicOnNhd_comp_add_right_ball_zero_iff (x : E) (r : ℝ) {f : E → F} :
    HarmonicOnNhd (fun y ↦ f (y + x)) (Metric.ball 0 r) ↔
      HarmonicOnNhd f (Metric.ball x r) := by
  have hpre : ((fun y : E ↦ y + x) ⁻¹' Metric.ball x r) = Metric.ball 0 r := by
    rw [show (fun y : E ↦ y + x) = (x + ·) from funext fun _ ↦ add_comm _ _]
    simp [preimage_add_ball]
  rw [← hpre]
  exact harmonicOnNhd_comp_add_right_iff (a := x) (f := f) (s := Metric.ball x r)

/-- Pointwise harmonicity is invariant under the affine normalization `y ↦ x + r • y` when
the scale is nonzero. -/
theorem harmonicAt_comp_center_add_smul_iff (x : E) {r : ℝ} (hr : r ≠ 0) {f : E → F}
    {y : E} :
    HarmonicAt (fun z ↦ f (x + r • z)) y ↔ HarmonicAt f (x + r • y) := by
  have hfun : (fun z : E ↦ f (x + r • z)) = fun z ↦ (fun w : E ↦ f (x + w)) (r • z) := by
    rfl
  have hpoint : x + r • y = r • y + x := by rw [add_comm]
  have hscale :=
    harmonicAt_comp_smul_right_iff (c := r) hr (f := fun w : E ↦ f (x + w)) (x := y)
  have htranslate :=
    harmonicAt_comp_add_right_iff (f := f) (x := r • y) (a := x)
  have hcomm : (fun w : E ↦ f (x + w)) = fun w ↦ f (w + x) := by
    funext w
    rw [add_comm]
  rw [hcomm] at hscale
  rw [hfun]
  exact hscale.trans (by simpa [hpoint] using htranslate)

/-- Harmonicity on a neighbourhood of `Metric.ball x (c * r)` is equivalent to harmonicity
of `y ↦ f (x + c • y)` on a neighbourhood of `Metric.ball 0 r`, for `0 < c`. -/
theorem harmonicOnNhd_comp_center_add_smul_ball_radius_iff (x : E) {c : ℝ} (hc : 0 < c)
    (r : ℝ) {f : E → F} :
    HarmonicOnNhd (fun y ↦ f (x + c • y)) (Metric.ball 0 r) ↔
      HarmonicOnNhd f (Metric.ball x (c * r)) := by
  have hfun : (fun y : E ↦ f (x + c • y)) =
      fun y ↦ (fun z : E ↦ f (z + x)) (c • y) := by
    funext y
    rw [add_comm]
  have hpre : ((fun y : E ↦ c • y) ⁻¹' Metric.ball (0 : E) (c * r)) = Metric.ball 0 r := by
    rw [Set.preimage_smul₀ hc.ne', smul_ball (inv_ne_zero hc.ne') 0 (c * r)]
    simp [Real.norm_of_nonneg (inv_nonneg.2 hc.le), inv_mul_cancel_left₀ hc.ne']
  rw [hfun]
  rw [← harmonicOnNhd_comp_add_right_ball_zero_iff x (c * r) (f := f)]
  rw [← hpre]
  simpa using
    (harmonicOnNhd_comp_smul_right_iff c hc.ne' (f := fun z : E ↦ f (z + x))
      (s := Metric.ball 0 (c * r)))

/-- Harmonicity on a neighbourhood of `Metric.ball x r` is equivalent to harmonicity of the
normalized function `y ↦ f (x + r • y)` on a neighbourhood of the unit ball. -/
theorem harmonicOnNhd_comp_center_add_smul_ball_iff (x : E) {r : ℝ} (hr : 0 < r)
    {f : E → F} :
    HarmonicOnNhd (fun y ↦ f (x + r • y)) (Metric.ball 0 1) ↔
      HarmonicOnNhd f (Metric.ball x r) := by
  simpa using harmonicOnNhd_comp_center_add_smul_ball_radius_iff (x := x) hr 1 (f := f)

end TauCeti
