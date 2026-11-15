/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Extending primitives and wedge integrals on product domains

Mathlib's `DifferentiableOn.isExactOn_ball` gives every holomorphic function on a disc a
primitive there, built from `Complex.wedgeIntegral`. This file records:

* `DifferentiableOn.exists_hasDerivAt_eqOn_ball_inter` -- a primitive of a holomorphic integrand
  on `ball c r ∩ U`, for convex `U`, is the restriction of a primitive on `ball c r`.
* `TauCeti.norm_wedgeIntegral_le_of_norm_le_const` and
  `TauCeti.norm_wedgeIntegral_le_of_norm_le_mul_norm` -- norm bounds on
  `Complex.wedgeIntegral z w f` from constant or linear bounds on `Complex.Rectangle z w`.
* `Complex.IsConservativeOn.wedgeIntegral_sub_wedgeIntegral_eq_of_mem_reProdIm` and
  `Complex.IsConservativeOn.hasDerivAt_wedgeIntegral_of_mem_reProdIm` -- path additivity and
  differentiation of `Complex.wedgeIntegral` on any axis-aligned product `A ×ℂ B` of order-connected
  real sets (covering half-planes, open and closed strips, and rectangles, including base points on
  the boundary).
-/

public section

open Complex MeasureTheory Metric Set
open scoped Interval Topology

section BallInter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A holomorphic integrand `g` on a disc has a primitive on the disc agreeing with any given
primitive `f` of `g` on the intersection of the disc with a convex set `U`. -/
theorem DifferentiableOn.exists_hasDerivAt_eqOn_ball_inter {f g : ℂ → E} {c : ℂ} {r : ℝ}
    {U : Set ℂ} (hg : DifferentiableOn ℂ g (ball c r)) (hU : Convex ℝ U)
    (hf : ∀ z ∈ ball c r ∩ U, HasDerivWithinAt f (g z) (ball c r ∩ U) z) :
    ∃ G : ℂ → E, (∀ z ∈ ball c r, HasDerivAt G (g z) z) ∧ EqOn G f (ball c r ∩ U) := by
  obtain ⟨P, hP⟩ := hg.isExactOn_ball
  rcases (ball c r ∩ U).eq_empty_or_nonempty with hV | ⟨z₀, hz₀⟩
  · exact ⟨P, hP, by simp [hV]⟩
  refine ⟨fun z ↦ P z + (f z₀ - P z₀), fun z hz ↦ (hP z hz).add_const _, fun z hz ↦ ?_⟩
  have hderiv (w) (hw : w ∈ ball c r ∩ U) :
      HasDerivWithinAt (f - P) 0 (ball c r ∩ U) w := by
    simpa using (hf w hw).sub (hP w hw.1).hasDerivWithinAt
  have := ((convex_ball c r).inter hU).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
    (fun _ _ ↦ norm_zero.le) hz₀ hz
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero, Pi.sub_apply, Pi.sub_apply] at this
  simp [← this]

end BallInter

noncomputable section WedgeIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E}

namespace TauCeti

/-- If `‖f u‖ ≤ M` throughout `Rectangle z w`, then `‖wedgeIntegral z w f‖ ≤ 2 * M * ‖w - z‖`. -/
theorem norm_wedgeIntegral_le_of_norm_le_const {M : ℝ} {z w : ℂ}
    (hf : ∀ u ∈ Rectangle z w, ‖f u‖ ≤ M) : ‖wedgeIntegral z w f‖ ≤ 2 * M * ‖w - z‖ := by
  have hre : ‖∫ x in z.re..w.re, f (x + z.im * I)‖ ≤ M * |w.re - z.re| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦
      hf _ ⟨by simpa using uIoc_subset_uIcc hx, by simp⟩
  have him : ‖∫ y in z.im..w.im, f (w.re + y * I)‖ ≤ M * |w.im - z.im| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y hy ↦
      hf _ ⟨by simp, by simpa using uIoc_subset_uIcc hy⟩
  have hM : 0 ≤ M := (norm_nonneg (f z)).trans (hf z ⟨left_mem_uIcc, left_mem_uIcc⟩)
  calc ‖wedgeIntegral z w f‖
      ≤ ‖∫ x in z.re..w.re, f (x + z.im * I)‖ +
          ‖I • ∫ y in z.im..w.im, f (w.re + y * I)‖ := norm_add_le _ _
    _ ≤ M * |w.re - z.re| + M * |w.im - z.im| := by simpa [norm_smul] using add_le_add hre him
    _ ≤ M * ‖w - z‖ + M * ‖w - z‖ := by
        rw [← sub_re, ← sub_im]; gcongr; exacts [abs_re_le_norm _, abs_im_le_norm _]
    _ = 2 * M * ‖w - z‖ := by ring

/-- Under a linear norm bound `‖f u‖ ≤ C₀ * ‖u‖` on `Rectangle z w`, the wedge integral satisfies
`‖wedgeIntegral z w f‖ ≤ 2 * C₀ * (‖z‖ + ‖w - z‖) * ‖w - z‖`. -/
theorem norm_wedgeIntegral_le_of_norm_le_mul_norm {C₀ : ℝ} {z w : ℂ}
    (hf : ∀ u ∈ Rectangle z w, ‖f u‖ ≤ C₀ * ‖u‖) :
    ‖wedgeIntegral z w f‖ ≤ 2 * C₀ * (‖z‖ + ‖w - z‖) * ‖w - z‖ := by
  by_cases hzw : z = 0 ∧ w = 0
  · simp [hzw.1, hzw.2, wedgeIntegral]
  have hC₀ : 0 ≤ C₀ := (not_and_or.1 hzw).elim
    (fun hz ↦ nonneg_of_mul_nonneg_left
      ((norm_nonneg _).trans (hf z ⟨left_mem_uIcc, left_mem_uIcc⟩)) (norm_pos_iff.2 hz))
    (fun hw ↦ nonneg_of_mul_nonneg_left
      ((norm_nonneg _).trans (hf w ⟨right_mem_uIcc, right_mem_uIcc⟩)) (norm_pos_iff.2 hw))
  refine (norm_wedgeIntegral_le_of_norm_le_const (M := C₀ * (‖z‖ + ‖w - z‖)) fun u hu ↦
    (hf u hu).trans <| mul_le_mul_of_nonneg_left
      ((norm_le_insert' u z).trans <| add_le_add_right ?_ _) hC₀).trans_eq (by ring)
  rw [← dist_eq_norm, ← dist_eq_norm w z, dist_eq_re_im, dist_eq_re_im]
  exact Real.sqrt_le_sqrt (add_le_add (sq_le_sq.2 (abs_sub_left_of_mem_uIcc hu.1))
    (sq_le_sq.2 (abs_sub_left_of_mem_uIcc hu.2)))

end TauCeti

/-- On an axis-aligned product `A ×ℂ B` of order-connected real sets, wedge integrals of a
continuous conservative function are additive across arbitrary points of `A ×ℂ B`. -/
theorem Complex.IsConservativeOn.wedgeIntegral_sub_wedgeIntegral_eq_of_mem_reProdIm
    {A B : Set ℝ} (hf : IsConservativeOn f (A ×ℂ B)) (hA : A.OrdConnected) (hB : B.OrdConnected)
    (hcont : ContinuousOn f (A ×ℂ B)) {b z w : ℂ} (hb : b ∈ A ×ℂ B) (hz : z ∈ A ×ℂ B)
    (hw : w ∈ A ×ℂ B) : wedgeIntegral b w f - wedgeIntegral b z f = wedgeIntegral z w f := by
  set I₁ := ∫ x in b.re..w.re, f (x + b.im * I); set I₂ := I • ∫ y in b.im..w.im, f (w.re + y * I)
  set I₃ := ∫ x in b.re..z.re, f (x + b.im * I); set I₄ := I • ∫ y in b.im..z.im, f (z.re + y * I)
  set I₅ := ∫ x in z.re..w.re, f (x + z.im * I); set I₆ := I • ∫ y in z.im..w.im, f (w.re + y * I)
  set I₇ := ∫ x in z.re..w.re, f (x + b.im * I); set I₈ := I • ∫ y in b.im..z.im, f (w.re + y * I)
  have intH {x₁ x₂ y : ℝ} (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hy : y ∈ B) :
      IntervalIntegrable (fun x : ℝ ↦ f (x + y * I)) volume x₁ x₂ :=
    (hcont.comp (by fun_prop) fun _ hx ↦
      ⟨by simpa using hA.uIcc_subset hx₁ hx₂ hx, by simpa using hy⟩).intervalIntegrable
  have intV {x y₁ y₂ : ℝ} (hx : x ∈ A) (hy₁ : y₁ ∈ B) (hy₂ : y₂ ∈ B) :
      IntervalIntegrable (fun y : ℝ ↦ f (x + y * I)) volume y₁ y₂ :=
    (hcont.comp (by fun_prop) fun _ hy ↦
      ⟨by simpa using hx, by simpa using hB.uIcc_subset hy₁ hy₂ hy⟩).intervalIntegrable
  have hI₁ : I₁ = I₃ + I₇ :=
    (intervalIntegral.integral_add_adjacent_intervals (intH hb.1 hz.1 hb.2)
      (intH hz.1 hw.1 hb.2)).symm
  have hI₂ : I₂ = I₈ + I₆ := by
    rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals (intV hw.1 hb.2 hz.2)
      (intV hw.1 hz.2 hw.2)]
  have hI₀ : I₇ - I₅ + I₈ - I₄ = 0 := by
    simpa [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq] using
      hf (z.re + b.im * I) (w.re + z.im * I) fun _ hp ↦
        ⟨hA.uIcc_subset hz.1 hw.1 (by simpa using hp.1),
          hB.uIcc_subset hb.2 hz.2 (by simpa using hp.2)⟩
  grind [wedgeIntegral]

/-- On an axis-aligned product `A ×ℂ B` of order-connected real sets, the wedge integral of a
continuous conservative function from any base point `b ∈ A ×ℂ B` has complex derivative `f z` at
every interior point `z` (`A ×ℂ B ∈ 𝓝 z`), even when `b` lies on the boundary of `A ×ℂ B`. -/
theorem Complex.IsConservativeOn.hasDerivAt_wedgeIntegral_of_mem_reProdIm [CompleteSpace E]
    {A B : Set ℝ} (hf : IsConservativeOn f (A ×ℂ B)) (hA : A.OrdConnected) (hB : B.OrdConnected)
    (hcont : ContinuousOn f (A ×ℂ B)) {b z : ℂ} (hb : b ∈ A ×ℂ B) (hz : A ×ℂ B ∈ 𝓝 z) :
    HasDerivAt (fun w ↦ wedgeIntegral b w f) (f z) z := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hz
  refine (((hf.mono hball).hasDerivAt_wedgeIntegral (hcont.mono hball)
    (mem_ball_self hr)).const_add (wedgeIntegral b z f)).congr_of_eventuallyEq ?_
  filter_upwards [hz] with w hw
  have := hf.wedgeIntegral_sub_wedgeIntegral_eq_of_mem_reProdIm hA hB hcont hb
    (mem_of_mem_nhds hz) hw
  grind

end WedgeIntegral
