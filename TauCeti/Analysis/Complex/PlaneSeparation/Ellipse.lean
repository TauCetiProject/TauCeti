/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.Isoperimetric
public import TauCeti.Analysis.Green.Examples.CurveArea.Ellipse
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
import TauCeti.LinearAlgebra.Complex.Module

/-!
# The isoperimetric inequality for ellipses

For nonzero real `a` and `b`, the ellipse `t ↦ a cos t + (b sin t) i` traverses, over `[0, 2π]`,
the image `C` of the unit circle under the diagonal real-linear map `z ↦ a re z + (b im z) i`. So
`C` is a Jordan curve (`TauCeti.isJordanCurve_image_ellipse_uIcc`) whose inside is the image of the
open unit disc (`TauCeti.filledHull_image_ellipse_uIcc_sdiff`), of area `π |ab|`
(`TauCeti.volume_filledHull_image_ellipse_uIcc_sdiff`).

The ellipse is a circle exactly when its axes have equal length, `|a| = |b|`
(`TauCeti.exists_image_ellipse_uIcc_eq_sphere_iff`). So the isoperimetric inequality
`4π A ≤ L²` for the inside of `C`, of area `A`, and the length `L = H¹(C)` of `C` is an equality
exactly when `|a| = |b|`, and is strict for every ellipse with unequal axes
(`TauCeti.ofReal_four_pi_mul_volume_filledHull_image_ellipse_uIcc_sdiff_lt_iff`).

## References

* R. Osserman, *The isoperimetric inequality*, Bull. Amer. Math. Soc. **84** (1978), 1182–1238.
-/

public section

open MeasureTheory Metric Set TauCeti.Green.Examples
open scoped ENNReal Real

namespace TauCeti

variable {a b : ℝ}

/-- The trace of an ellipse with nonzero axes is a Jordan curve. -/
theorem isJordanCurve_image_ellipse_uIcc (ha : a ≠ 0) (hb : b ≠ 0) :
    IsJordanCurve (ellipse a b '' uIcc 0 (2 * π)) := by
  have h := (isJordanCurve_image_homeomorph_iff
    (ellipseCoordinates a b ha hb).toHomeomorph).mpr (isJordanCurve_sphere 0 one_pos)
  rw [image_ellipse_uIcc a b ha hb]
  simpa using h

/-- The inside of the trace of an ellipse with nonzero axes is the image of the open unit disc
under the axis coordinates. -/
theorem filledHull_image_ellipse_uIcc_sdiff (ha : a ≠ 0) (hb : b ≠ 0) :
    filledHull (ellipse a b '' uIcc 0 (2 * π)) \ ellipse a b '' uIcc 0 (2 * π) =
      ellipseCoordinates a b ha hb '' ball 0 1 := by
  set A := ellipseCoordinates a b ha hb
  have hfr : frontier (A '' ball 0 1) = ellipse a b '' uIcc 0 (2 * π) := by
    rw [image_ellipse_uIcc a b ha hb, ← frontier_ball (0 : ℂ) one_ne_zero]
    simpa using (A.toHomeomorph.image_frontier (ball 0 1)).symm
  have hU := (hfr ▸ isJordanCurve_image_ellipse_uIcc ha hb :
      IsJordanCurve (frontier (A '' ball 0 1))).eq_filledHull_sdiff_of_isOpen_of_isBounded
    (A.toHomeomorph.isOpenMap _ isOpen_ball)
    ((isCompact_closedBall (0 : ℂ) 1).image A.continuous |>.isBounded.subset
      (image_mono ball_subset_closedBall))
  rw [hfr] at hU
  exact hU.symm

/-- **The area inside an ellipse.** The inside of the trace of an ellipse with nonzero axes `a`
and `b` has area `π |ab|`. -/
theorem volume_filledHull_image_ellipse_uIcc_sdiff (ha : a ≠ 0) (hb : b ≠ 0) :
    volume (filledHull (ellipse a b '' uIcc 0 (2 * π)) \ ellipse a b '' uIcc 0 (2 * π)) =
      ENNReal.ofReal (π * |a * b|) := by
  rw [filledHull_image_ellipse_uIcc_sdiff ha hb, ← volume_ellipse_image_ball a b ha hb]
  simp

/-- The axis coordinates scale every norm by `|a|` when the axes have equal length. -/
private theorem norm_ellipseCoordinates_of_abs_eq (ha : a ≠ 0) (hb : b ≠ 0) (hab : |a| = |b|)
    (z : ℂ) : ‖ellipseCoordinates a b ha hb z‖ = |a| * ‖z‖ := by
  set A := ellipseCoordinates a b ha hb
  have he : A z = (a * z.re : ℝ) + (b * z.im : ℝ) * Complex.I := by
    have h : A z = z.re • A 1 + z.im • A Complex.I :=
      LinearMap.apply_eq_re_smul_one_add_im_smul_I A.toLinearEquiv.toLinearMap z
    rw [h, ellipseCoordinates_one, ellipseCoordinates_I]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hsq : b ^ 2 = a ^ 2 := (sq_eq_sq_iff_abs_eq_abs b a).2 hab.symm
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow, sq_abs, he, Complex.sq_norm,
    Complex.sq_norm, Complex.normSq_add_mul_I, Complex.normSq_apply]
  linear_combination z.im ^ 2 * hsq

/-- **The circular ellipses.** The trace of an ellipse with nonzero axes `a` and `b` is a circle
of positive radius exactly when `|a| = |b|`. -/
theorem exists_image_ellipse_uIcc_eq_sphere_iff (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ ellipse a b '' uIcc 0 (2 * π) = sphere c r) ↔ |a| = |b| := by
  set A := ellipseCoordinates a b ha hb
  rw [image_ellipse_uIcc a b ha hb]
  constructor
  · rintro ⟨c, r, -, h⟩
    -- The four vertices `±a` and `±b i` lie on the circle, which forces `c = 0` and `a² = r² = b²`.
    have hmem (z : ℂ) (hz : ‖z‖ = 1) : ‖A z - c‖ ^ 2 = r ^ 2 := by
      have : A z ∈ sphere c r := h ▸ mem_image_of_mem A (mem_sphere_zero_iff_norm.2 hz)
      rw [mem_sphere_iff_norm.1 this]
    have h₁ := hmem 1 (by simp)
    have h₂ := hmem (-1) (by simp)
    have h₃ := hmem Complex.I (by simp)
    have h₄ := hmem (-Complex.I) (by simp)
    simp only [map_neg, A, ellipseCoordinates_one, ellipseCoordinates_I, Complex.sq_norm,
      Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im] at h₁ h₂ h₃ h₄
    have hre : c.re = 0 := by
      have : a * c.re = 0 := by linarith
      simpa [ha] using this
    have him : c.im = 0 := by
      have : b * c.im = 0 := by linarith
      simpa [hb] using this
    rw [hre, him] at h₁ h₃
    exact (sq_eq_sq_iff_abs_eq_abs a b).1 (by linarith)
  · intro hab
    refine ⟨0, |a|, abs_pos.2 ha, Set.ext fun y ↦ ⟨?_, fun hy ↦ ?_⟩⟩
    · rintro ⟨z, hz, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hz ⊢
      rw [norm_ellipseCoordinates_of_abs_eq ha hb hab, hz, mul_one]
    · refine ⟨A.symm y, ?_, A.apply_symm_apply y⟩
      rw [mem_sphere_zero_iff_norm] at hy ⊢
      have := norm_ellipseCoordinates_of_abs_eq ha hb hab (A.symm y)
      rw [A.apply_symm_apply, hy] at this
      exact (mul_eq_left₀ (abs_ne_zero.2 ha)).1 this.symm

/-- **Equality in the isoperimetric inequality for an ellipse.** The inside of the trace `C` of
an ellipse with nonzero axes `a` and `b` satisfies `4π |inside C| = H¹(C)²` exactly when
`|a| = |b|`. -/
theorem ofReal_four_pi_mul_volume_filledHull_image_ellipse_uIcc_sdiff_eq_iff (ha : a ≠ 0)
    (hb : b ≠ 0) :
    ENNReal.ofReal (4 * π) *
        volume (filledHull (ellipse a b '' uIcc 0 (2 * π)) \ ellipse a b '' uIcc 0 (2 * π)) =
      μHE[1] (ellipse a b '' uIcc 0 (2 * π)) ^ 2 ↔ |a| = |b| :=
  (isJordanCurve_image_ellipse_uIcc ha hb).ofReal_four_pi_mul_volume_filledHull_sdiff_eq_iff.trans
    (exists_image_ellipse_uIcc_eq_sphere_iff ha hb)

/-- **The isoperimetric inequality is strict for noncircular ellipses.** The inside of the trace
`C` of an ellipse with nonzero axes `a` and `b` satisfies `4π |inside C| < H¹(C)²` exactly when
`|a| ≠ |b|`. -/
theorem ofReal_four_pi_mul_volume_filledHull_image_ellipse_uIcc_sdiff_lt_iff (ha : a ≠ 0)
    (hb : b ≠ 0) :
    ENNReal.ofReal (4 * π) *
        volume (filledHull (ellipse a b '' uIcc 0 (2 * π)) \ ellipse a b '' uIcc 0 (2 * π)) <
      μHE[1] (ellipse a b '' uIcc 0 (2 * π)) ^ 2 ↔ |a| ≠ |b| := by
  rw [lt_iff_le_and_ne, ne_eq,
    ofReal_four_pi_mul_volume_filledHull_image_ellipse_uIcc_sdiff_eq_iff ha hb, and_iff_right
      (isJordanCurve_image_ellipse_uIcc ha hb).ofReal_four_pi_mul_volume_filledHull_sdiff_le]

end TauCeti
