/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.Isoperimetric
public import TauCeti.Analysis.Green.Examples.CurveArea.Ellipse
import TauCeti.Analysis.Complex.PlaneSeparation.Inside

/-!
# The isoperimetric inequality for ellipses

For nonzero real `a` and `b`, the ellipse `t ↦ a cos t + (b sin t) i` traverses, over `[0, 2π]`,
the image `C` of the unit circle under the diagonal real-linear map `z ↦ a re z + (b im z) i`. So
`C` is a Jordan curve (`TauCeti.isJordanCurve_image_ellipse_uIcc`) whose inside is the image of the
open unit disc (`TauCeti.filledHull_image_ellipse_uIcc_sdiff`), of area `π |ab|`
(`TauCeti.volume_filledHull_image_ellipse_uIcc_sdiff`).

The ellipse is a circle exactly when its axes have equal length, `|a| = |b|`
(`TauCeti.Green.Examples.exists_image_ellipse_uIcc_eq_sphere_iff`). So the isoperimetric inequality
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
