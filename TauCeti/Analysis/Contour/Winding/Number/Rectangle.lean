/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Curve.Rectangle
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import TauCeti.Analysis.Green.Polygonal.Geometry
import TauCeti.Analysis.Contour.Winding.Integer
import TauCeti.Analysis.Contour.Winding.Number.Segment.Bounds
import TauCeti.Analysis.Contour.Winding.StarConvex

/-!
# Winding numbers of the boundary of a rectangle

This file evaluates the generalized winding number `TauCeti.Contour.windingNumber` of the closed
rectangle boundary `Complex.rectBoundary z w` on `[0, 4]`:

* about a point of the open rectangle `Ioo z.re w.re ×ℂ Ioo z.im w.im` it is `1`
  (`TauCeti.Contour.windingNumber_rectBoundary_eq_one`). The hypothesis forces `z` to be the lower
  left corner, so the boundary is traversed counterclockwise;
* about a point outside the closed rectangle `Complex.Rectangle z w` it is `0`
  (`TauCeti.Contour.windingNumber_rectBoundary_eq_zero`), whatever the position of the corners.

Consequently the boundary is null-homologous in every set containing the closed rectangle
(`TauCeti.Contour.isNullHomologous_rectBoundary`). These are the inputs that let the argument
principle and the residue theorem for null-homologous curves count the zeros and poles of a
function inside a rectangle, as in the Riemann–von Mangoldt formula.

The interior value is computed edge by edge: off the boundary the winding number is the sum of the
winding numbers of the four edges, a point strictly to the left of a directed segment sees that
segment with winding number of real part in `(0, 1/2)`, and the only integer in `(0, 2)` is `1`.
This adapts the argument of `TauCeti.Green.windingNumber_triangleCurve_eq_one`, which evaluates
the winding number of a counterclockwise triangle in the same way.
The exterior value holds because the rectangle is convex, so the curve contracts inside it.
-/

public section

open Set Complex

namespace TauCeti.Contour

variable {z w p : ℂ}

/-- The rectangle boundary over `[0, 4]` lies in the closed rectangle. -/
private theorem rectBoundary_mem_rectangle_of_mem_uIcc {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) 4) :
    rectBoundary z w t ∈ Rectangle z w :=
  rectBoundary_mem_rectangle (by rwa [uIcc_of_le (by norm_num)] at ht)

/-- **The winding number of a rectangle boundary vanishes outside the closed rectangle.** -/
theorem windingNumber_rectBoundary_eq_zero (hp : p ∉ Rectangle z w) :
    windingNumber (rectBoundary z w) 0 4 p = 0 :=
  windingNumber_eq_zero_of_starConvex
    ((convex_rectangle z w).starConvex (rectBoundary_mem_rectangle ⟨le_rfl, by norm_num⟩))
    (isPiecewiseC1On_rectBoundary z w) (by simp) (fun _ ↦ rectBoundary_mem_rectangle_of_mem_uIcc)
    hp

/-- **The boundary of a rectangle is null-homologous in every set containing the rectangle.** -/
theorem isNullHomologous_rectBoundary {U : Set ℂ} (hU : Rectangle z w ⊆ U) :
    IsNullHomologous (rectBoundary z w) 0 4 U :=
  (isNullHomologous_of_starConvex
    ((convex_rectangle z w).starConvex (rectBoundary_mem_rectangle ⟨le_rfl, by norm_num⟩))
    (isPiecewiseC1On_rectBoundary z w) (by simp)
    (fun _ ↦ rectBoundary_mem_rectangle_of_mem_uIcc)).mono hU

/-- **The boundary of a rectangle winds once around every point of the open rectangle.** The
hypothesis forces `z` to be the lower left corner, so that the boundary is traversed
counterclockwise. -/
theorem windingNumber_rectBoundary_eq_one (hp : p ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    windingNumber (rectBoundary z w) 0 4 p = 1 := by
  have hfr : p ∉ frontier (Rectangle z w) := by
    have hint := hp
    rw [← interior_rectangle (hp.1.1.trans hp.1.2).le (hp.2.1.trans hp.2.2).le] at hint
    exact disjoint_left.1 disjoint_interior_frontier hint
  obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := hp
  -- Off the boundary, the winding number is the sum of the winding numbers of the four edges.
  have hsum := (rectPolygon z w).windingNumber_contourCycle (boundary_rectPolygon z w ▸ hfr)
  rw [Polygon.contourCycle_def, Polygon.contourCurve_def, Cycle.windingNumber_of_raw,
    Nat.cast_ofNat, ← rectBoundary_def, Fin.sum_univ_four] at hsum
  -- Each edge sees `p` on its left, so contributes a real part in `(0, 1/2)`.
  have hedge (i : Fin 4) (hleft : 0 < ((p - rectPolygon z w i) /
      (rectPolygon z w (finRotate 4 i) - rectPolygon z w i)).im) :
      (windingNumber ((rectPolygon z w).edgePath ℝ i) 0 1 p).re ∈ Ioo 0 (1 / 2) := by
    have heq : ⇑((rectPolygon z w).edgePath ℝ i) = fun t : ℝ ↦ rectPolygon z w i +
        t • (rectPolygon z w (finRotate 4 i) - rectPolygon z w i) := by
      funext t
      rw [Polygon.edgePath, AffineMap.lineMap_apply_module', add_comm]
    rw [heq]
    exact windingNumber_segment_re_mem_Ioo hleft
  have e₀ := hedge 0 (Green.im_div_sub_pos_of_triangleDet_pos (by
    simp [Green.triangleDet_def, finRotate_apply]; nlinarith))
  have e₁ := hedge 1 (Green.im_div_sub_pos_of_triangleDet_pos (by
    simp [Green.triangleDet_def, finRotate_apply]; nlinarith))
  have e₂ := hedge 2 (Green.im_div_sub_pos_of_triangleDet_pos (by
    simp [Green.triangleDet_def, finRotate_apply]; nlinarith))
  have e₃ := hedge 3 (Green.im_div_sub_pos_of_triangleDet_pos (by
    simp [Green.triangleDet_def, finRotate_apply]; nlinarith))
  -- The winding number of the closed curve is an integer, which must be `1`.
  obtain ⟨n, hn⟩ := (isPiecewiseC1On_rectBoundary z w).exists_int_windingNumber (by simp)
    fun t ht (h : rectBoundary z w t = p) ↦
      hfr (h ▸ rectBoundary_mem_frontier (by rwa [uIcc_of_le (by norm_num)] at ht))
  have hre := congrArg re hsum
  simp only [add_re, hn, intCast_re] at hre
  have hpos : (0 : ℤ) < n := by
    have : (0 : ℝ) < n := by linarith [e₀.1, e₁.1, e₂.1, e₃.1]
    exact_mod_cast this
  have hlt : n < 2 := by
    have : (n : ℝ) < 2 := by linarith [e₀.2, e₁.2, e₂.2, e₃.2]
    exact_mod_cast this
  rw [hn, show n = 1 by omega, Int.cast_one]

end TauCeti.Contour
