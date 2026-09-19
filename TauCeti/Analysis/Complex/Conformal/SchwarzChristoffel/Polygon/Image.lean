/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Image
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.Boundary
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.ClosingSide

/-!
# The Schwarz--Christoffel image and the closing side

For strictly ordered prevertices with exponents in `(-1, 0)` summing to `-2`, the
Schwarz--Christoffel polygon lies in the closed half-plane above its horizontal closing side. The
filled-hull bound for the primitive therefore puts its entire upper-half-plane image in the same
closed half-plane. Since that image is open, it actually lies in the corresponding open
half-plane and misses both pieces of the closing side.

This is one part of identifying the image with the polygon interior. Bounded-side avoidance is
proved using supporting lines, and the resulting global image and injectivity statements are
assembled in `TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.Mapping`.

## Main results

* `TauCeti.schwarzChristoffelPolygon_boundary_subset_halfSpace` -- the polygon boundary lies on or
  above its closing line.
* `TauCeti.im_schwarzChristoffelVertex_zero_lt_of_mem_interior_closedConvexHull_boundary` -- the
  polygon interior lies strictly above its closing line.
* `TauCeti.im_schwarzChristoffelVertex_zero_lt_primitive` -- every value of the primitive in the
  upper half-plane lies strictly above the closing line.
* `TauCeti.disjoint_image_schwarzChristoffelPrimitive_closingSides` -- the image misses both
  pieces of the closing side.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Bornology Complex Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

/-- **The Schwarz--Christoffel polygon boundary lies on or above its closing line.** The two
closing edges lie on the line, while the finite vertices and hence every bounded edge lie in its
upper closed half-plane. -/
theorem schwarzChristoffelPolygon_boundary_subset_halfSpace
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    (schwarzChristoffelPolygon a e z₀).boundary ℝ ⊆
      {z | (schwarzChristoffelVertex a e z₀ 0).im ≤ z.im} := by
  rw [schwarzChristoffelPolygon_boundary]
  rintro z ((hz | hz) | hz)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact (convex_halfSpace_im_ge _).segment_subset
      (im_schwarzChristoffelVertex_zero_le a e z₀ ha he hsum i.castSucc)
      (im_schwarzChristoffelVertex_zero_le a e z₀ ha he hsum i.succ) hi
  · exact (convex_halfSpace_im_ge _).segment_subset
      (im_schwarzChristoffelVertex_zero_le a e z₀ ha he hsum (Fin.last n))
      (im_schwarzChristoffelVertexAtInfinity_eq_im_zero a e z₀ ha he hsum).ge hz
  · have hinfty :=
      (im_schwarzChristoffelVertexAtInfinity_eq_im_zero a e z₀ ha he hsum).ge
    have hzero : (schwarzChristoffelVertex a e z₀ 0).im ≤
      (schwarzChristoffelVertex a e z₀ 0).im := le_rfl
    exact (convex_halfSpace_im_ge _).segment_subset hinfty hzero hz

/-- **The convex Schwarz--Christoffel polygon interior lies strictly above its closing line.**
Here the polygon interior is represented by the interior of the closed convex hull of its
boundary. -/
theorem im_schwarzChristoffelVertex_zero_lt_of_mem_interior_closedConvexHull_boundary
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) {z : ℂ}
    (hz : z ∈ interior (closedConvexHull ℝ
      ((schwarzChristoffelPolygon a e z₀).boundary ℝ))) :
    (schwarzChristoffelVertex a e z₀ 0).im < z.im := by
  let H : Set ℂ := {w | (schwarzChristoffelVertex a e z₀ 0).im ≤ w.im}
  have hhull : closedConvexHull ℝ ((schwarzChristoffelPolygon a e z₀).boundary ℝ) ⊆ H :=
    closedConvexHull_min
      (schwarzChristoffelPolygon_boundary_subset_halfSpace a e z₀ ha he hsum)
      (convex_halfSpace_im_ge _) (isClosed_le continuous_const Complex.continuous_im)
  have hzH := interior_mono hhull hz
  simpa only [H, interior_setOfPred_le_im, mem_ofPred_eq] using hzH

/-- **The convex Schwarz--Christoffel polygon interior misses its closing sides.**  Here the
polygon interior is represented by the interior of the closed convex hull of its boundary. -/
theorem disjoint_interior_closedConvexHull_schwarzChristoffelPolygon_closingSides
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    Disjoint
      (interior (closedConvexHull ℝ ((schwarzChristoffelPolygon a e z₀).boundary ℝ)))
      ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last n).castSucc ∪
        (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 1))) := by
  rw [schwarzChristoffelPolygon_edgeSet_last_prevertex,
    schwarzChristoffelPolygon_edgeSet_last, Set.disjoint_left]
  intro w hw hside
  have hwlt :=
    im_schwarzChristoffelVertex_zero_lt_of_mem_interior_closedConvexHull_boundary
      a e z₀ ha he hsum hw
  have hinfty := im_schwarzChristoffelVertexAtInfinity_eq_im_zero a e z₀ ha he hsum
  have hlast := im_schwarzChristoffelVertex_last_eq_im_zero a e z₀ ha he hsum
  rcases hside with hside | hside
  · have hle := (convex_halfSpace_im_le _).segment_subset hlast.le hinfty.le hside
    exact (not_le_of_gt hwlt) hle
  · have hzero : (schwarzChristoffelVertex a e z₀ 0).im ≤
        (schwarzChristoffelVertex a e z₀ 0).im := le_rfl
    have hle := (convex_halfSpace_im_le _).segment_subset hinfty.le hzero hside
    exact (not_le_of_gt hwlt) hle

/-- **Every value of the Schwarz--Christoffel primitive lies strictly above the closing line.**
The image lies in the filled hull of the polygon boundary, hence in its closed convex hull and in
the closed half-plane above the closing side. Openness of the image upgrades the weak inequality
to a strict one. -/
theorem im_schwarzChristoffelVertex_zero_lt_primitive
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    (schwarzChristoffelVertex a e z₀ 0).im <
      (schwarzChristoffelPrimitive a e z₀ z).im := by
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using (he k).1
  have hinfty : ∑ k, e k < -1 := by rw [hsum]; norm_num
  apply im_schwarzChristoffelVertex_zero_lt_of_mem_interior_closedConvexHull_boundary
    a e z₀ ha he hsum
  rw [← range_schwarzChristoffelCompactifiedBoundary a e z₀ ha.monotone hfinite hinfty]
  exact image_schwarzChristoffelPrimitive_subset_interior_closedConvexHull
    a e z₀ hfinite hinfty (mem_image_of_mem _ hz)

/-- **The upper-half-plane image misses the closing sides of the Schwarz--Christoffel polygon.**
Both closing segments lie on the horizontal line through the first finite vertex, while every
interior value lies strictly above that line. -/
theorem disjoint_image_schwarzChristoffelPrimitive_closingSides
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    Disjoint (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
      ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last n).castSucc ∪
        (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 1))) := by
  apply (disjoint_interior_closedConvexHull_schwarzChristoffelPolygon_closingSides
    a e z₀ ha he hsum).mono_left
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using (he k).1
  have hinfty : ∑ k, e k < -1 := by rw [hsum]; norm_num
  rw [← range_schwarzChristoffelCompactifiedBoundary a e z₀ ha.monotone hfinite hinfty]
  exact image_schwarzChristoffelPrimitive_subset_interior_closedConvexHull
    a e z₀ hfinite hinfty

end TauCeti
