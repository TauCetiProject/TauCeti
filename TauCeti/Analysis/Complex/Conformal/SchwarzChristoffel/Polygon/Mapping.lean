/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.Image
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.SupportLine
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Covering
import Mathlib.Analysis.Convex.Contractible

/-!
# The convex Schwarz--Christoffel polygon mapping theorem

For strictly ordered real prevertices and turning exponents in `(-1, 0)` summing to `-2`, the
Schwarz--Christoffel primitive maps the upper half-plane bijectively onto the interior of the
closed convex hull of its polygonal boundary.

The supporting-line inequalities for the bounded and closing sides show that this convex interior
does not meet the polygonal boundary.  It is simply connected because it is nonempty and convex.
The primitive is a covering map away from its compactified boundary path, so the covering is
trivial over this interior and gives the desired bijection.

## Main results

* `TauCeti.disjoint_interior_closedConvexHull_schwarzChristoffelPolygon_boundary` -- the convex
  polygon interior misses its boundary.
* `TauCeti.bijOn_schwarzChristoffelPrimitive_interior_closedConvexHull` -- the primitive maps the
  upper half-plane bijectively onto that interior.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

/-- **The convex Schwarz--Christoffel polygon interior is disjoint from its boundary.**  The
interior is represented as the interior of the closed convex hull of the polygonal boundary. -/
theorem disjoint_interior_closedConvexHull_schwarzChristoffelPolygon_boundary
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    Disjoint
      (interior (closedConvexHull ℝ ((schwarzChristoffelPolygon a e z₀).boundary ℝ)))
      ((schwarzChristoffelPolygon a e z₀).boundary ℝ) := by
  rw [Set.disjoint_left]
  intro z hz hzboundary
  rw [schwarzChristoffelPolygon_boundary] at hzboundary
  rcases hzboundary with (hzside | hzside) | hzside
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hzside
    have hd :=
      disjoint_interior_closedConvexHull_schwarzChristoffelPolygon_edgeSet_castSucc_castSucc
        a e z₀ ha he hsum i
    rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc, Set.disjoint_left] at hd
    exact hd hz hi
  · have hd := disjoint_interior_closedConvexHull_schwarzChristoffelPolygon_closingSides
      a e z₀ ha he hsum
    rw [schwarzChristoffelPolygon_edgeSet_last_prevertex,
      schwarzChristoffelPolygon_edgeSet_last, Set.disjoint_left] at hd
    exact hd hz (Or.inl hzside)
  · have hd := disjoint_interior_closedConvexHull_schwarzChristoffelPolygon_closingSides
      a e z₀ ha he hsum
    rw [schwarzChristoffelPolygon_edgeSet_last_prevertex,
      schwarzChristoffelPolygon_edgeSet_last, Set.disjoint_left] at hd
    exact hd hz (Or.inr hzside)

/-- **The Schwarz--Christoffel primitive maps the upper half-plane bijectively onto its convex
polygon interior.**  The target is the interior of the closed convex hull of the polygonal
boundary. -/
theorem bijOn_schwarzChristoffelPrimitive_interior_closedConvexHull
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    BijOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet
      (interior (closedConvexHull ℝ ((schwarzChristoffelPolygon a e z₀).boundary ℝ))) := by
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using (he k).1
  have hinfty : ∑ k, e k < -1 := by rw [hsum]; norm_num
  let W := interior (closedConvexHull ℝ ((schwarzChristoffelPolygon a e z₀).boundary ℝ))
  have hFW : schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ⊆ W := by
    dsimp only [W]
    rw [← range_schwarzChristoffelCompactifiedBoundary a e z₀ ha.monotone hfinite hinfty]
    exact image_schwarzChristoffelPrimitive_subset_interior_closedConvexHull
      a e z₀ hfinite hinfty
  have hWne : W.Nonempty :=
    ⟨schwarzChristoffelPrimitive a e z₀ z₀, hFW (mem_image_of_mem _ z₀.im_pos)⟩
  have hWconvex : Convex ℝ W := by
    dsimp only [W]
    exact convex_closedConvexHull.interior
  let _ : ContractibleSpace W := hWconvex.contractibleSpace hWne
  apply bijOn_schwarzChristoffelPrimitive_of_subset a e z₀ hfinite hinfty
  · rw [range_schwarzChristoffelCompactifiedBoundary a e z₀ ha.monotone hfinite hinfty]
    exact disjoint_interior_closedConvexHull_schwarzChristoffelPolygon_boundary
      a e z₀ ha he hsum
  · exact hFW

end TauCeti
