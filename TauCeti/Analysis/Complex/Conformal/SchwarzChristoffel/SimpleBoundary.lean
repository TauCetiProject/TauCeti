/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Image
import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve

/-!
# The Schwarz--Christoffel image of a simple boundary polygon

Let `F = schwarzChristoffelPrimitive a e z₀` and let `P` be the range of the compactified boundary
path `schwarzChristoffelCompactifiedBoundary a e z₀`, under the standing assumptions of
`TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Image`: every finite prevertex is
integrable and the total exponent is less than `-1`. No convexity is assumed: the turning
exponents may have either sign, so the polygon may have reentrant corners.

When the compactified boundary path is injective, `P` is a Jordan curve, and the image of the
upper half-plane **does not meet `P`**: the image is open and lies in the filled hull of `P`, and
an open set in the filled hull of a Jordan curve misses the curve
(`TauCeti.IsJordanCurve.disjoint_of_isOpen_of_subset_filledHull`). Consequently the image is
exactly one complementary component of `P`, and its frontier is all of `P`.

Over that component, `TauCeti.isCoveringMapOn_schwarzChristoffelPrimitive` therefore exhibits the
whole upper half-plane as a covering space. For convex data the covering is a bijection onto the
interior of the polygon, `TauCeti.bijOn_schwarzChristoffelPrimitive_interior_closedConvexHull`.

## Main results

* `TauCeti.disjoint_image_schwarzChristoffelPrimitive_range` — the image of the upper half-plane
  misses a simple compactified boundary path.
* `TauCeti.image_schwarzChristoffelPrimitive_eq_connectedComponentIn` — the image is the
  component of the complement of the path containing `F z₀`.
* `TauCeti.frontier_image_schwarzChristoffelPrimitive_eq_range` — the frontier of the image is the
  whole path.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **The Schwarz--Christoffel image misses a simple boundary path.** If every finite prevertex is
integrable, the total exponent is less than `-1`, and the compactified boundary path is injective,
then the primitive sends no point of the upper half-plane onto that path. -/
theorem disjoint_image_schwarzChristoffelPrimitive_range (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    Disjoint (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
      (range (schwarzChristoffelCompactifiedBoundary a e z₀)) :=
  (isJordanCurve_range_schwarzChristoffelCompactifiedBoundary a e z₀ hfinite hinfty hinj)
    |>.disjoint_of_isOpen_of_subset_filledHull
      (isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl)
      (image_schwarzChristoffelPrimitive_subset_filledHull a e z₀ hfinite hinfty)

/-- **The Schwarz--Christoffel image is a complementary component of a simple boundary path.**
Under the hypotheses of `TauCeti.disjoint_image_schwarzChristoffelPrimitive_range`, the image of the
upper half-plane is the component of the complement of the compactified boundary path containing
the image of the base point. -/
theorem image_schwarzChristoffelPrimitive_eq_connectedComponentIn (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet =
      connectedComponentIn (range (schwarzChristoffelCompactifiedBoundary a e z₀))ᶜ
        (schwarzChristoffelPrimitive a e z₀ z₀) := by
  have hdisj := disjoint_image_schwarzChristoffelPrimitive_range a e z₀ hfinite hinfty hinj
  refine image_schwarzChristoffelPrimitive_eq_of_subset a e z₀ hfinite hinfty
    isPreconnected_connectedComponentIn
    (disjoint_left.mpr fun w hw => connectedComponentIn_subset _ _ hw) ?_
  exact ((convex_halfSpace_im_gt 0).isPreconnected.image _
    (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn).subset_connectedComponentIn
    (mem_image_of_mem _ z₀.im_pos) (subset_compl_iff_disjoint_right.mpr hdisj)

/-- **The frontier of the Schwarz--Christoffel image is a simple boundary path.** Under the
hypotheses of `TauCeti.disjoint_image_schwarzChristoffelPrimitive_range`, the frontier of the image
of the upper half-plane is the whole range of the compactified boundary path. -/
@[simp]
theorem frontier_image_schwarzChristoffelPrimitive_eq_range (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    frontier (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) =
      range (schwarzChristoffelCompactifiedBoundary a e z₀) := by
  rw [frontier_image_schwarzChristoffelPrimitive a e z₀ hfinite hinfty,
    (disjoint_image_schwarzChristoffelPrimitive_range a e z₀ hfinite hinfty hinj).sdiff_eq_right]

end TauCeti
