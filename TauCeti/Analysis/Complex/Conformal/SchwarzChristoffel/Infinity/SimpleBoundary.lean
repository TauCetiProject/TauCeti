/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Covering
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.MultipleEnds.Covering
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.ExteriorPoint
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Jordan
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded
import TauCeti.Analysis.Complex.Conformal.SimplyConnected
import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve

/-!
# The image bounded by a simple unbounded Schwarz--Christoffel chain

For integrable finite prevertices and total exponent in `[-1, 1)`, an injective real boundary
parametrization forces the primitive's interior image to avoid the boundary. Consequently the
primitive maps the upper half-plane bijectively onto the complementary component containing the
base-point image, and its frontier is the whole boundary chain. This gives the direct mapping
theorem for simple unbounded polygons, including parallel-ended polygons.

The same holds at total exponent `1`, an end of opening `2π`, when the logarithmic coefficient
`((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2` is negative. Some sign condition is needed
there: with exponents `-1 / 2` at `-1` and `3 / 2` at `1` the boundary is a simple chain of two
parallel rays joined by a segment, but the corner of opening `5π / 2` makes the image overlap
its boundary.

Inversion about an exterior point reduces separation to the planar Jordan curve theorem: the
inverted image is bounded, its frontier lies on the inverted boundary together with `0`, and
an open subset of the filled hull of a Jordan curve cannot meet that curve.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Bornology Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- A simple proper Schwarz--Christoffel boundary is disjoint from the image of the open upper
half-plane, if the end at infinity has opening less than `2π`, or opening `2π` with negative
logarithmic coefficient. The total exponents `-1` and `1` include parallel outer sides. -/
theorem disjoint_image_schwarzChristoffelPrimitive_range_of_neg_one_le_sum
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hlow : -1 ≤ ∑ i, e i)
    (hhigh : ∑ i, e i < 1 ∨ ∑ i, e i = 1 ∧ (∑ i, e i * a i) ^ 2 < ∑ i, e i * a i ^ 2)
    (hinj : Function.Injective (schwarzChristoffelBoundary a e z₀)) :
    Disjoint (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
      (range (schwarzChristoffelBoundary a e z₀)) := by
  let U := schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet
  let B := range (schwarzChristoffelBoundary a e z₀)
  have hcl : closure U = U ∪ B :=
    closure_image_schwarzChristoffelPrimitive_of_neg_one_le_sum a e z₀ hfinite hlow
  have hBcl : B ⊆ closure U := by rw [hcl]; exact subset_union_right
  have hJ := isJordanCurve_insert_infty_range_schwarzChristoffelBoundary
    a e z₀ hfinite hlow hinj
  have hUb : ¬IsBounded U := fun h =>
    not_isBounded_of_isJordanCurve_insert_infty hJ (h.closure.subset hBcl)
  obtain ⟨q, hq⟩ : ∃ q, q ∉ closure U := by
    rcases hhigh with hhigh | ⟨hsum, hC⟩
    · exact exists_notMem_closure_image_schwarzChristoffelPrimitive_of_sum_lt_one
        a e z₀ hfinite hhigh
    · exact exists_notMem_closure_image_schwarzChristoffelPrimitive_of_sum_eq_one
        a e z₀ hfinite hsum hC
  let κ : ℂ → ℂ := fun z => (z - q)⁻¹
  let C := insert (0 : ℂ) (κ '' B)
  have hC : IsJordanCurve C :=
    isJordanCurve_insert_zero_image_inv_sub (fun h => hq (hBcl h)) hJ
  have hUo : IsOpen U :=
    isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl
  have hVo : IsOpen (κ '' U) := isOpen_image_inv_sub hUo (fun h => hq (subset_closure h))
  have hVcl : closure (κ '' U) = (κ '' U) ∪ C := by
    rw [closure_image_inv_sub hq hUb, hcl, image_union]
    simp only [C, κ, union_insert]
  have hVfr : frontier (κ '' U) ⊆ C := by
    rw [hVo.frontier_eq, hVcl]
    exact fun w hw => hw.1.resolve_left hw.2
  have hdisj := hC.disjoint_of_isOpen_of_subset_filledHull hVo
    (subset_filledHull_of_frontier_subset (isBounded_image_inv_sub hq) hVfr)
  exact disjoint_left.mpr fun w hwU hwB =>
    disjoint_left.mp hdisj (mem_image_of_mem κ hwU)
      (mem_insert_of_mem 0 (mem_image_of_mem κ hwB))

/-- The image of a primitive with a simple proper boundary is the complementary component
containing its base-point image, for total exponent in `[-1, 1)`, or total exponent `1` with
negative logarithmic coefficient. -/
theorem image_schwarzChristoffelPrimitive_eq_connectedComponentIn_of_neg_one_le_sum
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hlow : -1 ≤ ∑ i, e i)
    (hhigh : ∑ i, e i < 1 ∨ ∑ i, e i = 1 ∧ (∑ i, e i * a i) ^ 2 < ∑ i, e i * a i ^ 2)
    (hinj : Function.Injective (schwarzChristoffelBoundary a e z₀)) :
    schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet =
      connectedComponentIn (range (schwarzChristoffelBoundary a e z₀))ᶜ
        (schwarzChristoffelPrimitive a e z₀ z₀) := by
  have hdisj := disjoint_image_schwarzChristoffelPrimitive_range_of_neg_one_le_sum
    a e z₀ hfinite hlow hhigh hinj
  refine image_schwarzChristoffelPrimitive_eq_of_subset_of_neg_one_le_prevertex_sum
    a e z₀ (fun j => (hfinite j).le) isPreconnected_connectedComponentIn ?_ ?_
  · rw [disjoint_image_left,
      preimage_range_schwarzChristoffelSphereBoundary_of_neg_one_le_sum a e z₀ hfinite hlow]
    exact disjoint_left.mpr fun w hw => connectedComponentIn_subset _ _ hw
  exact ((convex_halfSpace_im_gt 0).isPreconnected.image _
    (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn).subset_connectedComponentIn
    (mem_image_of_mem _ z₀.im_pos) (subset_compl_iff_disjoint_right.mpr hdisj)

/-- The frontier of the primitive image is the entire simple proper boundary chain. -/
@[simp]
theorem frontier_image_schwarzChristoffelPrimitive_eq_range_of_neg_one_le_sum
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hlow : -1 ≤ ∑ i, e i)
    (hhigh : ∑ i, e i < 1 ∨ ∑ i, e i = 1 ∧ (∑ i, e i * a i) ^ 2 < ∑ i, e i * a i ^ 2)
    (hinj : Function.Injective (schwarzChristoffelBoundary a e z₀)) :
    frontier (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) =
      range (schwarzChristoffelBoundary a e z₀) := by
  rw [frontier_image_schwarzChristoffelPrimitive_of_neg_one_le_sum a e z₀ hfinite hlow,
    (disjoint_image_schwarzChristoffelPrimitive_range_of_neg_one_le_sum
      a e z₀ hfinite hlow hhigh hinj).sdiff_eq_right]

/-- A Schwarz--Christoffel primitive with a simple proper boundary and total exponent in
`[-1, 1)`, or total exponent `1` with negative logarithmic coefficient
`((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2`, maps the upper half-plane bijectively onto the
complementary region containing its base-point image. This allows reentrant finite corners,
parallel outer sides, and ends of opening `2π`. -/
theorem bijOn_schwarzChristoffelPrimitive_of_simple_boundary_of_neg_one_le_sum
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hlow : -1 ≤ ∑ i, e i)
    (hhigh : ∑ i, e i < 1 ∨ ∑ i, e i = 1 ∧ (∑ i, e i * a i) ^ 2 < ∑ i, e i * a i ^ 2)
    (hinj : Function.Injective (schwarzChristoffelBoundary a e z₀)) :
    BijOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet
      (connectedComponentIn (range (schwarzChristoffelBoundary a e z₀))ᶜ
        (schwarzChristoffelPrimitive a e z₀ z₀)) := by
  let U := schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet
  have hdisj := disjoint_image_schwarzChristoffelPrimitive_range_of_neg_one_le_sum
    a e z₀ hfinite hlow hhigh hinj
  have hJ := isJordanCurve_insert_infty_range_schwarzChristoffelBoundary
    a e z₀ hfinite hlow hinj
  have hUc : IsConnected U :=
    ((convex_halfSpace_im_gt 0).isConnected ⟨z₀, z₀.im_pos⟩).image _
      (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn
  have hfrontier : IsPreconnected (frontier U) := by
    rw [frontier_image_schwarzChristoffelPrimitive_eq_range_of_neg_one_le_sum
      a e z₀ hfinite hlow hhigh hinj]
    exact isPreconnected_range
      (isProperMap_schwarzChristoffelBoundary a e z₀ hfinite hlow).continuous
  -- The frontier chain is unbounded and lies in the complement, so the connected image has
  -- no bounded complementary component. Its proper covering is therefore trivial.
  have hsimply := isSimplyConnected_of_isPreconnected_frontier
    (isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl)
    hUc hfrontier (fun h => not_isBounded_of_isJordanCurve_insert_infty hJ
      (h.subset (subset_compl_iff_disjoint_left.mpr hdisj)))
  have : SimplyConnectedSpace U := hsimply.simplyConnectedSpace
  rw [← image_schwarzChristoffelPrimitive_eq_connectedComponentIn_of_neg_one_le_sum
    a e z₀ hfinite hlow hhigh hinj]
  apply bijOn_schwarzChristoffelPrimitive_of_subset_of_neg_one_le_prevertex_sum
    a e z₀ (fun j => (hfinite j).le) ?_ subset_rfl
  rw [disjoint_image_left,
    preimage_range_schwarzChristoffelSphereBoundary_of_neg_one_le_sum a e z₀ hfinite hlow]
  exact hdisj

end TauCeti
