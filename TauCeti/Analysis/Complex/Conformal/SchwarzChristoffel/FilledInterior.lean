/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.SimpleMapping
import TauCeti.Analysis.Complex.PlaneSeparation.TwoComponents

/-!
# The filled interior of a simple Schwarz--Christoffel polygon

A simple compactified Schwarz--Christoffel boundary is a Jordan curve. By the Jordan curve
theorem its bounded complementary component is the filled hull of the boundary minus the
boundary itself. The Schwarz--Christoffel primitive maps the upper half-plane
bijectively onto this filled interior. This identifies the target of the direct map without
requiring convexity, including polygons with reentrant corners.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Complex Set Metric Topology UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The image of the Schwarz--Christoffel primitive bounded by a simple compactified
boundary is exactly the filled hull of that boundary with the boundary removed. -/
theorem image_schwarzChristoffelPrimitive_eq_filledHull_sdiff
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet =
      filledHull (range (schwarzChristoffelCompactifiedBoundary a e z₀)) \
        range (schwarzChristoffelCompactifiedBoundary a e z₀) := by
  let C := range (schwarzChristoffelCompactifiedBoundary a e z₀)
  have hJ : IsJordanCurve C :=
    isJordanCurve_range_schwarzChristoffelCompactifiedBoundary a e z₀ hfinite hinfty hinj
  have hb : schwarzChristoffelPrimitive a e z₀ z₀ ∈
      schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet :=
    mem_image_of_mem _ z₀.im_pos
  have hbase : schwarzChristoffelPrimitive a e z₀ z₀ ∈ filledHull C \ C := by
    exact ⟨image_schwarzChristoffelPrimitive_subset_filledHull a e z₀ hfinite hinfty hb,
      Set.disjoint_left.mp (disjoint_image_schwarzChristoffelPrimitive_range
        a e z₀ hfinite hinfty hinj) hb⟩
  -- The image is the bounded complementary component selected by the base point.
  rw [image_schwarzChristoffelPrimitive_eq_connectedComponentIn a e z₀ hfinite hinfty hinj]
  exact (hJ.filledHull_sdiff_eq_connectedComponentIn hbase).symm

/-- A simple compactified Schwarz--Christoffel boundary makes the primitive a bijection
from the upper half-plane onto the filled polygon interior. -/
theorem bijOn_schwarzChristoffelPrimitive_filledHull_sdiff
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    BijOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet
      (filledHull (range (schwarzChristoffelCompactifiedBoundary a e z₀)) \
        range (schwarzChristoffelCompactifiedBoundary a e z₀)) := by
  have h := bijOn_schwarzChristoffelPrimitive_of_simple_boundary
    a e z₀ hfinite hinfty hinj
  rw [← image_schwarzChristoffelPrimitive_eq_connectedComponentIn
    a e z₀ hfinite hinfty hinj] at h
  rw [← image_schwarzChristoffelPrimitive_eq_filledHull_sdiff
    a e z₀ hfinite hinfty hinj]
  exact h

end TauCeti
