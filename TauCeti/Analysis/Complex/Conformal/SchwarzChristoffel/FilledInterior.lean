/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.SimpleMapping
import TauCeti.Order.Interval.Finite
import TauCeti.Analysis.Complex.PlaneSeparation.LocalSeparation
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.LocallyStraight
import TauCeti.Algebra.BigOperators.Finset.Fiber

/-!
# The filled interior of a simple Schwarz--Christoffel polygon

A simple compactified Schwarz--Christoffel boundary is a Jordan curve. Its regular edge is
locally straight, so its bounded complementary component is the filled hull of the boundary
minus the boundary itself. The Schwarz--Christoffel primitive maps the upper half-plane
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
  obtain ⟨p, q, x, ha, hx⟩ := exists_Ioo_disjoint_range_of_finite a
  let B := schwarzChristoffelBoundary a e z₀
  let C := range (schwarzChristoffelCompactifiedBoundary a e z₀)
  -- Pick a regular edge beyond every prevertex. Simplicity makes
  -- this part of the compactified boundary locally the only boundary arc.
  obtain ⟨ε, hε, hlocal⟩ := schwarzChristoffelCompactifiedBoundary_locally_openSegment
    a e z₀ (fun i _ => ha i) hfinite hinfty hinj hx
  have hpq : B p ≠ B q := by
    intro heq
    have h : (p : OnePoint ℝ) = (q : OnePoint ℝ) :=
      hinj (by simpa only [B, schwarzChristoffelCompactifiedBoundary_coe] using heq)
    have : p = q := by simpa using h
    exact (ne_of_lt (hx.1.trans hx.2)) this
  have hwseg : B x ∈ openSegment ℝ (B p) (B q) := by
    rw [← schwarzChristoffelBoundary_image_Ioo a e z₀ (hx.1.trans hx.2) (fun i _ => ha i)
      (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite p)
      (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite q)]
    exact ⟨x, hx, rfl⟩
  obtain ⟨δ, hδ, hsegline⟩ := exists_ball_openSegment_eq_line hpq hwseg
  let r := min ε δ
  have hr : 0 < r := lt_min hε hδ
  -- Shrink the edge neighbourhood until its open segment agrees with its line.
  have hline : ∀ z ∈ ball (B x) r,
      (z ∈ C ↔ (((B q - B p)⁻¹ * (z - B x))).im = 0) := by
    intro z hz
    have hzε : z ∈ ball (B x) ε := ball_subset_ball (min_le_left ε δ) hz
    have hzδ : z ∈ ball (B x) δ := ball_subset_ball (min_le_right ε δ) hz
    have hmem : z ∈ C ↔ z ∈ openSegment ℝ (B p) (B q) := by
      have hh := Set.ext_iff.mp hlocal z
      simpa [C, B, Set.mem_inter_iff, hzε] using hh
    exact hmem.trans (hsegline z hzδ)
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
  exact (hJ.filledHull_sdiff_eq_connectedComponentIn_of_locally_eq_line hr
    (B q - B p)⁻¹ hline hbase).symm

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
