/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import TauCeti.Data.Fin.Basic

/-!
# Strict side inequalities for convex hyperbolic polygons

Distinct sides of a convex polygon have distinct supporting geodesic lines. Every point on a
side other than its finite endpoints lies strictly to the left of all the other supporting
lines. This identifies regular edge points by strict inequalities and permits local tessellation
arguments without assuming those inequalities separately. The results include ideal vertices:
a side can be a segment, a ray, or a full line.

## Main results

* `ConvexPolygon.range_sideGeodesic_ne`: distinct sides have distinct supporting lines.
* `ConvexPolygon.mem_leftHalfPlane_of_mem_side`: a nonendpoint side point satisfies every
  other side inequality strictly.

## References

Walkden, *Hyperbolic geometry* (Manchester lecture notes, 2019), §14.2 (convex polygons as
intersections of half-planes) and §§19–20 (local tessellation in Poincaré's theorem).
Beardon, *The Geometry of Discrete Groups*, Chapter 9.
-/

public section

open UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane.ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n)

/-- Distinct sides of a convex polygon have distinct supporting geodesic lines, including
when one or both sides have ideal endpoints. -/
theorem range_sideGeodesic_ne {i j : Fin n} (hij : i ≠ j) :
    Set.range (geodesicLine (P.sideGeodesic i)) ≠
      Set.range (geodesicLine (P.sideGeodesic j)) := by
  intro heq
  have hg := P.isGeodesicFromTo_sideGeodesic i
  have hnot : P.vertex i ∉ extLeftHalfPlane (P.sideGeodesic j) ∧
      P.vertex (i + 1) ∉ extLeftHalfPlane (P.sideGeodesic j) := by
    rcases extLeftHalfPlane_eq_or_eq_mul_pslS_of_range_eq heq with h | h
    · rw [h]
      exact ⟨hg.left_notMem_extLeftHalfPlane, hg.right_notMem_extLeftHalfPlane⟩
    · rw [h]
      have hrev := isGeodesicFromTo_mul_pslS_iff.2 hg
      exact ⟨hrev.right_notMem_extLeftHalfPlane, hrev.left_notMem_extLeftHalfPlane⟩
  by_cases hi : i = j + 1
  · apply hnot.2
    apply P.vertex_mem_extLeftHalfPlane_sideGeodesic
    · rw [hi]
      exact add_one_add_one_ne_self P.three_le j
    · rw [hi]
      exact add_one_ne_self (by omega) (j + 1)
  · exact hnot.1 (P.vertex_mem_extLeftHalfPlane_sideGeodesic hij hi)

/-- A point of a side other than its finite endpoints lies strictly to the left of every
other side's supporting geodesic. -/
theorem mem_leftHalfPlane_of_mem_side {i j : Fin n} {z : ℍ} (hz : z ∈ P.side i)
    (hzp : P.vertex i ≠ .inl z) (hzq : P.vertex (i + 1) ≠ .inl z) (hji : j ≠ i) :
    z ∈ leftHalfPlane (P.sideGeodesic j) := by
  rw [P.side_def] at hz
  exact mem_leftHalfPlane_of_mem_extGeodesicSegment (P.isGeodesicFromTo_sideGeodesic i)
    (P.vertex_mem_extClosedLeftHalfPlane_sideGeodesic j i)
    (P.vertex_mem_extClosedLeftHalfPlane_sideGeodesic j (i + 1))
    (P.range_sideGeodesic_ne hji.symm) hz hzp hzq

end TauCeti.UpperHalfPlane.ConvexPolygon
