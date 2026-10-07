/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import TauCeti.Data.Fin.Basic

/-!
# Strict side inequalities at regular polygon boundary points

A point on a polygon side, different from its finite endpoints, lies strictly to the left of
every other supporting geodesic. This follows from strict convexity of geodesic pieces with
one strict endpoint: distinct polygon edges have at least one endpoint strictly left of the
other edge. The result applies equally to finite sides, rays, and sides with two ideal vertices.

This identifies the strict inequalities needed for local tessellation across paired sides.

## References

Beardon, *The Geometry of Discrete Groups*, Chapter 9; Walkden, *Hyperbolic geometry*
(MATH32051 lecture notes, Manchester 2019), §14.2 (convex hyperbolic polygons).
-/

public section

open UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane.ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n)

/-- Away from its finite endpoints, a polygon side is strictly left of every other side's
supporting geodesic. -/
theorem mem_leftHalfPlane_of_mem_side {i j : Fin n} {z : ℍ} (hz : z ∈ P.side i)
    (hzi : Sum.inl z ≠ P.vertex i) (hzi' : Sum.inl z ≠ P.vertex (i + 1)) (hij : i ≠ j) :
    z ∈ leftHalfPlane (P.sideGeodesic j) := by
  rw [P.side_def] at hz
  by_cases hi : i ≠ j + 1
  · exact mem_leftHalfPlane_of_mem_extGeodesicSegment
      (P.vertex_mem_extLeftHalfPlane_sideGeodesic hij hi)
      (P.vertex_mem_extClosedLeftHalfPlane_sideGeodesic j (i + 1)) hz hzi'
  · have hi : i = j + 1 := not_ne_iff.1 hi
    have hi' : i + 1 ≠ j := by
      rw [hi]
      exact add_one_add_one_ne_self P.three_le j
    have hi'' : i + 1 ≠ j + 1 := fun h ↦ hij ((Equiv.addRight (1 : Fin n)).injective h)
    rw [extGeodesicSegment_comm] at hz
    exact mem_leftHalfPlane_of_mem_extGeodesicSegment
      (P.vertex_mem_extLeftHalfPlane_sideGeodesic hi' hi'')
      (P.vertex_mem_extClosedLeftHalfPlane_sideGeodesic j i) hz hzi

end TauCeti.UpperHalfPlane.ConvexPolygon
