/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import TauCeti.Data.Fin.Basic

/-!
# The local sector at a polygon vertex

The sector at a vertex of a convex hyperbolic polygon is the intersection of the closed left
half-planes of its incoming and outgoing sides. The polygon lies in this sector and, near a
finite vertex, agrees with it: all the nonincident side inequalities are strict at that vertex.
This identifies the actual local polygon pieces used when assembling tiles around a vertex.

At an ideal vertex placed at `∞`, the sector is the vertical strip between the verticals through
the two neighbouring vertices, and it has positive width. The polygon agrees with this strip
above some height, that is, along `UpperHalfPlane.atImInfty`: every nonincident side is a
semicircle with `∞` strictly on its left.

The construction commutes with projective transformations and cyclic relabelling, allowing the
same local description to be used for translated polygon tiles.

## Main results

* `ConvexPolygon.eventuallyEq_carrier_vertexSector`: near a finite vertex, the polygon is its
  sector.
* `ConvexPolygon.mem_vertexSector_iff_of_vertex_eq_inr_infty`: the sector at a vertex at `∞` is
  a vertical strip.
* `ConvexPolygon.eventuallyEq_carrier_vertexSector_atImInfty`: near a vertex at `∞`, the polygon
  is that strip.

## References

Beardon, *The Geometry of Discrete Groups*, Chapter 9 (the local tessellation at a vertex in
Poincaré's polygon theorem). Walkden, *Hyperbolic geometry*, §§14.2 and 19–20.
-/

public section

open Set Topology UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint

namespace TauCeti.UpperHalfPlane.ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n)

/-- The closed sector bounded by the incoming and outgoing supporting geodesics at vertex `j`.
At a finite vertex this is the local polygon piece. -/
def vertexSector (j : Fin n) : Set ℍ :=
  closure (leftHalfPlane (P.sideGeodesic (j - 1))) ∩
    closure (leftHalfPlane (P.sideGeodesic j))

/-- The vertex sector is the intersection of the two incident closed half-planes. -/
theorem vertexSector_def (j : Fin n) :
    P.vertexSector j = closure (leftHalfPlane (P.sideGeodesic (j - 1))) ∩
      closure (leftHalfPlane (P.sideGeodesic j)) :=
  (rfl)

/-- Membership in a vertex sector is given by the two incident side inequalities. -/
@[simp]
theorem mem_vertexSector_iff (j : Fin n) (z : ℍ) :
    z ∈ P.vertexSector j ↔ z ∈ closure (leftHalfPlane (P.sideGeodesic (j - 1))) ∧
      z ∈ closure (leftHalfPlane (P.sideGeodesic j)) :=
  Iff.rfl

/-- Vertex sectors are closed. -/
theorem isClosed_vertexSector (j : Fin n) : IsClosed (P.vertexSector j) :=
  isClosed_closure.inter isClosed_closure

/-- The interior of the sector is cut out by the two strict incident side inequalities. -/
theorem interior_vertexSector (j : Fin n) :
    interior (P.vertexSector j) = leftHalfPlane (P.sideGeodesic (j - 1)) ∩
      leftHalfPlane (P.sideGeodesic j) := by
  rw [vertexSector_def, interior_inter, interior_closure_leftHalfPlane,
    interior_closure_leftHalfPlane]

/-- Membership in the sector interior is given by the two strict incident side inequalities. -/
@[simp]
theorem mem_interior_vertexSector_iff (j : Fin n) (z : ℍ) :
    z ∈ interior (P.vertexSector j) ↔ z ∈ leftHalfPlane (P.sideGeodesic (j - 1)) ∧
      z ∈ leftHalfPlane (P.sideGeodesic j) := by
  rw [interior_vertexSector, mem_inter_iff]

/-- The polygon is contained in each of its vertex sectors. -/
theorem carrier_subset_vertexSector (j : Fin n) : P.carrier ⊆ P.vertexSector j :=
  subset_inter (P.carrier_subset_closure_leftHalfPlane (j - 1))
    (P.carrier_subset_closure_leftHalfPlane j)

/-- Moving the polygon moves its vertex sectors. -/
@[simp]
theorem vertexSector_smul (g : PSL(2, ℝ)) (j : Fin n) :
    (g • P).vertexSector j = g • P.vertexSector j := by
  rw [vertexSector_def, vertexSector_def, P.closure_leftHalfPlane_sideGeodesic_smul,
    P.closure_leftHalfPlane_sideGeodesic_smul, smul_set_inter]

/-- Cyclic relabelling relabels the vertex sectors. -/
@[simp]
theorem vertexSector_rotate (k j : Fin n) :
    (P.rotate k).vertexSector j = P.vertexSector (j + k) := by
  simp only [vertexSector_def, sideGeodesic_rotate, sub_add_eq_add_sub]

/-- The polygon agrees with the sector at `j` along any filter on which the open left half-plane
of every side having `vertex j` strictly on its left is eventually entered. -/
theorem eventuallyEq_carrier_vertexSector_of_eventually {l : Filter ℍ} {j : Fin n}
    (h : ∀ i, P.vertex j ∈ extLeftHalfPlane (P.sideGeodesic i) →
      ∀ᶠ w in l, w ∈ leftHalfPlane (P.sideGeodesic i)) :
    P.carrier =ᶠ[l] P.vertexSector j := by
  -- the sides not incident to `j` have `vertex j` strictly on their left
  have hlocal : ∀ᶠ w in l, ∀ i, i ≠ j - 1 → i ≠ j → w ∈ leftHalfPlane (P.sideGeodesic i) := by
    refine Filter.eventually_all.2 fun i ↦ ?_
    by_cases hi : i = j - 1 ∨ i = j
    · exact Filter.Eventually.of_forall fun _ h₁ h₂ ↦ (hi.elim h₁ h₂).elim
    · refine (h i (P.vertex_mem_extLeftHalfPlane_sideGeodesic (Ne.symm (not_or.mp hi).2)
        fun h ↦ (not_or.mp hi).1 (by rw [h]; simp))).mono fun _ hw _ _ ↦ hw
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [hlocal] with w hw
  refine ⟨fun h ↦ P.carrier_subset_vertexSector j h, fun h ↦ ?_⟩
  refine (P.mem_carrier_iff w).2 fun i ↦ ?_
  by_cases hi₁ : i = j - 1
  · simpa only [hi₁] using ((P.mem_vertexSector_iff j w).1 h).1
  by_cases hi₂ : i = j
  · simpa only [hi₂] using ((P.mem_vertexSector_iff j w).1 h).2
  exact subset_closure (hw i hi₁ hi₂)

/-- Near a finite vertex, the polygon agrees with the sector bounded by its two incident sides.
No conditions on side pairings or other vertices are needed. -/
theorem eventuallyEq_carrier_vertexSector {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) : P.carrier =ᶠ[𝓝 z] P.vertexSector j := by
  refine P.eventuallyEq_carrier_vertexSector_of_eventually fun i hi ↦ ?_
  rw [hz, inl_mem_extLeftHalfPlane_iff] at hi
  exact (isOpen_leftHalfPlane _).mem_nhds hi

/-! ### The sector at an ideal vertex at `∞` -/

/-- At a vertex at `∞`, the sector is the closed vertical strip between the verticals through
the next and the previous vertex. -/
theorem mem_vertexSector_iff_of_vertex_eq_inr_infty {j : Fin n} (hj : P.vertex j = .inr ∞)
    (z : ℍ) :
    z ∈ P.vertexSector j ↔ (toComplex (P.vertex (j + 1))).re ≤ z.re ∧
      z.re ≤ (toComplex (P.vertex (j - 1))).re := by
  have hprev := P.isGeodesicFromTo_sideGeodesic (j - 1)
  have hnext := P.isGeodesicFromTo_sideGeodesic j
  rw [sub_add_cancel, hj] at hprev
  rw [hj] at hnext
  rw [mem_vertexSector_iff, mem_closure_leftHalfPlane_iff_sideForm_nonpos,
    mem_closure_leftHalfPlane_iff_sideForm_nonpos,
    hprev.sideForm_eq_of_inr_infty_right (hj ▸ P.vertex_ne_vertex_sub_one j).symm,
    hnext.sideForm_eq_of_inr_infty_left (hj ▸ P.vertex_ne_vertex_add_one j).symm, coe_re,
    sub_nonpos, sub_nonpos, and_comm]

/-- At a vertex at `∞`, the vertical through the next vertex lies strictly to the left of the
vertical through the previous vertex, so the sector there is a strip of positive width. -/
theorem re_toComplex_vertex_add_one_lt_of_vertex_eq_inr_infty {j : Fin n}
    (hj : P.vertex j = .inr ∞) :
    (toComplex (P.vertex (j + 1))).re < (toComplex (P.vertex (j - 1))).re := by
  have hprev := P.isGeodesicFromTo_sideGeodesic (j - 1)
  rw [sub_add_cancel, hj] at hprev
  have h := P.sideForm_sideGeodesic_toComplex_neg (i := j - 1) (j := j + 1)
    (hj ▸ (P.vertex_ne_vertex_add_one j).symm)
    (fun h ↦ add_one_add_one_ne_self P.three_le j (by rw [h, sub_add_cancel]))
    (fun h ↦ P.vertex_ne_vertex_add_one j (by rw [sub_add_cancel] at h; rw [h]))
  rwa [hprev.sideForm_eq_of_inr_infty_right (hj ▸ P.vertex_ne_vertex_sub_one j).symm,
    sub_neg] at h

/-- Near an ideal vertex at `∞`, the polygon agrees with the vertical strip of its vertex sector:
above some height, the sides not incident to that vertex impose no constraint. -/
theorem eventuallyEq_carrier_vertexSector_atImInfty {j : Fin n} (hj : P.vertex j = .inr ∞) :
    P.carrier =ᶠ[atImInfty] P.vertexSector j := by
  refine P.eventuallyEq_carrier_vertexSector_of_eventually fun i hi ↦ ?_
  rw [hj, inr_mem_extLeftHalfPlane_iff] at hi
  exact eventually_mem_leftHalfPlane_of_infty_mem_boundaryLeftHalfPlane hi

end TauCeti.UpperHalfPlane.ConvexPolygon
