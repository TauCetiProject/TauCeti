/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Orientation
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Sides
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

At a finite vertex `z` the sector is an angular sector: measuring oriented angles at `z` from the
ray towards the next vertex, the ray towards the previous vertex sits at the interior angle, and a
point `w ≠ z` lies in the sector exactly when its oriented angle lies between `0` and the interior
angle, and in its interior exactly when the oriented angle lies strictly between them. The
interior angle at a finite vertex is therefore strictly between `0` and `π`. This angular
description is what lets sectors around a vertex be added up in Poincaré's polygon
theorem.

## Main results

* `ConvexPolygon.eventuallyEq_carrier_vertexSector`: near a finite vertex, the polygon agrees
  with its vertex sector.
* `ConvexPolygon.orientedAngle_rayToward_vertex_eq_interiorAngle`: the oriented angle at a finite
  vertex from the outgoing to the incoming ray is the interior angle.
* `ConvexPolygon.mem_vertexSector_iff_toReal_orientedAngle_mem_Icc`,
  `ConvexPolygon.mem_interior_vertexSector_iff_toReal_orientedAngle_mem_Ioo`: the sector at a
  finite vertex and its interior in angular coordinates.
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
open scoped MatrixGroups Pointwise Real OnePoint

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

/-! ### The sector in angular coordinates -/

variable {P}

/-- At a finite vertex, the outgoing side has the left half-plane of the ray towards the next
vertex. -/
private theorem leftHalfPlane_sideGeodesic_eq_rayToward {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) :
    leftHalfPlane (P.sideGeodesic j) = leftHalfPlane (rayToward z (P.vertex (j + 1))) := by
  have hne : (.inl z : ℍ ⊕ OnePoint ℝ) ≠ P.vertex (j + 1) := by
    rw [← hz]
    exact P.vertex_ne_vertex_add_one j
  have hg := P.isGeodesicFromTo_sideGeodesic j
  rw [hz] at hg
  exact (isGeodesicFromTo_rayToward hne).leftHalfPlane_eq hg

/-- At a finite vertex, the left half-plane of the incoming side is the right half-plane of the
ray towards the previous vertex. -/
private theorem leftHalfPlane_sideGeodesic_sub_one_eq_rayToward {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) :
    leftHalfPlane (P.sideGeodesic (j - 1)) = rightHalfPlane (rayToward z (P.vertex (j - 1))) := by
  have hne : (.inl z : ℍ ⊕ OnePoint ℝ) ≠ P.vertex (j - 1) := by
    rw [← hz]
    exact P.vertex_ne_vertex_sub_one j
  have hg := P.isGeodesicFromTo_sideGeodesic (j - 1)
  rw [sub_add_cancel, hz] at hg
  rw [← leftHalfPlane_mul_pslS,
    (isGeodesicFromTo_mul_pslS_iff.2 (isGeodesicFromTo_rayToward hne)).leftHalfPlane_eq hg]

/-- At a finite vertex `z`, a point `w ≠ z` lies in the sector exactly when it is weakly
counterclockwise of the ray towards the next vertex and weakly clockwise of the ray towards the
previous vertex. -/
private theorem mem_vertexSector_iff_sign_orientedAngle {j : Fin n} {z w : ℍ}
    (hz : P.vertex j = .inl z) (hw : z ≠ w) :
    w ∈ P.vertexSector j ↔
      (orientedAngle z (geodesicLine (rayToward z (P.vertex (j - 1))) 1) w).sign ≠ 1 ∧
        (orientedAngle z (geodesicLine (rayToward z (P.vertex (j + 1))) 1) w).sign ≠ -1 := by
  have hright := mem_closure_rightHalfPlane_geodesicBetween_iff
    (B := geodesicLine (rayToward z (P.vertex (j - 1))) 1) hw
  have hleft := mem_closure_leftHalfPlane_geodesicBetween_iff
    (B := geodesicLine (rayToward z (P.vertex (j + 1))) 1) hw
  rw [← rayToward_eq_geodesicBetween z (P.vertex (j - 1))] at hright
  rw [← rayToward_eq_geodesicBetween z (P.vertex (j + 1))] at hleft
  rw [mem_vertexSector_iff, leftHalfPlane_sideGeodesic_sub_one_eq_rayToward hz,
    leftHalfPlane_sideGeodesic_eq_rayToward hz, hright, hleft]

/-- At a finite vertex `z`, a point `w ≠ z` lies in the interior of the sector exactly when it is
strictly counterclockwise of the ray towards the next vertex and strictly clockwise of the ray
towards the previous vertex. -/
private theorem mem_interior_vertexSector_iff_sign_orientedAngle {j : Fin n} {z w : ℍ}
    (hz : P.vertex j = .inl z) (hw : z ≠ w) :
    w ∈ interior (P.vertexSector j) ↔
      (orientedAngle z (geodesicLine (rayToward z (P.vertex (j - 1))) 1) w).sign = -1 ∧
        (orientedAngle z (geodesicLine (rayToward z (P.vertex (j + 1))) 1) w).sign = 1 := by
  have hright := orientedAngle_sign_eq_neg_one_iff
    (B := geodesicLine (rayToward z (P.vertex (j - 1))) 1) hw
  have hleft := orientedAngle_sign_eq_one_iff
    (B := geodesicLine (rayToward z (P.vertex (j + 1))) 1) hw
  rw [← rayToward_eq_geodesicBetween z (P.vertex (j - 1))] at hright
  rw [← rayToward_eq_geodesicBetween z (P.vertex (j + 1))] at hleft
  rw [mem_interior_vertexSector_iff, leftHalfPlane_sideGeodesic_sub_one_eq_rayToward hz,
    leftHalfPlane_sideGeodesic_eq_rayToward hz, hright, hleft]

/-- At a finite vertex, the ray towards the previous vertex contains a point strictly to the left
of the outgoing side. -/
private theorem exists_geodesicBetween_eq_rayToward_vertex_sub_one {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) :
    ∃ C : ℍ, z ≠ C ∧ geodesicBetween z C = rayToward z (P.vertex (j - 1)) ∧
      C ∈ leftHalfPlane (P.sideGeodesic j) := by
  have hj : j - 1 ≠ j := sub_one_ne_self (Nat.le_of_succ_le P.three_le) j
  rcases hq : P.vertex (j - 1) with B | ξ
  · refine ⟨B, fun h ↦ P.vertex_ne_vertex_sub_one j (by rw [hz, hq, h]), (rayToward_inl z B).symm,
      ?_⟩
    have hB := P.vertex_mem_extLeftHalfPlane_sideGeodesic hj
      (fun h ↦ add_one_add_one_ne_self P.three_le j (by rw [← h, sub_add_cancel]))
    rwa [hq, inl_mem_extLeftHalfPlane_iff] at hB
  · have hC : z ≠ geodesicLine (rayToward z (.inr ξ)) 1 := fun h ↦ zero_ne_one
      (geodesicLine_injective _ ((geodesicLine_rayToward_zero z _).trans h))
    have hside : geodesicLine (rayToward z (.inr ξ)) 1 ∈ P.side (j - 1) := by
      rw [side_def, sub_add_cancel, hq, hz, extGeodesicSegment_inr_inl]
      exact ⟨1, Set.mem_Ici.2 zero_le_one, rfl⟩
    refine ⟨_, hC, (rayToward_eq_geodesicBetween z _).symm,
      P.mem_leftHalfPlane_of_mem_side hside (by rw [hq]; exact Sum.inr_ne_inl) ?_ hj.symm⟩
    rw [sub_add_cancel, hz, Ne, Sum.inl.injEq]
    exact hC

/-- At a finite vertex, the ray towards the previous vertex lies strictly counterclockwise of the
ray towards the next vertex. -/
private theorem sign_orientedAngle_rayToward_vertex {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) :
    (orientedAngle z (geodesicLine (rayToward z (P.vertex (j + 1))) 1)
      (geodesicLine (rayToward z (P.vertex (j - 1))) 1)).sign = 1 := by
  obtain ⟨C, hzC, hC, hCl⟩ := P.exists_geodesicBetween_eq_rayToward_vertex_sub_one hz
  rw [orientedAngle_def, ← rayToward_eq_geodesicBetween z (P.vertex (j - 1)), ← hC,
    ← orientedAngle_def, orientedAngle_sign_eq_one_iff hzC, ← rayToward_eq_geodesicBetween,
    ← leftHalfPlane_sideGeodesic_eq_rayToward hz]
  exact hCl

/-- At a finite vertex `z`, the oriented angle at `z` from the ray towards the next vertex to the
ray towards the previous vertex is the interior angle. The rays are represented by their points
at parameter `1`. -/
theorem orientedAngle_rayToward_vertex_eq_interiorAngle {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) :
    orientedAngle z (geodesicLine (rayToward z (P.vertex (j + 1))) 1)
      (geodesicLine (rayToward z (P.vertex (j - 1))) 1) = P.interiorAngle j := by
  rw [interiorAngle_def, hz, vertexAngle_inl_eq_interiorAngle, UpperHalfPlane.interiorAngle_comm,
    interiorAngle_eq_abs_toReal_orientedAngle]
  exact (Real.Angle.coe_abs_toReal_of_sign_nonneg
    (by rw [P.sign_orientedAngle_rayToward_vertex hz]; decide)).symm

/-- **The vertex sector in angular coordinates.** At a finite vertex `z`, a point `w ≠ z` lies in
the sector exactly when the oriented angle at `z` from the ray towards the next vertex to `w`
lies between `0` and the interior angle. The ray is represented by its point at parameter `1`. -/
theorem mem_vertexSector_iff_toReal_orientedAngle_mem_Icc {j : Fin n} {z w : ℍ}
    (hz : P.vertex j = .inl z) (hw : z ≠ w) :
    w ∈ P.vertexSector j ↔
      (orientedAngle z (geodesicLine (rayToward z (P.vertex (j + 1))) 1) w).toReal ∈
        Set.Icc 0 (P.interiorAngle j) := by
  have hj : (P.vertex j).isLeft := by simp [hz]
  have hα := P.interiorAngle_lt_pi j
  have hα₀ := P.interiorAngle_pos_of_isLeft_vertex hj
  -- with `D` and `E` the points on the outgoing and incoming rays, the oriented angle from `E` is
  -- `φ - α`, a real number in `(-π, π)` once `0 ≤ φ`
  obtain ⟨D, hD⟩ : ∃ D, D = geodesicLine (rayToward z (P.vertex (j + 1))) 1 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = geodesicLine (rayToward z (P.vertex (j - 1))) 1 := ⟨_, rfl⟩
  have hφ := Real.Angle.neg_pi_lt_toReal (orientedAngle z D w)
  have hφ' := Real.Angle.toReal_le_pi (orientedAngle z D w)
  have hEw : orientedAngle z E w =
      (((orientedAngle z D w).toReal - P.interiorAngle j : ℝ) : Real.Angle) := by
    rw [← orientedAngle_add z E D w, orientedAngle_rev, hD, hE,
      P.orientedAngle_rayToward_vertex_eq_interiorAngle hz, Real.Angle.coe_sub,
      Real.Angle.coe_toReal, neg_add_eq_sub]
  rw [mem_vertexSector_iff_sign_orientedAngle hz hw, ← hD, ← hE, hEw, Ne, Ne,
    ← Real.Angle.toReal_neg_iff_sign_neg, ← Real.Angle.toReal_mem_Ioo_iff_sign_pos, not_lt,
    Set.mem_Icc]
  refine ⟨fun ⟨h₁, h₀⟩ ↦ ⟨h₀, ?_⟩, fun ⟨h₀, h₁⟩ ↦ ⟨?_, h₀⟩⟩
  · by_contra hlt
    rw [Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩] at h₁
    exact h₁ ⟨by linarith, by linarith⟩
  · rw [Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩]
    exact fun h ↦ h.1.not_ge (by linarith)

/-- **The interior of the vertex sector in angular coordinates.** At a finite vertex `z`, a point
`w ≠ z` lies in the interior of the sector exactly when the oriented angle at `z` from the ray
towards the next vertex to `w` lies strictly between `0` and the interior angle. The ray is
represented by its point at parameter `1`. -/
theorem mem_interior_vertexSector_iff_toReal_orientedAngle_mem_Ioo {j : Fin n} {z w : ℍ}
    (hz : P.vertex j = .inl z) (hw : z ≠ w) :
    w ∈ interior (P.vertexSector j) ↔
      (orientedAngle z (geodesicLine (rayToward z (P.vertex (j + 1))) 1) w).toReal ∈
        Set.Ioo 0 (P.interiorAngle j) := by
  have hα := P.interiorAngle_lt_pi j
  have hα₀ := P.interiorAngle_nonneg j
  -- as for the closed sector, the oriented angle from the incoming ray `E` is `φ - α`
  obtain ⟨D, hD⟩ : ∃ D, D = geodesicLine (rayToward z (P.vertex (j + 1))) 1 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = geodesicLine (rayToward z (P.vertex (j - 1))) 1 := ⟨_, rfl⟩
  have hφ := Real.Angle.neg_pi_lt_toReal (orientedAngle z D w)
  have hφ' := Real.Angle.toReal_le_pi (orientedAngle z D w)
  have hEw : orientedAngle z E w =
      (((orientedAngle z D w).toReal - P.interiorAngle j : ℝ) : Real.Angle) := by
    rw [← orientedAngle_add z E D w, orientedAngle_rev, hD, hE,
      P.orientedAngle_rayToward_vertex_eq_interiorAngle hz, Real.Angle.coe_sub,
      Real.Angle.coe_toReal, neg_add_eq_sub]
  rw [mem_interior_vertexSector_iff_sign_orientedAngle hz hw, ← hD, ← hE, hEw,
    ← Real.Angle.toReal_neg_iff_sign_neg, ← Real.Angle.toReal_mem_Ioo_iff_sign_pos, Set.mem_Ioo,
    Set.mem_Ioo]
  refine ⟨fun ⟨h₁, h₀, _⟩ ↦ ⟨h₀, ?_⟩, fun ⟨h₀, h₁⟩ ↦ ⟨?_, h₀, by linarith⟩⟩
  · rw [Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩] at h₁
    linarith
  · rw [Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩]
    linarith

end TauCeti.UpperHalfPlane.ConvexPolygon
