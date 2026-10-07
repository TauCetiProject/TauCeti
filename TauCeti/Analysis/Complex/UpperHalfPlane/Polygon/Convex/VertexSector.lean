/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex

/-!
# The local sector at a finite polygon vertex

The sector at a vertex of a convex hyperbolic polygon is the intersection of the closed left
half-planes of its incoming and outgoing sides. The polygon lies in this sector and, near a
finite vertex, agrees with it: all the nonincident side inequalities are strict at that vertex.
This identifies the actual local polygon pieces used when assembling tiles around a vertex.
Ideal vertices are allowed elsewhere in the polygon; the local equality concerns a vertex in
the upper half-plane.

The construction commutes with projective transformations and cyclic relabelling, allowing the
same local description to be used for translated polygon tiles.

## References

Beardon, *The Geometry of Discrete Groups*, Chapter 9 (the local tessellation at a vertex in
Poincaré's polygon theorem). Walkden, *Hyperbolic geometry*, §§14.2 and 19–20.
-/

public section

open Set Topology UpperHalfPlane
open scoped MatrixGroups Pointwise

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

/-- Near a finite vertex, the polygon agrees with the sector bounded by its two incident sides.
No conditions on side pairings or other vertices are needed. -/
theorem eventuallyEq_carrier_vertexSector {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) : P.carrier =ᶠ[𝓝 z] P.vertexSector j := by
  have hlocal : ∀ᶠ w in 𝓝 z, ∀ i, i ≠ j - 1 → i ≠ j →
      w ∈ leftHalfPlane (P.sideGeodesic i) := by
    refine Filter.eventually_all.2 fun i ↦ ?_
    by_cases hi : i = j - 1 ∨ i = j
    · exact Filter.Eventually.of_forall fun _ h₁ h₂ ↦ (hi.elim h₁ h₂).elim
    · have hzi : z ∈ leftHalfPlane (P.sideGeodesic i) := by
        have h := P.vertex_mem_extLeftHalfPlane_sideGeodesic
          (Ne.symm (not_or.mp hi).2) (fun h ↦ (not_or.mp hi).1 (by rw [h]; simp))
        rwa [hz, inl_mem_extLeftHalfPlane_iff] at h
      have hmem : ∀ᶠ w in 𝓝 z, w ∈ leftHalfPlane (P.sideGeodesic i) :=
        (isOpen_leftHalfPlane _).mem_nhds hzi
      exact hmem.mono fun _ hw _ _ ↦ hw
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [hlocal] with w hw
  refine ⟨fun h ↦ P.carrier_subset_vertexSector j h, fun h ↦ ?_⟩
  refine (P.mem_carrier_iff w).2 fun i ↦ ?_
  by_cases hi₁ : i = j - 1
  · simpa only [hi₁] using ((P.mem_vertexSector_iff j w).1 h).1
  by_cases hi₂ : i = j
  · simpa only [hi₂] using ((P.mem_vertexSector_iff j w).1 h).2
  exact subset_closure (hw i hi₁ hi₂)

end TauCeti.UpperHalfPlane.ConvexPolygon
