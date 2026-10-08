/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.VertexSector
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Geometry

/-!
# Local polygon pieces around a vertex cycle

Following the side pairings from vertex `j` transports it to `next^[m] j` by
`partialCycleMap j m`. Pulling the polygon at that vertex back by the inverse partial product
therefore gives a tile meeting the original vertex. Near a finite vertex, any finite union of
these tiles agrees with the union of their pulled-back vertex sectors. In particular, the
sector union contains a neighbourhood exactly when the tile union does. This reduces local
vertex coverage to the angular geometry of the incident sectors, without assuming a cycle
angle condition or coverage.

Consecutive sectors lie on opposite sides of their common supporting geodesic. The construction
allows partial products extending beyond a full cycle, as needed when several circuits are
required around an elliptic vertex.

## References

Beardon, *The Geometry of Discrete Groups*, Chapter 9. Walkden, *Hyperbolic geometry*,
§§17 and 19–20 (vertex cycles and the local tessellation in Poincaré's polygon theorem).
-/

public section

open Set Topology UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-- Successive pulled-back sectors are separated by the supporting geodesic of the side
leaving the current vertex. -/
theorem inv_map_smul_vertexSector_next_subset_closure_rightHalfPlane (j : Fin n) :
    (σ.map j)⁻¹ • P.vertexSector (σ.next j) ⊆
      closure (rightHalfPlane (P.sideGeodesic j)) := by
  have h := smul_set_mono (a := (σ.map j)⁻¹)
    (fun z hz ↦ ((P.mem_vertexSector_iff (σ.next j) z).1 hz).1)
  rw [next_apply, add_sub_cancel_right, ← σ.map_pair, ← closure_smul,
    σ.map_smul_leftHalfPlane, σ.pair_pair] at h
  simpa only [map_pair, next_apply] using h

/-- The interiors of consecutive vertex sectors are disjoint, including when a side is
paired with itself. -/
theorem disjoint_inv_map_smul_vertexSector_next_interior_vertexSector (j : Fin n) :
    Disjoint ((σ.map j)⁻¹ • P.vertexSector (σ.next j)) (interior (P.vertexSector j)) := by
  refine Set.disjoint_left.2 fun z hz hzi ↦ ?_
  have hr := σ.inv_map_smul_vertexSector_next_subset_closure_rightHalfPlane j hz
  have hl := ((P.mem_interior_vertexSector_iff j z).1 hzi).2
  rw [mem_closure_rightHalfPlane_iff] at hr
  rw [mem_leftHalfPlane_iff] at hl
  exact (not_lt_of_ge hr) hl

/-- In the common coordinate at the initial vertex, each sector misses the interior of the
preceding sector. This is adjacent-sector separation, without a claim about nonadjacent sectors. -/
theorem disjoint_inv_partialCycleMap_smul_vertexSector_succ_interior (j : Fin n) (m : ℕ) :
    Disjoint
      ((σ.partialCycleMap j (m + 1))⁻¹ • P.vertexSector (σ.next^[m + 1] j))
      ((σ.partialCycleMap j m)⁻¹ • interior (P.vertexSector (σ.next^[m] j))) := by
  rw [partialCycleMap_succ, mul_inv_rev, mul_smul, Function.iterate_succ_apply',
    Set.disjoint_smul_set]
  exact σ.disjoint_inv_map_smul_vertexSector_next_interior_vertexSector (σ.next^[m] j)

/-- Near the initial finite vertex, every tile in a vertex cycle equals its pulled-back
sector. This holds also for partial products extending beyond one circuit. -/
theorem eventuallyEq_inv_partialCycleMap_smul_carrier_vertexSector {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) (m : ℕ) :
    (σ.partialCycleMap j m)⁻¹ • P.carrier =ᶠ[𝓝 z]
      (σ.partialCycleMap j m)⁻¹ • P.vertexSector (σ.next^[m] j) := by
  have hvertex : ((σ.partialCycleMap j m)⁻¹ • P).vertex (σ.next^[m] j) = .inl z := by
    rw [vertex_smul, ← σ.partialCycleMap_smul_vertex j m, inv_smul_smul, hz]
  simpa only [carrier_smul, vertexSector_smul] using
    ((σ.partialCycleMap j m)⁻¹ • P).eventuallyEq_carrier_vertexSector hvertex

/-- A finite fan of tiles along a vertex cycle locally equals its fan of sectors. -/
theorem eventuallyEq_iUnion_inv_partialCycleMap_smul_carrier_vertexSector {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) (r : ℕ) :
    (⋃ m ∈ Finset.range r, (σ.partialCycleMap j m)⁻¹ • P.carrier) =ᶠ[𝓝 z]
      ⋃ m ∈ Finset.range r,
        (σ.partialCycleMap j m)⁻¹ • P.vertexSector (σ.next^[m] j) :=
  (Finset.range r).eventuallyEqSet_iUnion fun m _ ↦
    σ.eventuallyEq_inv_partialCycleMap_smul_carrier_vertexSector hz m

/-- The cycle tiles cover a neighbourhood of a finite vertex if and only if their sectors
cover one. No angular coverage is assumed in deriving this equivalence. -/
theorem mem_interior_iUnion_inv_partialCycleMap_smul_carrier_iff {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) (r : ℕ) :
    z ∈ interior (⋃ m ∈ Finset.range r, (σ.partialCycleMap j m)⁻¹ • P.carrier) ↔
      z ∈ interior (⋃ m ∈ Finset.range r,
        (σ.partialCycleMap j m)⁻¹ • P.vertexSector (σ.next^[m] j)) :=
  (σ.eventuallyEq_iUnion_inv_partialCycleMap_smul_carrier_vertexSector hz r).mem_interior_iff

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
