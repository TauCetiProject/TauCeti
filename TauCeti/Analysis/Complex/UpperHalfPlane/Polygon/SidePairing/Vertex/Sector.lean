/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.VertexSector
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Geometry
import Mathlib.Order.Interval.Set.Union

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

In the common coordinate at a finite vertex, consecutive pulled-back sectors share a boundary ray
and turn clockwise by the successive interior angles. Once these angles add up to at least `2π`
the sectors cover all of `ℍ`, so the tiles cover a neighbourhood of the vertex. This is the local
tessellation at a finite vertex in Poincaré's polygon theorem; for a cycle it applies after `t`
circuits whenever `t` times the angle sum is at least `2π`, in particular for an elliptic cycle
with angle sum `2π / t`.

## Main results

* `SidePairing.mem_interior_iUnion_inv_partialCycleMap_smul_carrier_iff`: the tiles cover a
  neighbourhood of a finite vertex exactly when their pulled-back sectors do.
* `SidePairing.orientedAngle_rayToward_inv_partialCycleMap_smul_vertex`: in the common
  coordinate at a finite vertex, the incoming ray of the `m`-th tile has turned clockwise
  through the first `m` angles.
* `SidePairing.arg_smulDeriv_cycleMap`: the rotation angle of a finite vertex cycle is its
  angle sum modulo `2π`.
* `SidePairing.iUnion_inv_partialCycleMap_smul_vertexSector_eq_univ`: sectors with total angle at
  least `2π` cover `ℍ`.
* `SidePairing.mem_interior_iUnion_inv_partialCycleMap_smul_carrier_of_le_mul_cycleAngleSum`:
  `t` circuits of a finite vertex cycle with total angle at least `2π` cover a neighbourhood of
  the vertex.

## References

Beardon, *The Geometry of Discrete Groups*, Chapter 9. Walkden, *Hyperbolic geometry*,
§§17 and 19–20 (vertex cycles and the local tessellation in Poincaré's polygon theorem).
-/

public section

open Set Topology UpperHalfPlane
open scoped MatrixGroups Pointwise Real

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

/-- The tile at step `m` of a cycle through a finite vertex `z` has `z` as its vertex. -/
theorem inv_partialCycleMap_smul_vertex {j : Fin n} {z : ℍ} (hz : P.vertex j = .inl z)
    (m : ℕ) : ((σ.partialCycleMap j m)⁻¹ • P).vertex (σ.next^[m] j) = .inl z := by
  rw [vertex_smul, ← σ.partialCycleMap_smul_vertex j m, inv_smul_smul, hz]

/-- Near the initial finite vertex, every tile in a vertex cycle equals its pulled-back
sector. This holds also for partial products extending beyond one circuit. -/
theorem eventuallyEq_inv_partialCycleMap_smul_carrier_vertexSector {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) (m : ℕ) :
    (σ.partialCycleMap j m)⁻¹ • P.carrier =ᶠ[𝓝 z]
      (σ.partialCycleMap j m)⁻¹ • P.vertexSector (σ.next^[m] j) := by
  simpa only [carrier_smul, vertexSector_smul] using
    ((σ.partialCycleMap j m)⁻¹ • P).eventuallyEq_carrier_vertexSector
      (σ.inv_partialCycleMap_smul_vertex hz m)

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

/-! ### Coverage of a neighbourhood of a finite vertex -/

/-- In the common coordinate at a finite vertex, the incoming ray of the `m`-th tile is reached
from the incoming ray of the first tile by turning clockwise through the first `m` angles. -/
theorem orientedAngle_rayToward_inv_partialCycleMap_smul_vertex {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) (m : ℕ) :
    orientedAngle z (geodesicLine (rayToward z (P.vertex (j - 1))) 1)
        (geodesicLine (rayToward z
          (((σ.partialCycleMap j m)⁻¹ • P).vertex (σ.next^[m] j - 1))) 1) =
      ((-∑ l ∈ Finset.range m, P.interiorAngle (σ.next^[l] j) : ℝ) : Real.Angle) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := ((σ.partialCycleMap j m)⁻¹ • P).orientedAngle_rayToward_vertex_eq_interiorAngle
      (σ.inv_partialCycleMap_smul_vertex hz m)
    rw [interiorAngle_smul] at h
    -- The `show` supplies the transformed-polygon vertex equality expected by `rw`, before
    -- `vertex_smul` normalizes it to the canonical pointwise side-pairing formula.
    rw [(show (((σ.partialCycleMap j (m + 1))⁻¹ • P).vertex (σ.next^[m + 1] j - 1)) =
        (((σ.partialCycleMap j m)⁻¹ • P).vertex (σ.next^[m] j + 1)) from
      by simpa only [vertex_smul] using σ.inv_partialCycleMap_succ_smul_vertex_sub_one j m),
      ← orientedAngle_add _ _ (geodesicLine
      (rayToward z (((σ.partialCycleMap j m)⁻¹ • P).vertex (σ.next^[m] j - 1))) 1), ih,
      orientedAngle_rev, h, Finset.sum_range_succ]
    simp only [neg_add, Real.Angle.coe_add, Real.Angle.coe_neg]

/-- In the common coordinate at a finite vertex, the outgoing ray of the `m`-th tile is reached
from the incoming ray of the first tile by turning clockwise through the first `m + 1` angles. -/
private theorem orientedAngle_rayToward_inv_partialCycleMap_smul_vertex_add_one {j : Fin n}
    {z : ℍ} (hz : P.vertex j = .inl z) (m : ℕ) :
    orientedAngle z (geodesicLine (rayToward z (P.vertex (j - 1))) 1)
        (geodesicLine (rayToward z
          (((σ.partialCycleMap j m)⁻¹ • P).vertex (σ.next^[m] j + 1))) 1) =
      ((-∑ l ∈ Finset.range (m + 1), P.interiorAngle (σ.next^[l] j) : ℝ) : Real.Angle) := by
  -- Again fix the transformed-polygon vertex type before normalization by `vertex_smul`.
  rw [← (show (((σ.partialCycleMap j (m + 1))⁻¹ • P).vertex (σ.next^[m + 1] j - 1)) =
        (((σ.partialCycleMap j m)⁻¹ • P).vertex (σ.next^[m] j + 1)) from
      by simpa only [vertex_smul] using σ.inv_partialCycleMap_succ_smul_vertex_sub_one j m)]
  exact σ.orientedAngle_rayToward_inv_partialCycleMap_smul_vertex hz (m + 1)

/-- In the common coordinate at a finite vertex, the angle of `w` measured from the outgoing ray of
the `m`-th tile is its angle measured from the incoming ray of the first tile, plus the first
`m + 1` angles. -/
theorem orientedAngle_rayToward_inv_partialCycleMap_smul_vertex_add_one_left {j : Fin n}
    {z : ℍ} (hz : P.vertex j = .inl z) (m : ℕ) (w : ℍ) :
    orientedAngle z (geodesicLine (rayToward z
        (((σ.partialCycleMap j m)⁻¹ • P).vertex (σ.next^[m] j + 1))) 1) w =
      orientedAngle z (geodesicLine (rayToward z (P.vertex (j - 1))) 1) w +
        ((∑ l ∈ Finset.range (m + 1), P.interiorAngle (σ.next^[l] j) : ℝ) : Real.Angle) := by
  rw [← orientedAngle_add _ _ (geodesicLine (rayToward z (P.vertex (j - 1))) 1), orientedAngle_rev,
    σ.orientedAngle_rayToward_inv_partialCycleMap_smul_vertex_add_one hz m, Real.Angle.coe_neg,
    neg_neg, add_comm]

/-- The cycle transformation at a finite vertex rotates its tangent space counterclockwise
through the cycle angle sum, modulo `2π`. This does not require discreteness or no-overlap. -/
theorem arg_smulDeriv_cycleMap {j : Fin n} {z : ℍ} (hz : P.vertex j = .inl z) :
    ((Matrix.ProjectiveSpecialLinearGroup.smulDeriv (σ.cycleMap j) z).arg : Real.Angle) =
      (σ.cycleAngleSum j : Real.Angle) := by
  have hfix : σ.cycleMap j • z = z := by
    simpa only [hz, Sum.smul_inl, Sum.inl.injEq] using σ.cycleMap_smul_vertex j
  have hinv : (σ.cycleMap j)⁻¹ • z = z := by simp [inv_smul_eq_iff, hfix]
  have hne : Sum.inl z ≠ P.vertex (j - 1) := by
    rw [← hz]
    exact P.vertex_ne_vertex_sub_one j
  have hray : rayToward z ((σ.cycleMap j)⁻¹ • P.vertex (j - 1)) =
      (σ.cycleMap j)⁻¹ * rayToward z (P.vertex (j - 1)) := by
    simpa only [hinv] using rayToward_smul (σ.cycleMap j)⁻¹ hne
  have hangle := σ.orientedAngle_rayToward_inv_partialCycleMap_smul_vertex hz
    (σ.cycleLength j)
  rw [vertex_smul, σ.next_iterate_cycleLength, ← σ.cycleMap_def, hray,
    ← smul_geodesicLine] at hangle
  have hE : z ≠ geodesicLine (rayToward z (P.vertex (j - 1))) 1 := by
    intro h
    exact zero_ne_one (geodesicLine_injective _ ((geodesicLine_rayToward_zero _ _).trans h))
  have hderiv : Matrix.ProjectiveSpecialLinearGroup.smulDeriv (σ.cycleMap j)⁻¹ z =
      (Matrix.ProjectiveSpecialLinearGroup.smulDeriv (σ.cycleMap j) z)⁻¹ := by
    simpa only [hfix] using
      Matrix.ProjectiveSpecialLinearGroup.smulDeriv_inv (σ.cycleMap j) z
  rw [orientedAngle_smul_right_of_smul_eq_self hinv hE, hderiv, Complex.arg_inv_coe_angle,
    ← σ.cycleAngleSum_eq_sum_range, Real.Angle.coe_neg] at hangle
  exact neg_injective hangle

/-- **The vertex sectors along a cycle cover the plane once their angles reach `2π`.** Pull back
the sectors of the vertices `next^[m] j`, `m < r`, to the finite vertex `z = vertex j` by the
inverse partial cycle maps. If their interior angles sum to at least `2π`, these sectors turn
around `z` through a full circle, so their union is all of `ℍ`. -/
theorem iUnion_inv_partialCycleMap_smul_vertexSector_eq_univ {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) {r : ℕ}
    (hr : 2 * π ≤ ∑ m ∈ Finset.range r, P.interiorAngle (σ.next^[m] j)) :
    ⋃ m ∈ Finset.range r, (σ.partialCycleMap j m)⁻¹ • P.vertexSector (σ.next^[m] j) =
      Set.univ := by
  set B : ℕ → ℝ := fun m ↦ ∑ l ∈ Finset.range m, P.interiorAngle (σ.next^[l] j) with hB
  have hr₀ : r ≠ 0 := by
    rintro rfl
    simp only [Finset.range_zero, Finset.sum_empty] at hr
    linarith [Real.pi_pos]
  refine Set.eq_univ_of_forall fun w ↦ Set.mem_iUnion₂.2 ?_
  simp only [Finset.mem_range]
  rcases eq_or_ne z w with rfl | hw
  · refine ⟨0, Nat.pos_of_ne_zero hr₀, ?_⟩
    simpa using P.carrier_subset_vertexSector j (P.vertex_mem_carrier hz)
  -- measure `w` clockwise from the incoming ray `E` of the first tile, by `-x ∈ [0, 2π)`
  set E := geodesicLine (rayToward z (P.vertex (j - 1))) 1
  obtain ⟨x, hx, hxw⟩ :
      ∃ x : ℝ, x ∈ Set.Ioc (-(2 * π)) 0 ∧ (x : Real.Angle) = orientedAngle z E w := by
    have h₁ := Real.Angle.neg_pi_lt_toReal (orientedAngle z E w)
    have h₂ := Real.Angle.toReal_le_pi (orientedAngle z E w)
    by_cases h : (orientedAngle z E w).toReal ≤ 0
    · exact ⟨_, ⟨by linarith [Real.pi_pos], h⟩, Real.Angle.coe_toReal _⟩
    · refine ⟨(orientedAngle z E w).toReal - 2 * π, ⟨by linarith, by linarith⟩, ?_⟩
      rw [Real.Angle.coe_sub, Real.Angle.coe_two_pi, sub_zero, Real.Angle.coe_toReal]
  -- the tile whose sector has turned past `w`
  have hxB : -x ∈ Set.Ico (B 0) (B r) := by
    simp only [hB, Finset.range_zero, Finset.sum_empty, Set.mem_Ico]
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  obtain ⟨m, hmr, hm', hm⟩ := Set.mem_iUnion₂.1 (Ico_subset_biUnion_Ico r B hxB)
  rw [Finset.mem_range] at hmr
  refine ⟨m, hmr, ?_⟩
  -- in the coordinate of the `m`-th tile, `w` is at angle `x + B (m + 1) ∈ [0, α m]`
  have hsucc : B (m + 1) = B m + P.interiorAngle (σ.next^[m] j) := Finset.sum_range_succ _ _
  have hle := P.interiorAngle_le_pi (σ.next^[m] j)
  have hangle : (orientedAngle z (geodesicLine (rayToward z
      (((σ.partialCycleMap j m)⁻¹ • P).vertex (σ.next^[m] j + 1))) 1) w).toReal =
        x + B (m + 1) := by
    rw [σ.orientedAngle_rayToward_inv_partialCycleMap_smul_vertex_add_one_left hz m w, ← hxw,
      ← Real.Angle.coe_add, Real.Angle.toReal_coe_eq_self_iff]
    exact ⟨by linarith [Real.pi_pos], by linarith⟩
  rw [← vertexSector_smul,
    ((σ.partialCycleMap j m)⁻¹ • P).mem_vertexSector_iff_toReal_orientedAngle_mem_Icc
      (σ.inv_partialCycleMap_smul_vertex hz m) hw, interiorAngle_smul, hangle]
  exact ⟨by linarith, by linarith⟩

/-- **Local coverage at a finite vertex.** If the interior angles at the first `r` vertices of
the cycle through a finite vertex `z = vertex j` sum to at least `2π`, then the pulled-back tiles
`(partialCycleMap j m)⁻¹ • P`, `m < r`, cover a neighbourhood of `z`. -/
theorem mem_interior_iUnion_inv_partialCycleMap_smul_carrier {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) {r : ℕ}
    (hr : 2 * π ≤ ∑ m ∈ Finset.range r, P.interiorAngle (σ.next^[m] j)) :
    z ∈ interior (⋃ m ∈ Finset.range r, (σ.partialCycleMap j m)⁻¹ • P.carrier) := by
  rw [σ.mem_interior_iUnion_inv_partialCycleMap_smul_carrier_iff hz,
    σ.iUnion_inv_partialCycleMap_smul_vertexSector_eq_univ hz hr, interior_univ]
  exact Set.mem_univ z

/-- **Local coverage at a finite vertex cycle.** If `t` circuits of the cycle through a finite
vertex `z = vertex j` have total angle at least `2π`, then the tiles met along those circuits
cover a neighbourhood of `z`. This is the case of an elliptic cycle whose angle sum is `2π / t`
in Poincaré's polygon theorem. -/
theorem mem_interior_iUnion_inv_partialCycleMap_smul_carrier_of_le_mul_cycleAngleSum
    {j : Fin n} {z : ℍ} (hz : P.vertex j = .inl z) {t : ℕ} (ht : 2 * π ≤ t * σ.cycleAngleSum j) :
    z ∈ interior (⋃ m ∈ Finset.range (t * σ.cycleLength j),
      (σ.partialCycleMap j m)⁻¹ • P.carrier) :=
  σ.mem_interior_iUnion_inv_partialCycleMap_smul_carrier hz
    (by rwa [σ.sum_range_mul_cycleLength_interiorAngle])

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
