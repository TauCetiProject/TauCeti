/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import TauCeti.Analysis.Complex.UpperHalfPlane.IdealRegion
import TauCeti.Data.Fin.Basic

/-!
# Sides, boundary and interior of convex hyperbolic polygons

Distinct sides of a convex polygon have distinct supporting geodesic lines. Every point on a
side other than its finite endpoints lies strictly to the left of all the other supporting
lines. This identifies regular edge points by strict inequalities and permits local tessellation
arguments without assuming those inequalities separately. The results include ideal vertices:
a side can be a segment, a ray, or a full line.

A point of the polygon on the supporting line of a side lies on that side: beyond a finite
endpoint, the line leaves the closed half-plane of the adjacent side. Hence the boundary of the
polygon is the union of its sides, and so is null. A point near a regular side point, on the
inner side of its line, is interior, so the interior is nonempty, and by convexity the polygon is
the closure of its interior.

## Main results

* `ConvexPolygon.range_sideGeodesic_ne`: distinct sides have distinct supporting lines.
* `ConvexPolygon.mem_leftHalfPlane_of_mem_side`: a nonendpoint side point satisfies every
  other side inequality strictly.
* `ConvexPolygon.carrier_inter_range_sideGeodesic`: the polygon meets the supporting line of a
  side exactly in that side.
* `ConvexPolygon.frontier_carrier`: the boundary is the union of the sides.
* `ConvexPolygon.volume_frontier_carrier`: the boundary is a null set.
* `ConvexPolygon.nonempty_interior_carrier`, `ConvexPolygon.closure_interior_carrier`: the
  interior is nonempty and dense in the polygon.

## References

Walkden, *Hyperbolic geometry* (Manchester lecture notes, 2019), §14.2 (convex polygons as
intersections of half-planes) and §§19–20 (local tessellation in Poincaré's theorem).
Beardon, *The Geometry of Discrete Groups*, Chapter 9.
-/

public section

open Filter MeasureTheory Set Topology UpperHalfPlane
open scoped MatrixGroups OnePoint

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

/-- Every side has a point other than its finite endpoints. -/
theorem exists_mem_side_ne_endpoints (k : Fin n) :
    ∃ z ∈ P.side k, P.vertex k ≠ .inl z ∧ P.vertex (k + 1) ≠ .inl z := by
  have hg := P.isGeodesicFromTo_sideGeodesic k
  rw [side_def]
  rcases hp : P.vertex k with v | ξ <;> rcases hq : P.vertex (k + 1) with w | η <;>
    rw [hp, hq] at hg
  · obtain ⟨s, t, hst, rfl, rfl⟩ := isGeodesicFromTo_inl_inl.1 hg
    refine ⟨geodesicLine (P.sideGeodesic k) ((s + t) / 2), ?_, ?_, ?_⟩
    · rw [extGeodesicSegment_inl_inl, geodesicSegment_geodesicLine, uIcc_of_le hst.le]
      exact mem_image_of_mem _ ⟨by linarith, by linarith⟩
    · exact fun h ↦ by
        have := geodesicLine_injective _ (Sum.inl_injective h)
        linarith
    · exact fun h ↦ by
        have := geodesicLine_injective _ (Sum.inl_injective h)
        linarith
  · refine ⟨geodesicLine (rayToward v (.inr η)) 1, ?_, fun h ↦ ?_, Sum.inr_ne_inl⟩
    · rw [extGeodesicSegment_inl_inr]
      exact mem_image_of_mem _ (mem_Ici.2 zero_le_one)
    · have := geodesicLine_injective _
        ((geodesicLine_rayToward_zero v _).trans (Sum.inl_injective h))
      norm_num at this
  · refine ⟨geodesicLine (rayToward w (.inr ξ)) 1, ?_, Sum.inr_ne_inl, fun h ↦ ?_⟩
    · rw [extGeodesicSegment_inr_inl]
      exact mem_image_of_mem _ (mem_Ici.2 zero_le_one)
    · have := geodesicLine_injective _
        ((geodesicLine_rayToward_zero w _).trans (Sum.inl_injective h))
      norm_num at this
  · have hξη : ξ ≠ η := fun h ↦ hg.ne (congrArg _ h)
    refine ⟨geodesicLine (geodesicFromTo (.inr ξ) (.inr η)) 0, ?_, Sum.inr_ne_inl,
      Sum.inr_ne_inl⟩
    rw [extGeodesicSegment_inr_inr hξη]
    exact mem_range_self 0

/-- On the supporting geodesic of side `k`, a parameter strictly between two parameters of
points of the polygon is not on the supporting geodesic of another side. -/
private theorem geodesicLine_notMem_range_sideGeodesic {k j : Fin n} (hjk : j ≠ k) {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (ha : geodesicLine (P.sideGeodesic k) a ∈ P.carrier)
    (hb : geodesicLine (P.sideGeodesic k) b ∈ P.carrier) :
    geodesicLine (P.sideGeodesic k) c ∉ range (geodesicLine (P.sideGeodesic j)) :=
  disjoint_left.1 (disjoint_leftHalfPlane_range_geodesicLine _)
    (geodesicLine_mem_leftHalfPlane_of_mem_closure hac hcb
      (P.carrier_subset_closure_leftHalfPlane j ha) (P.carrier_subset_closure_leftHalfPlane j hb)
      (P.range_sideGeodesic_ne hjk.symm))

/-- The points of the polygon on the supporting geodesic of a side are exactly the points of
that side. -/
@[simp]
theorem carrier_inter_range_sideGeodesic (k : Fin n) :
    P.carrier ∩ range (geodesicLine (P.sideGeodesic k)) = P.side k := by
  refine Subset.antisymm ?_
    (subset_inter (P.side_subset_carrier k) (P.side_subset_range_sideGeodesic k))
  rintro _ ⟨hx, u, rfl⟩
  have hk₁ : k + 1 ≠ k := add_one_ne_self (by have := P.three_le; omega) k
  have hk₀ : k - 1 ≠ k := sub_one_ne_self (by have := P.three_le; omega) k
  -- a finite vertex lies on the supporting geodesics of both sides through it
  have hprev {v : ℍ} (hv : P.vertex k = .inl v) :
      v ∈ range (geodesicLine (P.sideGeodesic (k - 1))) :=
    P.side_subset_range_sideGeodesic _
      (P.mem_side_of_vertex_add_one_eq_inl (by rwa [sub_add_cancel]))
  have hnext {w : ℍ} (hw : P.vertex (k + 1) = .inl w) :
      w ∈ range (geodesicLine (P.sideGeodesic (k + 1))) :=
    P.side_subset_range_sideGeodesic _ (P.mem_side_of_vertex_eq_inl hw)
  have hside := P.side_subset_carrier k
  have hg := P.isGeodesicFromTo_sideGeodesic k
  rw [side_def] at hside ⊢
  -- In each case the side is the image of an interval of parameters of `sideGeodesic k`. A
  -- parameter `u` beyond a finite endpoint would put that endpoint, a vertex on the line of the
  -- adjacent side, strictly between two points of the polygon on the line of side `k`.
  rcases hp : P.vertex k with v | ξ <;> rcases hq : P.vertex (k + 1) with w | η <;>
    rw [hp, hq] at hg hside
  · -- a segment `[s, t]`
    obtain ⟨s, t, hst, hs, ht⟩ := isGeodesicFromTo_inl_inl.1 hg
    rw [extGeodesicSegment_inl_inl, ← hs, ← ht, geodesicSegment_geodesicLine,
      uIcc_of_le hst.le]
    refine mem_image_of_mem _ ⟨le_of_not_gt fun hus ↦ ?_, le_of_not_gt fun htu ↦ ?_⟩
    · exact P.geodesicLine_notMem_range_sideGeodesic hk₀ hus hst hx
        (ht ▸ P.vertex_mem_carrier hq) (hs ▸ hprev hp)
    · exact P.geodesicLine_notMem_range_sideGeodesic hk₁ hst htu
        (hs ▸ P.vertex_mem_carrier hp) hx (ht ▸ hnext hq)
  · -- a forward ray `[s, ∞)`
    obtain ⟨⟨s, hs⟩, hη⟩ := isGeodesicFromTo_inl_inr.1 hg
    rw [extGeodesicSegment_inl_inr, ← hs, ← hη] at hside ⊢
    simp only [rayToward_geodesicLine_inr_smul_infty, geodesicLine_mul_dilation] at hside ⊢
    refine ⟨u - s, mem_Ici.2 (sub_nonneg.2 (le_of_not_gt fun hus ↦ ?_)), by
      dsimp only
      rw [add_sub_cancel]⟩
    exact P.geodesicLine_notMem_range_sideGeodesic hk₀ hus (lt_add_one s) hx
      (hside (mem_image_of_mem _ (mem_Ici.2 zero_le_one))) (hs ▸ hprev hp)
  · -- a backward ray `(-∞, t]`, the forward ray of the reversed line
    obtain ⟨hξ, ⟨t, ht⟩⟩ := isGeodesicFromTo_inr_inl.1 hg
    have hξ' : ξ = (P.sideGeodesic k * pslS) • (∞ : OnePoint ℝ) := by
      rw [mul_smul, pslS_smul_infty, hξ]
    have hw : w = geodesicLine (P.sideGeodesic k * pslS) (-t) := by
      rw [geodesicLine_mul_pslS, neg_neg, ht]
    rw [extGeodesicSegment_inr_inl, hξ', hw] at hside ⊢
    simp only [rayToward_geodesicLine_inr_smul_infty, geodesicLine_mul_dilation] at hside ⊢
    simp only [geodesicLine_mul_pslS] at hside ⊢
    refine ⟨t - u, mem_Ici.2 (sub_nonneg.2 (le_of_not_gt fun htu ↦ ?_)), by
      dsimp only
      congr 1
      ring⟩
    refine P.geodesicLine_notMem_range_sideGeodesic hk₁ (sub_one_lt t) htu ?_ hx (ht ▸ hnext hq)
    have := hside (mem_image_of_mem _ (mem_Ici.2 zero_le_one))
    convert this using 2
    ring
  · -- the whole line
    obtain ⟨hξ, hη⟩ := isGeodesicFromTo_inr_inr.1 hg
    have hξη : ξ ≠ η := fun h ↦ (isGeodesicFromTo_inr_inr.2 ⟨hξ, hη⟩).ne (congrArg _ h)
    rw [extGeodesicSegment_inr_inr hξη,
      (isGeodesicFromTo_inr_inr.2 ⟨hξ, hη⟩).range_geodesicLine_eq
        (isGeodesicFromTo_geodesicFromTo (Sum.inr_injective.ne hξη))]
    exact mem_range_self u

/-- The boundary of a convex polygon is the union of its sides. -/
@[simp]
theorem frontier_carrier : frontier P.carrier = ⋃ i, P.side i := by
  refine Subset.antisymm (fun z hz ↦ ?_) (iUnion_subset P.side_subset_frontier_carrier)
  rw [P.isClosed_carrier.frontier_eq] at hz
  obtain ⟨hzc, hzi⟩ := hz
  obtain ⟨k, hk⟩ : ∃ k, z ∉ leftHalfPlane (P.sideGeodesic k) := by
    simpa using hzi
  have hz := P.carrier_subset_closure_leftHalfPlane k hzc
  rw [closure_leftHalfPlane] at hz
  exact mem_iUnion.2 ⟨k, P.carrier_inter_range_sideGeodesic k ▸ ⟨hzc, hz.resolve_left hk⟩⟩

/-- The boundary of a convex polygon is a null set: it is the union of finitely many sides, each
contained in a geodesic line. -/
theorem volume_frontier_carrier : volume (frontier P.carrier) = 0 := by
  rw [P.frontier_carrier]
  exact measure_iUnion_null fun i ↦
    measure_mono_null (P.side_subset_range_sideGeodesic i) (volume_range_geodesicLine _)

/-- A convex polygon has nonempty interior. -/
theorem nonempty_interior_carrier : (interior P.carrier).Nonempty := by
  obtain ⟨z, hz, hzp, hzq⟩ := P.exists_mem_side_ne_endpoints 0
  -- near the regular side point `z` every other side inequality stays strict
  have hO : IsOpen (⋂ j : {j : Fin n // j ≠ 0}, leftHalfPlane (P.sideGeodesic j)) :=
    isOpen_iInter_of_finite fun _ ↦ isOpen_leftHalfPlane _
  have hzO : z ∈ ⋂ j : {j : Fin n // j ≠ 0}, leftHalfPlane (P.sideGeodesic j) :=
    mem_iInter.2 fun j ↦ P.mem_leftHalfPlane_of_mem_side hz hzp hzq j.2
  obtain ⟨w, hwO, hw⟩ := mem_closure_iff.1
    (P.carrier_subset_closure_leftHalfPlane 0 (P.side_subset_carrier 0 hz)) _ hO hzO
  refine ⟨w, (P.mem_interior_carrier_iff w).2 fun j ↦ ?_⟩
  by_cases hj : j = 0
  · exact hj ▸ hw
  · exact mem_iInter.1 hwO ⟨j, hj⟩

/-- A convex polygon is the closure of its interior. -/
@[simp]
theorem closure_interior_carrier : closure (interior P.carrier) = P.carrier := by
  refine Subset.antisymm (closure_minimal interior_subset P.isClosed_carrier) fun x hx ↦ ?_
  obtain ⟨p, hp⟩ := P.nonempty_interior_carrier
  rcases eq_or_ne x p with rfl | hxp
  · exact subset_closure hp
  -- the points of the geodesic segment from `x` to `p`, other than `x`, are interior
  have hmem : ∀ t ∈ Ioo 0 (dist x p),
      geodesicLine (geodesicBetween x p) t ∈ interior P.carrier := fun t ht ↦
    (P.mem_interior_carrier_iff _).2 fun j ↦ geodesicLine_mem_leftHalfPlane_of_mem_closure ht.1 ht.2
      (by rw [geodesicLine_geodesicBetween_zero]; exact P.carrier_subset_closure_leftHalfPlane j hx)
      (by rw [geodesicLine_geodesicBetween_dist]
          exact P.carrier_subset_closure_leftHalfPlane j (interior_subset hp))
      fun he ↦ disjoint_left.1 (disjoint_leftHalfPlane_range_geodesicLine _)
        ((P.mem_interior_carrier_iff p).1 hp j)
        (he ▸ ⟨dist x p, geodesicLine_geodesicBetween_dist x p⟩)
  have hlim : Tendsto (geodesicLine (geodesicBetween x p)) (𝓝[>] 0) (𝓝 x) := by
    have h := ((isometry_geodesicLine (geodesicBetween x p)).continuous.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [geodesicLine_geodesicBetween_zero] at h
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (dist_pos.2 hxp)] with t ht using hmem t ht

end TauCeti.UpperHalfPlane.ConvexPolygon
