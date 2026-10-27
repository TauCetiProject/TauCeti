/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Sides

/-!
# Separation across paired polygon sides

A side-pairing transformation reverses the endpoints of an oriented side while preserving the
orientation of the upper half-plane. It therefore carries the left half-plane of that side to
the right half-plane of the paired side. Consequently, the original polygon and its paired
translate have disjoint interiors, and their intersection lies on the supporting geodesic of
the paired side. The paired side itself belongs to their intersection. At every point of that
side other than its finite endpoints, the two tiles together contain a neighbourhood: the
strict inequalities for the other sides follow from convexity.

These are the separation facts for adjacent tiles in a polygon tessellation. They apply to
finite and ideal vertices, and even to a side paired with itself. They require no discreteness
or cycle hypotheses. Separation for arbitrary products of side-pairing transformations, and
coverage by all translates, require additional hypotheses.

## Main results

* `ConvexPolygon.SidePairing.map_smul_leftHalfPlane`: the supporting half-planes are exchanged.
* `ConvexPolygon.SidePairing.disjoint_smul_carrier_interior_carrier`: the paired translate misses
  the interior of the original polygon.
* `ConvexPolygon.SidePairing.inter_smul_carrier_subset_range_sideGeodesic`: intersections occur
  only on the supporting geodesic of the paired side.
* `ConvexPolygon.SidePairing.map_injective`: distinct sides have distinct side-pairing maps.
* `ConvexPolygon.SidePairing.mem_interior_union_smul_carrier`: local coverage when the other
  side inequalities in both tiles are strict.
* `ConvexPolygon.SidePairing.mem_interior_union_smul_carrier_of_mem_side`: local coverage at
  every nonendpoint point of a paired side, with no additional inequalities assumed.
* `ConvexPolygon.SidePairing.exists_mem_side_mem_interior_union_inv_smul_carrier`: local
  coverage at every boundary point of the polygon other than a finite vertex.

## References

Walkden, *Hyperbolic geometry* (MATH32052 lecture notes, Manchester 2019), §16.1 (orientation
of side pairings) and §§19–20 (Poincaré's theorem). Beardon, *The Geometry of Discrete Groups*,
Chapter 9.
-/

public section

open Set Topology UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-- The side-pairing map carries the left half-plane of the source side to the right half-plane
of the paired side. -/
-- Not `@[simp]`: `smul_leftHalfPlane` already rewrites the left-hand side.
theorem map_smul_leftHalfPlane (i : Fin n) :
    σ.map i • leftHalfPlane (P.sideGeodesic i) = rightHalfPlane (P.sideGeodesic (σ.pair i)) := by
  have h := (P.isGeodesicFromTo_sideGeodesic i).smul (σ.map i)
  rw [σ.map_smul_vertex, σ.map_smul_vertex_add_one] at h
  have hrev := isGeodesicFromTo_mul_pslS_iff.2 (P.isGeodesicFromTo_sideGeodesic (σ.pair i))
  rw [smul_leftHalfPlane, hrev.leftHalfPlane_eq h, leftHalfPlane_mul_pslS]

/-- The side-pairing map carries the right half-plane of the source side to the left half-plane
of the paired side. -/
-- Not `@[simp]`: `smul_rightHalfPlane` already rewrites the left-hand side.
theorem map_smul_rightHalfPlane (i : Fin n) :
    σ.map i • rightHalfPlane (P.sideGeodesic i) = leftHalfPlane (P.sideGeodesic (σ.pair i)) := by
  have h := σ.map_smul_leftHalfPlane (σ.pair i)
  rw [σ.pair_pair, σ.map_pair] at h
  rw [← h, smul_inv_smul]

/-- The paired translate of the polygon lies on the right of the paired side, including its
supporting geodesic. -/
theorem smul_carrier_subset_closure_rightHalfPlane (i : Fin n) :
    σ.map i • P.carrier ⊆ closure (rightHalfPlane (P.sideGeodesic (σ.pair i))) := by
  rw [← σ.map_smul_leftHalfPlane, closure_smul]
  exact smul_set_mono (P.carrier_subset_closure_leftHalfPlane i)

/-- The paired translate misses the interior of the original polygon. This is stronger than
separation of their two interiors. -/
theorem disjoint_smul_carrier_interior_carrier (i : Fin n) :
    Disjoint (σ.map i • P.carrier) (interior P.carrier) := by
  refine Set.disjoint_left.2 fun z hz hzi ↦ ?_
  have hr := σ.smul_carrier_subset_closure_rightHalfPlane i hz
  have hl := (P.mem_interior_carrier_iff z).mp hzi (σ.pair i)
  rw [mem_closure_rightHalfPlane_iff] at hr
  rw [mem_leftHalfPlane_iff] at hl
  exact (not_lt_of_ge hr) hl

/-- The interior of the paired translate misses the entire original polygon. -/
theorem disjoint_smul_interior_carrier_carrier (i : Fin n) :
    Disjoint (σ.map i • interior P.carrier) P.carrier := by
  refine Set.disjoint_left.2 fun z hz hzc ↦ ?_
  have hinv := (Set.mem_smul_set_iff_inv_smul_mem).mp hz
  have hcinv : (σ.map i)⁻¹ • z ∈ σ.map (σ.pair i) • P.carrier := by
    rw [σ.map_pair]
    exact smul_mem_smul_set hzc
  exact Set.disjoint_left.1 (σ.disjoint_smul_carrier_interior_carrier (σ.pair i)) hcinv hinv

/-- The intersection of adjacent polygon carriers lies on the supporting geodesic of the paired
side. -/
theorem inter_smul_carrier_subset_range_sideGeodesic (i : Fin n) :
    P.carrier ∩ (σ.map i • P.carrier) ⊆ Set.range (geodesicLine (P.sideGeodesic (σ.pair i))) := by
  intro z hz
  have hl := P.carrier_subset_closure_leftHalfPlane (σ.pair i) hz.1
  have hr := σ.smul_carrier_subset_closure_rightHalfPlane i hz.2
  rw [mem_closure_leftHalfPlane_iff] at hl
  rw [mem_closure_rightHalfPlane_iff] at hr
  exact (mem_range_geodesicLine_iff _ _).2 (le_antisymm hl hr)

/-- The paired side lies in both the original polygon and its paired translate. -/
theorem side_subset_inter_smul_carrier (i : Fin n) :
    P.side (σ.pair i) ⊆ P.carrier ∩ (σ.map i • P.carrier) := by
  refine Set.subset_inter (P.side_subset_carrier _) ?_
  rw [← σ.map_smul_side]
  exact smul_set_mono (P.side_subset_carrier i)

/-- At a point satisfying all the other side inequalities strictly in both tiles, the polygon
and its paired translate together contain a neighbourhood. In particular, this gives local
coverage across a paired side away from any other supporting geodesic. -/
theorem mem_interior_union_smul_carrier (i : Fin n) {z : ℍ}
    (hz : ∀ j, j ≠ σ.pair i → z ∈ leftHalfPlane (P.sideGeodesic j))
    (hzinv : ∀ j, j ≠ i → (σ.map i)⁻¹ • z ∈ leftHalfPlane (P.sideGeodesic j)) :
    z ∈ interior (P.carrier ∪ (σ.map i • P.carrier)) := by
  have hlocal : ∀ᶠ w in 𝓝 z, ∀ j, j ≠ σ.pair i → w ∈ leftHalfPlane (P.sideGeodesic j) := by
    refine Filter.eventually_all.2 fun j ↦ ?_
    by_cases hj : j = σ.pair i
    · exact Filter.Eventually.of_forall fun _ h ↦ False.elim (h hj)
    · have hmem : ∀ᶠ w in 𝓝 z, w ∈ leftHalfPlane (P.sideGeodesic j) :=
        (isOpen_leftHalfPlane _).mem_nhds (hz j hj)
      exact hmem.mono fun _ hw _ ↦ hw
  have hlocalinv : ∀ᶠ w in 𝓝 z,
      ∀ j, j ≠ i → (σ.map i)⁻¹ • w ∈ leftHalfPlane (P.sideGeodesic j) := by
    refine Filter.eventually_all.2 fun j ↦ ?_
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun _ h ↦ False.elim (h hj)
    · have hmem : ∀ᶠ w in 𝓝 z, (σ.map i)⁻¹ • w ∈ leftHalfPlane (P.sideGeodesic j) :=
        (continuous_const_smul (σ.map i)⁻¹).continuousAt.eventually
          ((isOpen_leftHalfPlane _).mem_nhds (hzinv j hj))
      exact hmem.mono fun _ hw _ ↦ hw
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [hlocal, hlocalinv] with w hw hwinv
  by_cases hleft : w ∈ closure (leftHalfPlane (P.sideGeodesic (σ.pair i)))
  · refine Or.inl ((P.mem_carrier_iff w).2 fun j ↦ ?_)
    by_cases hj : j = σ.pair i
    · simpa only [hj] using hleft
    · exact subset_closure (hw j hj)
  · refine Or.inr (Set.mem_smul_set_iff_inv_smul_mem.2
      ((P.mem_carrier_iff _).2 fun j ↦ ?_))
    by_cases hj : j = i
    · subst j
      have hright : w ∈ closure (rightHalfPlane (P.sideGeodesic (σ.pair i))) := by
        rw [mem_closure_leftHalfPlane_iff] at hleft
        rw [mem_closure_rightHalfPlane_iff]
        exact (lt_of_not_ge hleft).le
      rwa [← σ.map_smul_leftHalfPlane, closure_smul,
        Set.mem_smul_set_iff_inv_smul_mem] at hright
    · exact subset_closure (hwinv j hj)

/-- Distinct sides have distinct side-pairing maps: the translate of the polygon by the map of
side `i` meets the polygon only on the supporting geodesic of `pair i`, which contains no other
side. -/
theorem map_injective : Function.Injective σ.map := by
  intro i i' h
  obtain ⟨z, hz, hzp, hzq⟩ := P.exists_mem_side_ne_endpoints (σ.pair i')
  have hzi : z ∈ range (geodesicLine (P.sideGeodesic (σ.pair i))) :=
    σ.inter_smul_carrier_subset_range_sideGeodesic i (h ▸ σ.side_subset_inter_smul_carrier i' hz)
  by_contra hne
  exact disjoint_left.1 (disjoint_leftHalfPlane_range_geodesicLine _)
    (P.mem_leftHalfPlane_of_mem_side hz hzp hzq (σ.pair.injective.ne hne)) hzi

/-- At every point of the paired side other than its finite endpoints, the two adjacent
polygon tiles together contain a neighbourhood. No extra side inequalities are assumed. -/
theorem mem_interior_union_smul_carrier_of_mem_side (i : Fin n) {z : ℍ}
    (hz : z ∈ P.side (σ.pair i)) (hzp : P.vertex (σ.pair i) ≠ .inl z)
    (hzq : P.vertex (σ.pair i + 1) ≠ .inl z) :
    z ∈ interior (P.carrier ∪ (σ.map i • P.carrier)) := by
  have hzinv : (σ.map i)⁻¹ • z ∈ P.side i := by
    rw [← σ.map_smul_side] at hz
    exact Set.mem_smul_set_iff_inv_smul_mem.1 hz
  have hpinv : P.vertex i ≠ .inl ((σ.map i)⁻¹ • z) := by
    intro heq
    apply hzq
    rw [← σ.map_smul_vertex i, heq, Sum.smul_inl, smul_inv_smul]
  have hqinv : P.vertex (i + 1) ≠ .inl ((σ.map i)⁻¹ • z) := by
    intro heq
    apply hzp
    rw [← σ.map_smul_vertex_add_one i, heq, Sum.smul_inl, smul_inv_smul]
  exact σ.mem_interior_union_smul_carrier i
    (fun _ hj ↦ P.mem_leftHalfPlane_of_mem_side hz hzp hzq hj)
    (fun _ hj ↦ P.mem_leftHalfPlane_of_mem_side hzinv hpinv hqinv hj)

/-- A boundary point of the polygon other than a finite vertex lies on a side `k`, and the polygon
and its translate `(map k)⁻¹ • P` across that side together contain a neighbourhood of it. -/
theorem exists_mem_side_mem_interior_union_inv_smul_carrier {z : ℍ} (hz : z ∈ P.carrier)
    (hzi : z ∉ interior P.carrier) (hv : ∀ i, P.vertex i ≠ .inl z) :
    ∃ k, z ∈ P.side k ∧ z ∈ interior (P.carrier ∪ (σ.map k)⁻¹ • P.carrier) := by
  have hzf : z ∈ frontier P.carrier := ⟨subset_closure hz, hzi⟩
  obtain ⟨k, hk⟩ := mem_iUnion.1 (P.frontier_carrier ▸ hzf)
  have h := σ.mem_interior_union_smul_carrier_of_mem_side (σ.pair k)
    (by rwa [σ.pair_pair]) (by rw [σ.pair_pair]; exact hv k)
    (by rw [σ.pair_pair]; exact hv (k + 1))
  rw [map_pair] at h
  exact ⟨k, hk, h⟩

/-- The side-pairing map carries a point of side `i` other than its endpoints to a point which is
not a finite vertex. -/
theorem map_smul_ne_vertex {i : Fin n} {x : ℍ} (hi : x ∈ P.side i) (hp : P.vertex i ≠ .inl x)
    (hq : P.vertex (i + 1) ≠ .inl x) (l : Fin n) : P.vertex l ≠ .inl (σ.map i • x) := by
  intro hl
  rcases P.eq_or_eq_add_one_of_vertex_eq_inl_of_mem_side hl (σ.map_smul_mem_side hi) with rfl | rfl
  · rw [← σ.map_smul_vertex_add_one, ← Sum.smul_inl] at hl
    exact hq (MulAction.injective _ hl)
  · rw [← σ.map_smul_vertex, ← Sum.smul_inl] at hl
    exact hp (MulAction.injective _ hl)

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
