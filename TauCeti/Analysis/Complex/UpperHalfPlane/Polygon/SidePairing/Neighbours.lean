/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Elliptic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Vertex.Stabilizer

/-!
# Intersecting translates of a fundamental polygon

For a side-paired convex hyperbolic polygon with disjoint translated interiors, the translates
meeting the polygon in the upper half-plane are exactly the polygon itself, its side neighbours,
and the inverse partial cycle tiles around its finite vertices. There are finitely many such
translates, even when the polygon has ideal vertices. Intersections only at the ideal boundary
are not counted.

Three distinct tiles can meet only at a finite vertex. These pair and triple intersection
results supply the geometric generator and relation localization for a presentation obtained
from a neighbourhood of the polygon: side intersections involve two adjacent tiles, and triple
intersections occur in finite vertex cycles. No local finiteness or discreteness is assumed.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 9.
* Svetlana Katok, *Fuchsian Groups*, Chapter 3.
* A. M. Macbeath, *Groups of homeomorphisms of a simply connected space*,
  Ann. of Math. (2) 79 (1964), 473–488.
-/

public section

open Set Topology UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)
  {Γ : Subgroup PSL(2, ℝ)}

/-- A translate meets the polygon in `ℍ` exactly when its transformation is the identity,
a side-pairing map, or an inverse partial cycle product at a finite vertex before one full turn.
Ideal-vertex contacts alone do not give an intersection in `ℍ`. -/
theorem inter_smul_carrier_nonempty_iff (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {g : PSL(2, ℝ)} (hg : g ∈ Γ) :
    (P.carrier ∩ g • P.carrier).Nonempty ↔
      g = 1 ∨ (∃ i, g = σ.map i) ∨
        ∃ (j : Fin n) (z : ℍ), P.vertex j = .inl z ∧
          ∃ m < orderOf (σ.cycleMap j) * σ.cycleLength j,
            (σ.partialCycleMap j m)⁻¹ = g := by
  constructor
  · rintro ⟨z, hz, hzg⟩
    by_cases hzi : z ∈ interior P.carrier
    · exact Or.inl (P.eq_of_smul_interior_inter_smul_carrier_nonempty hdisj
        Γ.one_mem hg ⟨z, by simpa using hzi, hzg⟩).symm
    by_cases hv : ∃ j, P.vertex j = .inl z
    · obtain ⟨j, hj⟩ := hv
      exact Or.inr (Or.inr ⟨j, z, hj,
        (σ.mem_smul_carrier_iff_exists_inv_partialCycleMap_eq hj hmap hdisj hg).1 hzg⟩)
    · have hzf : z ∈ frontier P.carrier := ⟨subset_closure hz, hzi⟩
      obtain ⟨i, hi⟩ := mem_iUnion.1 (P.frontier_carrier ▸ hzf)
      obtain ⟨w, hw, hgw⟩ := mem_smul_set.1 hzg
      rcases σ.eq_one_or_eq_map_pair_of_smul_mem_side (hmap (σ.pair i)) hdisj hg hw hi
          (fun h ↦ hv ⟨i, h⟩) (fun h ↦ hv ⟨i + 1, h⟩) hgw with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨σ.pair i, h⟩)
  · rintro (rfl | ⟨i, rfl⟩ | ⟨j, z, hj, hm⟩)
    · simpa using P.nonempty_interior_carrier.mono interior_subset
    · obtain ⟨z, hz, _, _⟩ := P.exists_mem_side_ne_endpoints (σ.pair i)
      exact ⟨z, σ.side_subset_inter_smul_carrier i hz⟩
    · exact ⟨z, P.vertex_mem_carrier hj,
        (σ.mem_smul_carrier_iff_exists_inv_partialCycleMap_eq hj hmap hdisj hg).2 hm⟩

/-- Only finitely many translates of the polygon meet it in `ℍ`. This also holds for
polygons with ideal vertices; it does not assert local finiteness at the ideal boundary. -/
theorem finite_setOf_inter_smul_carrier_nonempty (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    {g : PSL(2, ℝ) | g ∈ Γ ∧ (P.carrier ∩ g • P.carrier).Nonempty}.Finite := by
  classical
  have hcycles : (⋃ j : Fin n,
      (fun m ↦ (σ.partialCycleMap j m)⁻¹) ''
        (↑(Finset.range (orderOf (σ.cycleMap j) * σ.cycleLength j)) : Set ℕ)).Finite :=
    finite_iUnion fun _ ↦ (Finset.finite_toSet _).image _
  apply ((finite_singleton 1).union ((finite_range σ.map).union hcycles)).subset
  intro g ⟨hg, hmeet⟩
  rcases (σ.inter_smul_carrier_nonempty_iff hmap hdisj hg).1 hmeet with
    rfl | ⟨i, rfl⟩ | ⟨j, _, _, m, hm, rfl⟩
  · exact Or.inl (mem_singleton _)
  · exact Or.inr (Or.inl (mem_range_self i))
  · exact Or.inr (Or.inr (mem_iUnion.2 ⟨j, mem_image_of_mem _ (Finset.mem_range.2 hm)⟩))

/-- A common point of the polygon and two distinct nonidentity translates is a finite vertex
of the polygon. Thus triple intersections of distinct tiles are localized at vertex cycles. -/
theorem exists_vertex_of_mem_carrier_of_mem_two_smul_carrier
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {g h : PSL(2, ℝ)} (hg : g ∈ Γ) (hh : h ∈ Γ)
    (hg1 : g ≠ 1) (hh1 : h ≠ 1) (hgh : g ≠ h)
    {z : ℍ} (hz : z ∈ P.carrier) (hzg : z ∈ g • P.carrier)
    (hzh : z ∈ h • P.carrier) : ∃ j, P.vertex j = .inl z := by
  by_contra hv
  have hzi : z ∉ interior P.carrier := fun hzi ↦ hg1
    (P.eq_of_smul_interior_inter_smul_carrier_nonempty hdisj
      Γ.one_mem hg ⟨z, by simpa using hzi, hzg⟩).symm
  have hzf : z ∈ frontier P.carrier := ⟨subset_closure hz, hzi⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 (P.frontier_carrier ▸ hzf)
  have heq (k : PSL(2, ℝ)) (hk : k ∈ Γ) (hk1 : k ≠ 1)
      (hzk : z ∈ k • P.carrier) : k = σ.map (σ.pair i) := by
    obtain ⟨w, hw, hkw⟩ := mem_smul_set.1 hzk
    exact (σ.eq_one_or_eq_map_pair_of_smul_mem_side (hmap (σ.pair i)) hdisj hk hw hi
      (fun h ↦ hv ⟨i, h⟩) (fun h ↦ hv ⟨i + 1, h⟩) hkw).resolve_left hk1
  exact hgh ((heq g hg hg1 hzg).trans (heq h hh hh1 hzh).symm)

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
