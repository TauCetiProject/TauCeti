/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Polygon
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Vertex.Ideal

/-!
# Cusp orbits extracted from a fundamental polygon

Let `σ` pair the sides of a convex hyperbolic polygon `P`, and let `Γ ≤ PSL(2, ℝ)` contain the
side-pairing maps, with locally finite translates of `P` whose interiors are pairwise disjoint.
Then the cusp orbits of `Γ` are exactly the ideal vertex cycles of `P`: every ideal vertex is a
cusp point, every cusp point is `Γ`-equivalent to an ideal vertex, and two ideal vertices are
`Γ`-equivalent exactly when they lie in the same cycle.

The classification is an equivalence with the actual cusp-orbit subtype `Subgroup.CuspOrbit`
of the boundary quotient, sending a cycle to the orbit of any of its vertices. It supplies the
number of cusps in an orbifold signature, complementing the classification of elliptic orbits in
`ConvexPolygon.SidePairing.ellipticOrbitEquiv`. Compactness and finite covolume are not
additional hypotheses.

## Main results

* `ConvexPolygon.SidePairing.idealVertexCycleEquiv`: ideal vertex cycles are in bijection with
  cusp orbits.
* `ConvexPolygon.SidePairing.coe_idealVertexCycleEquiv_mk`: a cycle goes to the orbit of its
  vertex.
* `ConvexPolygon.SidePairing.natCard_cuspOrbit`: the number of cusp orbits is the number of
  ideal vertex cycles.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 9 (cycles of vertices at infinity).
* Svetlana Katok, *Fuchsian Groups*, §4.2 (cusps and vertices at infinity of a fundamental
  region).

The surjectivity is `ConvexPolygon.SidePairing.exists_vertex_eq_inr_smul_of_isCuspPoint`; the
injectivity is `ConvexPolygon.SidePairing.mem_orbit_iff_mem_cycle_of_vertex_eq_inr`, applied with
the parabolic cycle transformations given by local finiteness.
-/

public section

open MulAction Set UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing) {Γ : Subgroup PSL(2, ℝ)}

/-- The cusp orbit of an ideal vertex of a locally finite side-paired polygon. -/
private noncomputable def idealVertexCuspOrbit (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (j : {i : Fin n // (P.vertex i).isRight}) : Γ.CuspOrbit :=
  Γ.cuspOrbitMk ⟨(P.vertex j).getRight j.2, Subgroup.mem_cuspPoints.mpr <|
    σ.isCuspPoint_of_vertex_eq_inr (Sum.inr_getRight _ j.2).symm (σ.cycleMap_mem hmap _) hlf⟩

/-- Two ideal vertices have the same cusp orbit exactly when they lie in the same cycle. -/
private theorem idealVertexCuspOrbit_eq_iff_sameCycle (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (j k : {i : Fin n // (P.vertex i).isRight}) :
    σ.idealVertexCuspOrbit hmap hlf j = σ.idealVertexCuspOrbit hmap hlf k ↔
      σ.next.SameCycle j k := by
  have hk := (Sum.inr_getRight _ k.2).symm
  rw [idealVertexCuspOrbit, idealVertexCuspOrbit, Subgroup.cuspOrbitMk_eq_iff,
    σ.mem_orbit_iff_mem_cycle_of_vertex_eq_inr hk (Sum.inr_getRight _ j.2).symm hmap
      (σ.isParabolic_cycleMap_of_locallyFinite hk (σ.cycleMap_mem hmap _) hlf) hdisj,
    σ.mem_cycle_iff_sameCycle, Equiv.Perm.sameCycle_comm]

/-- Every cusp orbit contains an ideal vertex. -/
private theorem idealVertexCuspOrbit_surjective (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) :
    Function.Surjective (σ.idealVertexCuspOrbit hmap hlf) := by
  intro C
  obtain ⟨c, rfl⟩ := Subgroup.cuspOrbitMk_surjective C
  obtain ⟨γ, j, hj⟩ := σ.exists_vertex_eq_inr_smul_of_isCuspPoint hmap hlf
    (Subgroup.mem_cuspPoints.mp c.property)
  refine ⟨⟨j, by simp [hj]⟩, ?_⟩
  rw [idealVertexCuspOrbit, Subgroup.cuspOrbitMk_eq_iff, mem_orbit_iff]
  exact ⟨γ, by simp [hj]⟩

/-- **The cusp orbits of a locally finite fundamental polygon are its ideal vertex cycles.** Let
`Γ` contain the side-pairing maps, with locally finite translates of `P` whose interiors are
pairwise disjoint. Sending an ideal vertex to its boundary orbit identifies the same-cycle
quotient of the ideal vertices with the cusp orbits of `Γ`. -/
noncomputable def idealVertexCycleEquiv (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    σ.IdealVertexCycle ≃ Γ.CuspOrbit :=
  (Quotient.congrRight fun j k ↦
      (σ.idealVertexCuspOrbit_eq_iff_sameCycle hmap hlf hdisj j k).symm).trans
    (Setoid.quotientKerEquivOfSurjective _ (σ.idealVertexCuspOrbit_surjective hmap hlf))

/-- The cycle of an ideal vertex is sent to the boundary orbit of that vertex. -/
@[simp]
theorem coe_idealVertexCycleEquiv_mk (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (j : {i : Fin n // (P.vertex i).isRight}) :
    (σ.idealVertexCycleEquiv hmap hlf hdisj (Quotient.mk'' j) : Γ.BoundaryOrbit) =
      Quotient.mk'' ((P.vertex j).getRight j.2) := by
  -- Mathlib has no `apply_mk` lemmas for `Quotient.congrRight` and
  -- `Setoid.quotientKerEquivOfSurjective`; both compute on representatives.
  have h : σ.idealVertexCycleEquiv hmap hlf hdisj (Quotient.mk'' j) =
      σ.idealVertexCuspOrbit hmap hlf j := rfl
  rw [h, idealVertexCuspOrbit, Subgroup.cuspOrbitMk_val]

/-- **The number of cusps of a locally finite fundamental polygon.** The number of cusp orbits
of `Γ` is the number of ideal vertex cycles of `P`. -/
theorem natCard_cuspOrbit (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    Nat.card Γ.CuspOrbit = Nat.card σ.IdealVertexCycle :=
  (Nat.card_congr (σ.idealVertexCycleEquiv hmap hlf hdisj)).symm

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
