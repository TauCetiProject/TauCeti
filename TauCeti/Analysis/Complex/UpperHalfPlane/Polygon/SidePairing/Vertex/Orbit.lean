/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Vertex.Stabilizer

/-!
# Finite vertex cycles are vertex orbits

Let `σ` pair the sides of a convex hyperbolic polygon `P`, and let `Γ` contain its side-pairing
maps, with distinct translates of the interior disjoint. Two finite vertices of `P` are
`Γ`-equivalent exactly when their indices lie in the same vertex cycle. More precisely, every
transformation identifying two finite vertices is one of the partial cycle products met during
one full turn about the first vertex.

Together with the vertex stabilizer theorem, this identifies the finite vertex cycles and their
cycle orders with the corresponding orbits and stabilizer orders in the coarse quotient. It does
not assert that every elliptic orbit meets a vertex: a self-paired side can also have an elliptic
midpoint. Neither discreteness nor local finiteness is needed for the finite vertex result.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 9 (vertex cycles of a fundamental
  polygon).
* Svetlana Katok, *Fuchsian Groups*, Chapter 3 (side identifications and elliptic cycles).
-/

public section

open Set Topology UpperHalfPlane
open scoped MatrixGroups Pointwise Real

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing) {Γ : Subgroup PSL(2, ℝ)}

/-- Two finite vertices of a polygon with disjoint translated interiors represent the same group
orbit exactly when they lie in the same side-pairing cycle. -/
theorem mem_orbit_iff_mem_cycle {j k : Fin n} {z w : ℍ}
    (hz : P.vertex j = .inl z) (hw : P.vertex k = .inl w)
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    w ∈ MulAction.orbit Γ z ↔ k ∈ σ.cycle j := by
  rw [MulAction.mem_orbit_iff, σ.mem_cycle_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨m, -, -, hm⟩ := σ.exists_partialCycleMap_eq_of_smul_vertex_eq hz hw hmap hdisj g.2 hg
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    refine ⟨⟨σ.partialCycleMap j m, σ.partialCycleMap_mem hmap j m⟩, ?_⟩
    have h := σ.partialCycleMap_smul_vertex j m
    simpa only [hz, hw, hm, Sum.smul_inl, Sum.inl.injEq, Subgroup.mk_smul] using h

/-- On the finite vertices, the orbit relation is exactly the cycle relation. This also applies
to cycles with trivial vertex stabilizer. -/
theorem quotientMk_finite_vertex_eq_iff_sameCycle
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (j k : {i : Fin n // (P.vertex i).isLeft}) :
    (Quotient.mk'' ((P.vertex j).getLeft j.2) : MulAction.orbitRel.Quotient Γ ℍ) =
        Quotient.mk'' ((P.vertex k).getLeft k.2) ↔ σ.next.SameCycle j k := by
  rw [Quotient.eq'']
  have h := σ.mem_orbit_iff_mem_cycle
    (Sum.inl_getLeft (P.vertex k) k.2).symm (Sum.inl_getLeft (P.vertex j) j.2).symm hmap hdisj
  -- `orbitRel` relates `z` to `w` when `z` belongs to the orbit of `w`.
  rw [MulAction.orbitRel_apply, h]
  rw [σ.mem_cycle_iff, Equiv.Perm.sameCycle_comm]
  simp only [← Equiv.Perm.coe_pow]
  exact ⟨fun ⟨m, hm⟩ ↦ hm ▸ Equiv.Perm.sameCycle_pow_right.2 (.refl _ _),
    Equiv.Perm.SameCycle.exists_nat_pow_eq⟩

/-- Finite vertex cycles correspond bijectively to the coarse quotient orbits meeting a finite
vertex of `P`. The domain is Mathlib's same-cycle quotient, restricted to finite vertices; the
codomain is the image of those vertices under the ordinary orbit projection. In particular,
cycles of stabilizer order one are retained, and no assertion about elliptic side midpoints is
made. -/
noncomputable def finiteVertexCycleEquiv
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    Quotient (Setoid.comap Subtype.val
      (Equiv.Perm.SameCycle.setoid σ.next) : Setoid {i : Fin n // (P.vertex i).isLeft}) ≃
      Set.range (fun j : {i : Fin n // (P.vertex i).isLeft} ↦
        (Quotient.mk'' ((P.vertex j).getLeft j.2) : MulAction.orbitRel.Quotient Γ ℍ)) := by
  let f : {i : Fin n // (P.vertex i).isLeft} → MulAction.orbitRel.Quotient Γ ℍ :=
    fun j ↦ Quotient.mk'' ((P.vertex j).getLeft j.2)
  have hker : ∀ j k, σ.next.SameCycle j.val k.val ↔ Setoid.ker f j k :=
    fun j k ↦ (σ.quotientMk_finite_vertex_eq_iff_sameCycle hmap hdisj j k).symm
  exact (Quotient.congrRight hker).trans (Setoid.quotientKerEquivRange f)

/-- The finite-cycle bijection sends a vertex cycle to the actual orbit of its vertex. -/
@[simp]
theorem finiteVertexCycleEquiv_apply
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (j : {i : Fin n // (P.vertex i).isLeft}) :
    (σ.finiteVertexCycleEquiv hmap hdisj (Quotient.mk'' j)).val =
      Quotient.mk'' ((P.vertex j).getLeft j.2) := by
  -- Compute on representatives through Mathlib's kernel-quotient/image equivalence.
  rfl

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
