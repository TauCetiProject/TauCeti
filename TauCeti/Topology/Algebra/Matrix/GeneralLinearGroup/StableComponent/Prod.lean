/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.AlgebraicK1
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Basic
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.StableComponent.Basic
public import TauCeti.Topology.Algebra.Ring.Basic

/-!
# The stable component group of a product of topological rings

For topological rings `A` and `B`, an invertible matrix over `A × B` is a pair of invertible
matrices over `A` and over `B` (`TauCeti.prodEquivGL`), and this identification and its inverse
are continuous for the units topologies. The inverse therefore maps the product of the identity
components of `GLₙ(A)` and `GLₙ(B)` into the identity component of `GLₙ(A × B)`
(`TauCeti.prodEquivGL_symm_mem_connectedComponentOfOne_iff`). Passing to the stable component
groups, the homomorphisms induced by the two projections give an isomorphism

  `π₀GL_∞(A × B) ≃* π₀GL_∞(A) × π₀GL_∞(B)`

(`TauCeti.StableComponentGroup.prodEquiv`), the counterpart for the stable component group of
`K₁(A × B) ≃* K₁(A) × K₁(B)` in algebraic `K₁` (`TauCeti.AlgebraicK1.prodEquiv`). No
connectedness is assumed, so the stable component groups need not be commutative; the inverse
sends a pair of classes of invertible matrices of a common size to the class of the matrix over
`A × B` with these components (`TauCeti.StableComponentGroup.prodEquiv_symm_mk`).

## Main definitions

* `TauCeti.StableComponentGroup.prodEquiv`: `π₀GL_∞(A × B) ≃* π₀GL_∞(A) × π₀GL_∞(B)`, induced by
  the two projections.

## Main results

* `TauCeti.prodEquivGL_symm_mem_connectedComponentOfOne_iff`: an invertible matrix over `A × B`
  lies in the identity component exactly when both of its components do.
* `TauCeti.StableComponentGroup.prodEquiv_apply`,
  `TauCeti.StableComponentGroup.prodEquiv_symm_mk`: the isomorphism and its inverse on classes.
* `TauCeti.StableComponentGroup.map_fst_prodEquiv_symm`,
  `TauCeti.StableComponentGroup.map_snd_prodEquiv_symm`: the projections recover the two
  components from the inverse.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §8.1.
-/

public section

noncomputable section

namespace TauCeti

variable {A B : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [Ring B]
  [TopologicalSpace B] [IsTopologicalRing B]

/-- An invertible matrix over `A × B` lies in the identity component of `GLₙ(A × B)` exactly when
both of its components lie in the identity components of `GLₙ(A)` and `GLₙ(B)`. -/
theorem prodEquivGL_symm_mem_connectedComponentOfOne_iff {n : Type*} [Fintype n] [DecidableEq n]
    {p : GL n A × GL n B} :
    (prodEquivGL n A B).symm p ∈ Subgroup.connectedComponentOfOne (GL n (A × B)) ↔
      p.1 ∈ Subgroup.connectedComponentOfOne (GL n A) ∧
        p.2 ∈ Subgroup.connectedComponentOfOne (GL n B) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ?_⟩
  · rw [← unitsMap_fst_prodEquivGL_symm p]
    exact Subgroup.map_connectedComponentOfOne_le
      (Units.continuous_map (continuous_id.matrix_map continuous_fst)) ⟨_, h, rfl⟩
  · rw [← unitsMap_snd_prodEquivGL_symm p]
    exact Subgroup.map_connectedComponentOfOne_le
      (Units.continuous_map (continuous_id.matrix_map continuous_snd)) ⟨_, h, rfl⟩
  · -- The pair lies in the identity component of the product group, which the continuous
    -- inverse of `prodEquivGL` maps into the identity component of `GLₙ(A × B)`.
    have hp : p ∈ Subgroup.connectedComponentOfOne (GL n A × GL n B) := by
      rw [Subgroup.mem_connectedComponentOfOne_iff, Prod.one_eq_mk, connectedComponent_prod]
      exact ⟨Subgroup.mem_connectedComponentOfOne_iff.1 h.1,
        Subgroup.mem_connectedComponentOfOne_iff.1 h.2⟩
    exact Subgroup.map_connectedComponentOfOne_le (f := (prodEquivGL n A B).symm.toMonoidHom)
      continuous_prodEquivGL_symm ⟨p, hp, rfl⟩

namespace StableComponentGroup

/-- The first projection sends the class of the invertible matrix over `A × B` with components
`p.1` and `p.2` to the class of `p.1`. -/
private theorem map_fst_mk_prodEquivGL_symm {n : ℕ} (p : GL (Fin n) A × GL (Fin n) B) :
    map (RingHom.fst A B) RingHom.continuous_fst
        (mk (A × B) n ((prodEquivGL (Fin n) A B).symm p)) = mk A n p.1 := by
  rw [map_mk, RingHom.toMonoidHom_eq_coe, unitsMap_fst_prodEquivGL_symm]

/-- The second projection sends the class of the invertible matrix over `A × B` with components
`p.1` and `p.2` to the class of `p.2`. -/
private theorem map_snd_mk_prodEquivGL_symm {n : ℕ} (p : GL (Fin n) A × GL (Fin n) B) :
    map (RingHom.snd A B) RingHom.continuous_snd
        (mk (A × B) n ((prodEquivGL (Fin n) A B).symm p)) = mk B n p.2 := by
  rw [map_mk, RingHom.toMonoidHom_eq_coe, unitsMap_snd_prodEquivGL_symm]

variable (A B) in
/-- The homomorphism `π₀GL_∞(A × B) →* π₀GL_∞(A) × π₀GL_∞(B)` induced by the two projections. -/
private def prodHom :
    StableComponentGroup (A × B) →* StableComponentGroup A × StableComponentGroup B :=
  (map (RingHom.fst A B) RingHom.continuous_fst).prod
    (map (RingHom.snd A B) RingHom.continuous_snd)

/-- The homomorphism induced by the two projections is injective: if both components of an
invertible matrix over `A × B` become trivial after stabilization, then so does the matrix. -/
private theorem prodHom_injective : Function.Injective (prodHom A B) := by
  refine (injective_iff_map_eq_one _).2 fun x hx ↦ ?_
  obtain ⟨n, w, rfl⟩ := exists_mk x
  obtain ⟨p, rfl⟩ := (prodEquivGL (Fin n) A B).symm.surjective w
  simp only [prodHom, MonoidHom.prod_apply, map_fst_mk_prodEquivGL_symm,
    map_snd_mk_prodEquivGL_symm, Prod.mk_eq_one, mk_eq_one_iff] at hx
  obtain ⟨⟨k₁, h₁, hu⟩, ⟨k₂, h₂, hv⟩⟩ := hx
  -- Stabilize both components further, to the common size `max k₁ k₂`.
  have hu' := Subgroup.map_connectedComponentOfOne_le
    (continuous_stabilizeGL (A := A) (le_max_left k₁ k₂)) ⟨_, hu, rfl⟩
  have hv' := Subgroup.map_connectedComponentOfOne_le
    (continuous_stabilizeGL (A := B) (le_max_right k₁ k₂)) ⟨_, hv, rfl⟩
  rw [stabilizeGL_stabilizeGL] at hu' hv'
  refine mk_eq_one_iff.2 ⟨max k₁ k₂, h₁.trans (le_max_left k₁ k₂), ?_⟩
  rw [stabilizeGL_prodEquivGL_symm, prodEquivGL_symm_mem_connectedComponentOfOne_iff]
  exact ⟨hu', hv'⟩

/-- The homomorphism induced by the two projections is surjective: stabilize representatives of
the two classes to a common size and assemble them into an invertible matrix over `A × B`. -/
private theorem prodHom_surjective : Function.Surjective (prodHom A B) := by
  rintro ⟨x, y⟩
  obtain ⟨m, u, rfl⟩ := exists_mk x
  obtain ⟨k, v, rfl⟩ := exists_mk y
  refine ⟨mk (A × B) (max m k) ((prodEquivGL (Fin (max m k)) A B).symm
    (stabilizeGL A (le_max_left m k) u, stabilizeGL B (le_max_right m k) v)), ?_⟩
  simp only [prodHom, MonoidHom.prod_apply, map_fst_mk_prodEquivGL_symm,
    map_snd_mk_prodEquivGL_symm, mk_stabilizeGL]

variable (A B) in
/-- **The stable component group of a product of topological rings** is the product of the
stable component groups of the factors, through the homomorphisms induced by the two
projections. -/
def prodEquiv : StableComponentGroup (A × B) ≃* StableComponentGroup A × StableComponentGroup B :=
  MulEquiv.ofBijective (prodHom A B) ⟨prodHom_injective, prodHom_surjective⟩

/-- The isomorphism `π₀GL_∞(A × B) ≃* π₀GL_∞(A) × π₀GL_∞(B)` is given by the homomorphisms
induced by the two projections. -/
@[simp]
theorem prodEquiv_apply (x : StableComponentGroup (A × B)) :
    prodEquiv A B x =
      (map (RingHom.fst A B) RingHom.continuous_fst x,
        map (RingHom.snd A B) RingHom.continuous_snd x) :=
  (rfl)

/-- The inverse of `π₀GL_∞(A × B) ≃* π₀GL_∞(A) × π₀GL_∞(B)` sends the pair of classes of
invertible matrices `u` over `A` and `v` over `B` of the same size to the class of the invertible
matrix over `A × B` with components `u` and `v`. -/
@[simp]
theorem prodEquiv_symm_mk {n : ℕ} (u : GL (Fin n) A) (v : GL (Fin n) B) :
    (prodEquiv A B).symm (mk A n u, mk B n v) =
      mk (A × B) n ((prodEquivGL (Fin n) A B).symm (u, v)) := by
  rw [MulEquiv.symm_apply_eq, prodEquiv_apply]
  exact Prod.ext (map_fst_mk_prodEquivGL_symm (u, v)).symm
    (map_snd_mk_prodEquivGL_symm (u, v)).symm

/-- The homomorphism induced by the first projection recovers the first component from the inverse
of `π₀GL_∞(A × B) ≃* π₀GL_∞(A) × π₀GL_∞(B)`. -/
@[simp]
theorem map_fst_prodEquiv_symm (p : StableComponentGroup A × StableComponentGroup B) :
    map (RingHom.fst A B) RingHom.continuous_fst ((prodEquiv A B).symm p) = p.1 := by
  have h := congrArg Prod.fst ((prodEquiv A B).apply_symm_apply p)
  rwa [prodEquiv_apply] at h

/-- The homomorphism induced by the second projection recovers the second component from the
inverse of `π₀GL_∞(A × B) ≃* π₀GL_∞(A) × π₀GL_∞(B)`. -/
@[simp]
theorem map_snd_prodEquiv_symm (p : StableComponentGroup A × StableComponentGroup B) :
    map (RingHom.snd A B) RingHom.continuous_snd ((prodEquiv A B).symm p) = p.2 := by
  have h := congrArg Prod.snd ((prodEquiv A B).apply_symm_apply p)
  rwa [prodEquiv_apply] at h

end StableComponentGroup

end TauCeti
