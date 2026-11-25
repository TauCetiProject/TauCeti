/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import TauCeti.Analysis.Matrix.GeneralLinearGroup.Polar
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Cartan
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable.BlockSum
public import TauCeti.Topology.Algebra.Star.Unitary

/-!
# Unitary representatives of the stable component group

Let `A` be a unital C⋆-algebra. The polar unitary `x ↦ x.polarUnitary` of an invertible element
depends continuously on it (`Units.continuous_polarUnitary`, from the Cartan decomposition), fixes
unitaries, and commutes with unital star homomorphisms (`Units.coe_polarUnitary_map`). So it
retracts the group of invertible elements onto the unitary group, and two unitaries joined by a
path of invertible elements are joined by a path of unitaries
(`Unitary.joined_of_joined_toUnits`).

Applied to the C⋆-algebras of matrices over `A`, this gives the description of the stable
component group `π₀ GL_∞(A)` through unitary matrices: two unitary matrices have the same class
exactly when, after one common stabilization, they are joined by a path of unitary matrices
(`TauCeti.StableComponentGroup.mk_eq_mk_iff_exists_path_unitary`). Block sum is the group law,
`[diag(u, v)] = [u] [v]` (`TauCeti.StableComponentGroup.mk_blockSumGL`), so it agrees with the
product of unitaries of equal size, and the class of the adjoint of a unitary is the inverse class
(`TauCeti.StableComponentGroup.mk_toUnits_star`). In particular `diag(u, v)` and `diag(uv, 1)` are
joined by a path of unitaries after a stabilization
(`TauCeti.StableComponentGroup.exists_path_unitary_blockSumGL`).

## Main results

* `Units.coe_polarUnitary_map`: naturality of the polar unitary.
* `Unitary.joined_of_joined_toUnits`, `Matrix.GeneralLinearGroup.joined_unitary_of_joined_toUnits`:
  unitaries joined through invertible elements are joined through unitaries.
* `TauCeti.coe_stabilizeGL_mem_unitary`, `TauCeti.coe_blockSumGL_mem_unitary`: stabilization and
  block sum preserve unitary matrices.
* `TauCeti.StableComponentGroup.mk_eq_mk_iff_exists_path_unitary`: the stable homotopy criterion
  for unitary matrices.
* `TauCeti.StableComponentGroup.mk_blockSumGL`: block sum is the group law.
* `TauCeti.StableComponentGroup.mk_toUnits_star`: the class of the adjoint is the inverse.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Definition 8.1.1 and Proposition 8.1.3.
-/

public section

noncomputable section

open Matrix

section Polar

variable {A : Type*} [CStarAlgebra A]

/-- In a unital C⋆-algebra, two unitaries joined by a path of invertible elements are joined by a
path of unitaries: the polar unitary retracts the invertible elements onto the unitaries. -/
theorem Unitary.joined_of_joined_toUnits {u v : unitary A}
    (h : Joined (Unitary.toUnits u) (Unitary.toUnits v)) : Joined u v := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  simpa only [Units.polarUnitary_toUnits] using h.map Units.continuous_polarUnitary

/-- In a unital C⋆-algebra, two unitaries are joined by a path of unitaries exactly when they are
joined by a path of invertible elements. -/
theorem Unitary.joined_toUnits_iff {u v : unitary A} :
    Joined (Unitary.toUnits u) (Unitary.toUnits v) ↔ Joined u v :=
  ⟨joined_of_joined_toUnits, fun h ↦ h.map continuous_toUnits⟩

/-- **Naturality of the polar unitary**: a unital star homomorphism of C⋆-algebras sends the
polar unitary of `x` to the polar unitary of the image of `x`. -/
theorem Units.coe_polarUnitary_map {B : Type*} [CStarAlgebra B] [PartialOrder A]
    [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] (φ : A →⋆ₐ[ℂ] B) (x : Aˣ) :
    ((Units.map (φ : A →* B) x).polarUnitary : B) = φ (x.polarUnitary : A) := by
  have hv : φ (x.polarUnitary : A) ∈ unitary B := by
    rw [Unitary.mem_iff, ← map_star, ← map_mul, ← map_mul, Unitary.coe_star_mul_self,
      Unitary.mul_star_self_of_mem x.polarUnitary.prop, map_one, and_self]
  exact congrArg Subtype.val (polarUnitary_eq_of_mul_eq (v := ⟨_, hv⟩) _
    (map_nonneg φ (CFC.sqrt_nonneg ((x : A) * star (x : A))))
    (by simp [← map_mul, sqrt_mul_star_mul_polarUnitary]))

end Polar

namespace Matrix.GeneralLinearGroup

variable {A : Type*} [CStarAlgebra A] {n : Type*} [Fintype n] [DecidableEq n]

/-- The group of invertible matrices over a unital C⋆-algebra is locally path connected, since it
is homeomorphic to the open set of invertible elements of the C⋆-algebra of matrices. -/
instance instLocallyPathConnectedSpace : LocallyPathConnectedSpace (GL n A) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have : LocallyPathConnectedSpace (CStarMatrix n n A) :=
    (inferInstance : LocallyPathConnectedSpace (n → n → A))
  have : LocallyPathConnectedSpace (CStarMatrix n n A)ˣ :=
    Units.isOpenEmbedding_val.locallyPathConnectedSpace
  exact (toCStarMatrixUnits (n := n) (A := A)).toHomeomorph.symm.locallyPathConnectedSpace

/-- Two unitary matrices over a unital C⋆-algebra joined by a path of invertible matrices are
joined by a path of unitary matrices. -/
theorem joined_unitary_of_joined_toUnits {u v : unitary (Matrix n n A)}
    (h : Joined (Unitary.toUnits u) (Unitary.toUnits v)) : Joined u v := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  -- Transport to the C⋆-algebra `CStarMatrix n n A`, retract there, and transport back.
  have hmem (w : unitary (Matrix n n A)) :
      CStarMatrix.ofMatrix (w : Matrix n n A) ∈ unitary (CStarMatrix n n A) := by
    rw [← CStarMatrix.ofMatrix_symm_mem_unitary_iff]
    exact w.prop
  let e : unitary (Matrix n n A) ≃ₜ unitary (CStarMatrix n n A) :=
    { toFun w := ⟨CStarMatrix.ofMatrix (w : Matrix n n A), hmem w⟩
      invFun w := ⟨CStarMatrix.ofMatrix.symm (w : CStarMatrix n n A),
        CStarMatrix.ofMatrix_symm_mem_unitary_iff.2 w.prop⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun :=
        (CStarMatrix.ofMatrixL.continuous.comp continuous_subtypeVal).subtype_mk hmem
      continuous_invFun := (CStarMatrix.ofMatrixL.symm.continuous.comp
        continuous_subtypeVal).subtype_mk fun w ↦
          CStarMatrix.ofMatrix_symm_mem_unitary_iff.2 w.prop }
  have hj : Joined (Unitary.toUnits (e u)) (Unitary.toUnits (e v)) := by
    convert h.map (map_continuous (toCStarMatrixUnits (n := n) (A := A))) using 1 <;>
      exact Units.ext (by simp; rfl)
  simpa using (Unitary.joined_of_joined_toUnits hj).map e.symm.continuous

end Matrix.GeneralLinearGroup

namespace TauCeti

section Unitary

variable {A : Type*} [Ring A] [StarRing A]

/-- An invertible matrix whose adjoint is its inverse is unitary. -/
private theorem coe_mem_unitary_of_star_eq {n : Type*} [Fintype n] [DecidableEq n] {x : GL n A}
    (h : star (x : Matrix n n A) = (x⁻¹ : GL n A)) : (x : Matrix n n A) ∈ unitary _ := by
  rw [Unitary.mem_iff, h, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, mul_inv_cancel,
    Units.val_one, and_self]

/-- The inverse of a unitary invertible matrix is its adjoint. -/
private theorem coe_inv_eq_star {n : Type*} [Fintype n] [DecidableEq n] {x : GL n A}
    (hx : (x : Matrix n n A) ∈ unitary _) :
    ((x⁻¹ : GL n A) : Matrix n n A) = star (x : Matrix n n A) :=
  (Units.eq_inv_of_mul_eq_one_right (Unitary.star_mul_self_of_mem hx)).symm

/-- Stabilization sends unitary matrices to unitary matrices. -/
theorem coe_stabilizeGL_mem_unitary {m n : ℕ} (h : m ≤ n) {u : GL (Fin m) A}
    (hu : (u : Matrix (Fin m) (Fin m) A) ∈ unitary _) :
    (stabilizeGL A h u : Matrix (Fin n) (Fin n) A) ∈ unitary _ := by
  refine coe_mem_unitary_of_star_eq ?_
  rw [← map_inv]
  ext i j
  simp only [Matrix.star_apply, coe_stabilizeGL_apply, coe_inv_eq_star hu, Matrix.one_apply]
  by_cases hij : (i : ℕ) < m ∧ (j : ℕ) < m
  · rw [dite_eq_left_of_eq_true (eq_true hij.symm), dite_eq_left_of_eq_true (eq_true hij)]
  · rw [dite_eq_right_of_eq_false (eq_false fun h' ↦ hij h'.symm),
      dite_eq_right_of_eq_false (eq_false hij)]
    by_cases hij' : i = j
    · subst hij'
      simp
    · simp [hij', Ne.symm hij']

/-- The block sum of unitary matrices is unitary. -/
theorem coe_blockSumGL_mem_unitary {m n : ℕ} {u : GL (Fin m) A × GL (Fin n) A}
    (hu₁ : (u.1 : Matrix (Fin m) (Fin m) A) ∈ unitary _)
    (hu₂ : (u.2 : Matrix (Fin n) (Fin n) A) ∈ unitary _) :
    (blockSumGL A u : Matrix (Fin (m + n)) (Fin (m + n)) A) ∈ unitary _ := by
  refine coe_mem_unitary_of_star_eq ?_
  rw [← map_inv, coe_blockSumGL, coe_blockSumGL, Matrix.star_eq_conjTranspose,
    conjTranspose_reindex, fromBlocks_conjTranspose, conjTranspose_zero, conjTranspose_zero,
    Prod.fst_inv, Prod.snd_inv, coe_inv_eq_star hu₁, coe_inv_eq_star hu₂,
    Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]

end Unitary

namespace StableComponentGroup

section BlockSum

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [PreconnectedSpace A]

/-- **Block sum is the group law of the stable component group**: over a connected topological
ring, `[diag(u, v)] = [u] [v]`. -/
@[simp]
theorem mk_blockSumGL {m n : ℕ} (u : GL (Fin m) A × GL (Fin n) A) :
    mk A (m + n) (blockSumGL A u) = mk A m u.1 * mk A n u.2 := by
  rw [← AlgebraicK1.toStableComponentGroup_mk, AlgebraicK1.mk_blockSumGL, map_mul,
    AlgebraicK1.toStableComponentGroup_mk, AlgebraicK1.toStableComponentGroup_mk]

end BlockSum

/-- The class of the adjoint of a unitary matrix is the inverse of its class. -/
@[simp]
theorem mk_toUnits_star {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {n : ℕ} (u : unitary (Matrix (Fin n) (Fin n) A)) :
    mk A n (Unitary.toUnits (star u)) = (mk A n (Unitary.toUnits u))⁻¹ := by
  rw [Unitary.star_eq_inv, map_inv, map_inv]

variable {A : Type*} [CStarAlgebra A]

/-- **The stable homotopy criterion for unitaries**: two unitary matrices over a unital
C⋆-algebra have the same class in the stable component group exactly when, after one common
stabilization, they are joined by a path of unitary matrices. -/
theorem mk_eq_mk_iff_exists_path_unitary {n : ℕ} {u v : GL (Fin n) A}
    (hu : (u : Matrix (Fin n) (Fin n) A) ∈ unitary _)
    (hv : (v : Matrix (Fin n) (Fin n) A) ∈ unitary _) :
    mk A n u = mk A n v ↔ ∃ k, ∃ h : n ≤ k, ∃ γ : Path (stabilizeGL A h u) (stabilizeGL A h v),
      ∀ t, (γ t : Matrix (Fin k) (Fin k) A) ∈ unitary _ := by
  rw [mk_eq_mk_iff]
  refine exists_congr fun k ↦ exists_congr fun h ↦ ⟨fun hk ↦ ?_, fun ⟨γ, _⟩ ↦ ?_⟩
  · rw [map_mul, map_inv, Subgroup.mem_connectedComponentOfOne_iff_joined] at hk
    have hj : Joined (stabilizeGL A h u) (stabilizeGL A h v) := by
      simpa using hk.map (continuous_const.mul continuous_id :
        Continuous fun z : GL (Fin k) A ↦ stabilizeGL A h u * z)
    let U : unitary (Matrix (Fin k) (Fin k) A) := ⟨_, coe_stabilizeGL_mem_unitary h hu⟩
    let V : unitary (Matrix (Fin k) (Fin k) A) := ⟨_, coe_stabilizeGL_mem_unitary h hv⟩
    have hU : Unitary.toUnits U = stabilizeGL A h u := Units.ext rfl
    have hV : Unitary.toUnits V = stabilizeGL A h v := Units.ext rfl
    obtain ⟨γ⟩ := Matrix.GeneralLinearGroup.joined_unitary_of_joined_toUnits (u := U) (v := V)
      (by rwa [hU, hV])
    refine ⟨((γ.map Unitary.continuous_toUnits).cast hU.symm hV.symm), fun t ↦ ?_⟩
    exact (γ t).prop
  · rw [map_mul, map_inv]
    exact (Joined.inv_mul_mem_connectedComponentOfOne ⟨γ⟩)

/-- Over a unital C⋆-algebra, `diag(u, v)` and `diag(uv, 1)` are joined by a path of unitary
matrices after a stabilization, for unitary matrices `u` and `v` of equal size. -/
theorem exists_path_unitary_blockSumGL {n : ℕ} {u v : GL (Fin n) A}
    (hu : (u : Matrix (Fin n) (Fin n) A) ∈ unitary _)
    (hv : (v : Matrix (Fin n) (Fin n) A) ∈ unitary _) :
    ∃ k, ∃ h : n + n ≤ k,
      ∃ γ : Path (stabilizeGL A h (blockSumGL A (u, v)))
        (stabilizeGL A h (blockSumGL A (u * v, 1))),
        ∀ t, (γ t : Matrix (Fin k) (Fin k) A) ∈ unitary _ := by
  refine (mk_eq_mk_iff_exists_path_unitary ?_ ?_).1 (by simp)
  · exact coe_blockSumGL_mem_unitary hu hv
  · exact coe_blockSumGL_mem_unitary (mul_mem hu hv) (one_mem _)

end StableComponentGroup

end TauCeti
