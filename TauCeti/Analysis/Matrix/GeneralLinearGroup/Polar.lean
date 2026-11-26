/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Unitary.Polar
public import TauCeti.Analysis.Matrix.GeneralLinearGroup.Connected
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Cartan
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.StableComponent

/-!
# Unitary representatives of the stable component group

Applying `Units.exists_unitary_joined` to the C⋆-algebras `CStarMatrix n n A`, every invertible
matrix over a unital C⋆-algebra `A` is joined in `GLₙ(A)` to a unitary matrix, its polar unitary.
Consequently every class of the stable component group `π₀ GL_∞(A)` is the class of a unitary
matrix.

The polar unitary also retracts the invertible elements onto the unitaries continuously
(`Unitary.joined_of_joined_toUnits`), so two unitary matrices joined by a path of invertible
matrices are joined by a path of unitary matrices. Since `GLₙ(A)` is locally path connected, this
describes `π₀ GL_∞(A)` through unitary matrices: two unitary matrices have the same class exactly
when, after one common stabilization, they are joined by a path of unitary matrices. As block sum
is the group law (`TauCeti.StableComponentGroup.mk_blockSumGL`), `diag(u, v)` and `diag(uv, 1)`
are joined by a path of unitaries after a stabilization.

## Main results

* `Matrix.GeneralLinearGroup.exists_mem_unitary_joined`: every invertible matrix is joined in
  `GLₙ(A)` to a unitary matrix.
* `TauCeti.StableComponentGroup.exists_mem_unitary_mk_eq_mk`,
  `TauCeti.StableComponentGroup.exists_mem_unitary_mk_eq`: unitary matrices represent every
  class of the stable component group.
* `Matrix.GeneralLinearGroup.joined_unitary_of_joined_toUnits`: unitary matrices joined through
  invertible matrices are joined through unitary matrices.
* `TauCeti.StableComponentGroup.mk_eq_mk_iff_exists_path_unitary`: the stable homotopy criterion
  for unitary matrices.
* `TauCeti.StableComponentGroup.exists_path_unitary_blockSumGL`: `diag(u, v)` and `diag(uv, 1)`
  are stably joined by a path of unitary matrices.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §8.1, Definition 8.1.1 and Proposition 8.1.3.
* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), §2.1.
-/

public section

section Matrix

variable {A : Type*} [CStarAlgebra A]

/-- Every invertible matrix over a unital C⋆-algebra is joined in `GLₙ(A)` to a unitary matrix,
its polar unitary computed in `CStarMatrix n n A`. -/
theorem Matrix.GeneralLinearGroup.exists_mem_unitary_joined {n : Type*} [Fintype n]
    [DecidableEq n] (u : GL n A) :
    ∃ v : GL n A, (v : Matrix n n A) ∈ unitary (Matrix n n A) ∧ Joined u v := by
  -- Mathlib's C⋆-algebra structure on `CStarMatrix n n A` is stated for an ordered `A`.
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨w, hw⟩ := (toCStarMatrixUnits u).exists_unitary_joined
  refine ⟨toCStarMatrixUnits.symm (Unitary.toUnits w), ?_,
    by simpa using hw.map (map_continuous (toCStarMatrixUnits (n := n) (A := A)).symm)⟩
  rw [coe_toCStarMatrixUnits_symm, CStarMatrix.ofMatrix_symm_mem_unitary_iff]
  exact w.prop

/-- Two unitary matrices over a unital C⋆-algebra joined by a path of invertible matrices are
joined by a path of unitary matrices. -/
theorem Matrix.GeneralLinearGroup.joined_unitary_of_joined_toUnits {n : Type*} [Fintype n]
    [DecidableEq n] {u v : unitary (Matrix n n A)}
    (h : Joined (Unitary.toUnits u) (Unitary.toUnits v)) : Joined u v := by
  -- Mathlib's C⋆-algebra structure on `CStarMatrix n n A` is stated for an ordered `A`.
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  -- Transport to the C⋆-algebra `CStarMatrix n n A`, retract there, and transport back.
  have hj : Joined (Unitary.toUnits (toCStarMatrixUnitary u))
      (Unitary.toUnits (toCStarMatrixUnitary v)) := by
    convert h.map (map_continuous (toCStarMatrixUnits (n := n) (A := A))) using 1 <;>
      exact Units.ext (by simp)
  simpa using (Unitary.joined_of_joined_toUnits hj).map toCStarMatrixUnitary.symm.continuous

namespace TauCeti.StableComponentGroup

/-- Every invertible matrix over a unital C⋆-algebra has the class in the stable component group
of a unitary matrix of the same size. -/
theorem exists_mem_unitary_mk_eq_mk {n : ℕ} (u : GL (Fin n) A) :
    ∃ v : GL (Fin n) A,
      (v : Matrix (Fin n) (Fin n) A) ∈ unitary (Matrix (Fin n) (Fin n) A) ∧
        mk A n v = mk A n u := by
  obtain ⟨v, hv, h⟩ := Matrix.GeneralLinearGroup.exists_mem_unitary_joined u
  exact ⟨v, hv, (mk_eq_mk_iff.mpr ⟨n, le_rfl, by
    simpa using h.inv_mul_mem_connectedComponentOfOne⟩).symm⟩

/-- Every class of the stable component group of a unital C⋆-algebra is the class of a unitary
matrix. -/
theorem exists_mem_unitary_mk_eq (x : StableComponentGroup A) :
    ∃ n, ∃ u : GL (Fin n) A,
      (u : Matrix (Fin n) (Fin n) A) ∈ unitary (Matrix (Fin n) (Fin n) A) ∧ mk A n u = x := by
  obtain ⟨n, u, rfl⟩ := exists_mk x
  exact ⟨n, exists_mem_unitary_mk_eq_mk u⟩

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

end TauCeti.StableComponentGroup

end Matrix
