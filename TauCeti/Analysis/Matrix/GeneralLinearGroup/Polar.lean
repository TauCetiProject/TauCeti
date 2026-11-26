/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Unitary.Polar
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.StableComponent

/-!
# Invertible matrices over a C⋆-algebra are joined to unitary matrices

Applying `Units.exists_unitary_joined` to the C⋆-algebras `CStarMatrix n n A`, every invertible
matrix over a unital C⋆-algebra `A` is joined in `GLₙ(A)` to a unitary matrix, its polar unitary.
Consequently every class of the stable component group `π₀ GL_∞(A)` is the class of a unitary
matrix.

## Main results

* `Matrix.GeneralLinearGroup.exists_mem_unitary_joined`: every invertible matrix is joined in
  `GLₙ(A)` to a unitary matrix.
* `TauCeti.StableComponentGroup.exists_mem_unitary_mk_eq_mk`,
  `TauCeti.StableComponentGroup.exists_mem_unitary_mk_eq`: unitary matrices represent every
  class of the stable component group.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §8.1.
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

end TauCeti.StableComponentGroup

end Matrix
