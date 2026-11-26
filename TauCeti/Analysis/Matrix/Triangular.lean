/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.Triangular.Coordinates
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# Topology of triangular matrix coordinates

The upper and strict lower entries of a square matrix give a continuous linear equivalence with
the product of the two coordinate spaces. Over an `RCLike` field, a unitary upper
triangular matrix with positive diagonal is the identity. In Lie-theoretic language the unitary
group meets the upper triangular matrices with positive diagonal only in `1`, the identity
`K ∩ A N = 1` behind the uniqueness of the Iwasawa decomposition, the `QR` factorization and the
Cholesky factorization.

## Main results

* `Matrix.IsUpperTriangular.eq_one_of_mem_unitaryGroup`: a unitary upper triangular matrix with
  positive diagonal is the identity.
* `TauCeti.schurMatrixCLE`: the continuous linear equivalence that assembles the coordinates.
-/

public section

open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **A unitary upper triangular matrix with positive diagonal is the identity.** Over `ℝ` or `ℂ`,
the unitary group meets the group of upper triangular matrices with positive diagonal only in the
identity: this is `K ∩ A N = 1` in the Iwasawa decomposition. -/
theorem IsUpperTriangular.eq_one_of_mem_unitaryGroup {M : Matrix ι ι 𝕜}
    (hM : M.IsUpperTriangular) (hMU : M ∈ unitaryGroup ι 𝕜) (hpos : ∀ i, 0 < M i i) : M = 1 := by
  have hright : M * star M = 1 := mem_unitaryGroup_iff.1 hMU
  let _ : Invertible M := invertibleOfRightInverse M (star M) hright
  -- `star M` is the inverse of `M`, so it is upper triangular as `M` is
  have hstar : (star M).IsUpperTriangular := by
    rw [← inv_eq_right_inv hright]
    exact blockTriangular_inv_of_blockTriangular hM
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [one_apply_ne hij.ne]
    simpa [star_apply] using hstar hij
  · obtain ⟨r, hr, hri⟩ := RCLike.pos_iff_exists_ofReal.1 (hpos i)
    have h : M i i * star (M i i) = 1 := by
      rw [← star_apply, ← mul_apply_diag_of_isUpperTriangular hM hstar, hright, one_apply_eq]
    rw [← hri, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, ← RCLike.ofReal_one,
      RCLike.ofReal_inj] at h
    rw [one_apply_eq, ← hri, ← RCLike.ofReal_one, RCLike.ofReal_inj]
    rcases mul_self_eq_one_iff.1 h with h | h
    · exact h
    · linarith
  · rw [one_apply_ne hij.ne', hM hij]

end Matrix

namespace TauCeti

variable {𝕜 ι R : Type*} [CommSemiring 𝕜] [LinearOrder ι] [Semiring R]
  [Algebra 𝕜 R] [TopologicalSpace R]

/-- Assemble a matrix from its upper and strict lower coordinates, as a continuous linear
equivalence for the product topologies. -/
noncomputable def schurMatrixCLE : SchurCoordinates ι R ≃L[𝕜] Matrix ι ι R where
  toLinearEquiv := schurMatrixEquiv.restrictScalars 𝕜
  continuous_toFun := by
    refine continuous_matrix fun i j ↦ ?_
    -- Scalar restriction keeps the underlying assembly function.
    change Continuous (fun x : SchurCoordinates ι R ↦ schurMatrixEquiv x i j)
    rcases le_or_gt i j with h | h
    · simp only [schurMatrixEquiv_apply_of_le _ h]
      exact (continuous_apply _).comp continuous_fst
    · simp only [schurMatrixEquiv_apply_of_gt _ h]
      exact (continuous_apply _).comp continuous_snd
  continuous_invFun := by
    -- The inverse of the restricted map also has the same underlying function.
    change Continuous (fun A : Matrix ι ι R ↦ schurMatrixEquiv.symm A)
    have hUpper (ij : {ij : ι × ι // ij.1 ≤ ij.2}) :
        Continuous (fun A : Matrix ι ι R ↦ (schurMatrixEquiv.symm A).1 ij) := by
      simp only [Matrix.schurMatrixEquiv_symm_fst]
      exact continuous_id.matrix_elem _ _
    have hLower (ij : SchurLowerIndex ι) :
        Continuous (fun A : Matrix ι ι R ↦ (schurMatrixEquiv.symm A).2 ij) := by
      simp only [Matrix.schurMatrixEquiv_symm_snd]
      exact continuous_id.matrix_elem _ _
    exact (continuous_pi hUpper).prodMk (continuous_pi hLower)

/-- Continuous linear assembly agrees with the algebraic entry assembly. -/
@[simp] theorem schurMatrixCLE_apply (x : SchurCoordinates ι R) :
    schurMatrixCLE (𝕜 := 𝕜) x = schurMatrixEquiv x :=
  (rfl)

/-- Reading coordinates with the continuous linear split agrees with the algebraic split. -/
@[simp] theorem _root_.Matrix.schurMatrixCLE_symm_apply (A : Matrix ι ι R) :
    (schurMatrixCLE (𝕜 := 𝕜)).symm A = schurMatrixEquiv.symm A :=
  (rfl)

end TauCeti
