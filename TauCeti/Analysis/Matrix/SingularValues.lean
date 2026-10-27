/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# Singular values and two-sided unitary matrix orbits

Square matrices lie in the same two-sided unitary orbit exactly when their singular values
agree. The singular values are Mathlib's `LinearMap.singularValues`, applied through
`Matrix.toEuclideanLin`; no second enumeration is introduced.

`Matrix.exists_unitary_mul_diagonal_mul_unitary` reads the operator singular value decomposition
in the standard orthonormal basis. The orbit characterization then identifies the diagonal
entries as complete invariants, including for singular matrices and in dimension zero.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Section 2.6.
-/

public section

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Left multiplication by a unitary matrix preserves every singular value. -/
theorem singularValues_toEuclideanLin_unitary_mul
    (A : Matrix ι ι 𝕜) (U : unitaryGroup ι 𝕜) :
    (toEuclideanLin ((U : Matrix ι ι 𝕜) * A)).singularValues =
      (toEuclideanLin A).singularValues := by
  apply LinearMap.singularValues_eq_of_norm_apply_eq
  intro x
  have hU := Unitary.map_mem (toEuclideanCLM (n := ι) (𝕜 := 𝕜)) U.property
  simpa only [toEuclideanLin, toLpLin_mul_same, LinearMap.comp_apply,
    ← coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe] using
    ContinuousLinearMap.norm_map_of_mem_unitary hU (toEuclideanLin A x)

/-- Right multiplication by a unitary matrix preserves every singular value. -/
theorem singularValues_toEuclideanLin_mul_unitary
    (A : Matrix ι ι 𝕜) (U : unitaryGroup ι 𝕜) :
    (toEuclideanLin (A * (U : Matrix ι ι 𝕜))).singularValues =
      (toEuclideanLin A).singularValues := by
  rw [← LinearMap.singularValues_adjoint, ← toEuclideanLin_conjTranspose_eq_adjoint,
    conjTranspose_mul]
  exact (singularValues_toEuclideanLin_unitary_mul Aᴴ (star U)).trans
    (by rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.singularValues_adjoint])

/-- Every square matrix is a product of two unitary matrices and the diagonal matrix of its
singular values in decreasing order. Zero singular values are allowed. -/
theorem exists_unitary_mul_diagonal_mul_unitary (A : Matrix (Fin n) (Fin n) 𝕜) :
    ∃ U V : unitaryGroup (Fin n) 𝕜,
      A = (U : Matrix (Fin n) (Fin n) 𝕜) *
        diagonal (fun i : Fin n ↦ ((toEuclideanLin A).singularValues i : 𝕜)) * V := by
  let e := EuclideanSpace.basisFun (Fin n) 𝕜
  obtain ⟨U, V, h⟩ := (toEuclideanLin A).exists_linearIsometryEquiv_eq_comp_toLin_diagonal_comp e
  -- The operator theorem coerces isometries through continuous linear equivalences;
  -- matrix conversion uses their underlying linear equivalences. Compare these maps explicitly.
  have hc (W : EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin n)) :
      (W : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n)) =
        W.toLinearEquiv.toLinearMap := by
    ext x
    rfl
  rw [hc U, hc V] at h
  refine ⟨⟨U.toMatrix e.toBasis e.toBasis, U.toMatrix_mem_unitaryGroup e e⟩,
    ⟨V.toMatrix e.toBasis e.toBasis, V.toMatrix_mem_unitaryGroup e e⟩, ?_⟩
  simpa only [e, toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.toMatrix_comp e.toBasis e.toBasis e.toBasis, LinearMap.toMatrix_toLin,
    mul_assoc] using
    congrArg (LinearMap.toMatrix e.toBasis e.toBasis) h

/-- In a two-sided unitary factorization with a nonnegative decreasing real diagonal,
the diagonal entries are the singular values. -/
theorem singularValues_toEuclideanLin_of_unitary_mul_diagonal_mul_unitary
    (A : Matrix (Fin n) (Fin n) 𝕜) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hanti : Antitone d) (U V : unitaryGroup (Fin n) 𝕜)
    (h : A = (U : Matrix (Fin n) (Fin n) 𝕜) * diagonal (fun i ↦ (d i : 𝕜)) * V)
    (i : Fin n) : (toEuclideanLin A).singularValues i = d i := by
  rw [h, singularValues_toEuclideanLin_mul_unitary, singularValues_toEuclideanLin_unitary_mul]
  have hnorm (j : Fin n) : ‖(d j : 𝕜)‖ = d j := RCLike.norm_of_nonneg (hd j)
  simpa only [toEuclideanLin_eq_toLin_orthonormal, Equiv.refl_apply, hnorm] using
    Matrix.singularValues_toLin_diagonal (EuclideanSpace.basisFun (Fin n) 𝕜)
      (fun j ↦ (d j : 𝕜)) (Equiv.refl _)
      (by simpa only [Equiv.refl_apply, hnorm] using hanti) i

/-- Singular values classify two-sided unitary orbits of square matrices. -/
theorem exists_unitary_mul_mul_unitary_iff_singularValues_eq
    (A B : Matrix (Fin n) (Fin n) 𝕜) :
    (∃ U V : unitaryGroup (Fin n) 𝕜,
      B = (U : Matrix (Fin n) (Fin n) 𝕜) * A * V) ↔
      (toEuclideanLin A).singularValues = (toEuclideanLin B).singularValues := by
  constructor
  · rintro ⟨U, V, rfl⟩
    rw [singularValues_toEuclideanLin_mul_unitary,
      singularValues_toEuclideanLin_unitary_mul]
  · intro h
    obtain ⟨U, V, hA⟩ := exists_unitary_mul_diagonal_mul_unitary A
    obtain ⟨W, Z, hB⟩ := exists_unitary_mul_diagonal_mul_unitary B
    refine ⟨W * U⁻¹, V⁻¹ * Z, ?_⟩
    rw [hB, ← h]
    conv_rhs => rw [hA]
    simp only [Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star]
    simp [mul_assoc, ← mul_assoc (star (U : Matrix (Fin n) (Fin n) 𝕜)),
      ← mul_assoc (V : Matrix (Fin n) (Fin n) 𝕜)]

end Matrix
