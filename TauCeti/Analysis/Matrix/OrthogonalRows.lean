/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Extending orthonormal rows to a unitary matrix

A matrix `V : Matrix m n 𝕜` over `𝕜 = ℝ` or `ℂ` with `V * Vᴴ = 1` has orthonormal rows. Given an
injection `e : m → n`, placing these rows at the indices `e i` and extending them to an orthonormal
basis of `EuclideanSpace 𝕜 n` exhibits `V` as the rows `e i` of a unitary matrix (an orthogonal
matrix when `𝕜 = ℝ`).

Dividing an arbitrary `M` by a square factor `T` of its Gram matrix `M * Mᴴ` leaves orthonormal
rows, so `M = T * Q.submatrix e id` for a unitary `Q`. This is the `LQ` decomposition of a matrix
of full row rank, and it is what factors a congruence by such a matrix into a rotation followed by
a coordinate selection.

## Main results

* `Matrix.exists_mul_conjTranspose_eq_one_and_submatrix_eq` — a matrix with orthonormal rows
  consists of some rows of a unitary matrix.
* `Matrix.exists_mul_conjTranspose_eq_one_and_eq_mul_submatrix` — a matrix is an invertible
  square factor of its Gram matrix times such a row selection.
-/

public section

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- **A matrix with orthonormal rows is a row selection of a unitary matrix.** If `V * Vᴴ = 1` and
`e : m → n` is injective, then `V` consists of the rows `e i` of a unitary matrix `Q`. -/
theorem exists_mul_conjTranspose_eq_one_and_submatrix_eq (V : Matrix m n 𝕜) {e : m → n}
    (he : Function.Injective e) (hV : V * Vᴴ = 1) :
    ∃ Q : Matrix n n 𝕜, Q * Qᴴ = 1 ∧ Q.submatrix e id = V := by
  -- The conjugated rows of `V` are orthonormal; place them at the indices `e i`.
  set v : m → EuclideanSpace 𝕜 n := fun i ↦ WithLp.toLp 2 (star (V i)) with hv
  have horth : Orthonormal 𝕜 v := by
    rw [← gram_eq_one_iff_orthonormal, ← hV]
    ext i j
    simp [hv, gram_apply, EuclideanSpace.inner_toLp_toLp, mul_apply, dotProduct, mul_comm]
  have horth' : Orthonormal 𝕜 ((Set.range e).domRestrict (Function.extend e v 0)) := by
    convert horth.comp _ (Equiv.ofInjective e he).symm.injective
    ext ⟨_, i, rfl⟩ : 1
    simp [he.extend_apply]
  -- Extend them to an orthonormal basis `b`; the conjugated rows of `b` form `Q`.
  obtain ⟨b, hb⟩ := horth'.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨((EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix b)ᴴ, by simp, ?_⟩
  ext i j
  simp [Module.Basis.toMatrix_apply, hb _ (Set.mem_range_self i), he.extend_apply, hv]

/-- **A matrix is a square factor of its Gram matrix times a row selection of a unitary matrix.**
If `T * Tᴴ = M * Mᴴ` with `T` invertible and `e : m → n` injective, then `T⁻¹ * M` has orthonormal
rows, hence consists of the rows `e i` of a unitary matrix `Q`, and `M = T * Q.submatrix e id`.
This is the `LQ` decomposition of a matrix of full row rank. -/
theorem exists_mul_conjTranspose_eq_one_and_eq_mul_submatrix [Fintype m] (M : Matrix m n 𝕜)
    {e : m → n} (he : Function.Injective e) {T : Matrix m m 𝕜} (hTdet : T.det ≠ 0)
    (hT : T * Tᴴ = M * Mᴴ) :
    ∃ Q : Matrix n n 𝕜, Q * Qᴴ = 1 ∧ M = T * Q.submatrix e id := by
  have := T.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hTdet)
  have hVV : T⁻¹ * M * (T⁻¹ * M)ᴴ = 1 :=
    calc T⁻¹ * M * (T⁻¹ * M)ᴴ = T⁻¹ * (M * Mᴴ) * T⁻¹ᴴ := by
          simp [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by simp [← hT, conjTranspose_nonsing_inv]
  obtain ⟨Q, hQ, hQV⟩ := exists_mul_conjTranspose_eq_one_and_submatrix_eq (T⁻¹ * M) he hVV
  exact ⟨Q, hQ, by simp [hQV, ← Matrix.mul_assoc]⟩

end Matrix
