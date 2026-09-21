/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Extending orthonormal rows to an orthogonal matrix

A real `q × p` matrix `V` with `V * Vᵀ = 1` has orthonormal rows, and `q ≤ p` leaves room for
`p - q` more.  Extending those rows to an orthonormal basis of `ℝ ^ p` and reading the basis as
the rows of a square matrix exhibits `V` as the first `q` rows of an orthogonal matrix.

Dividing an arbitrary `M` of full row rank by a square factor `T` of its Gram matrix `M * Mᵀ`
leaves orthonormal rows, so `M = T * Q.submatrix _ id` for an orthogonal `Q`.  This is the `LQ`
decomposition, and it is what factors a congruence by a matrix of full row rank into a rotation
followed by a coordinate selection.

## Main results

* `Matrix.exists_mul_transpose_eq_one_and_submatrix_castLE_eq` — a real matrix with orthonormal
  rows consists of the first rows of an orthogonal matrix.
* `Matrix.exists_mul_transpose_eq_one_and_eq_mul_submatrix_castLE` — a real matrix of full row
  rank is a square factor of its Gram matrix times such a row selection.
-/

public section

namespace Matrix

open scoped RealInnerProductSpace

variable {p q : ℕ}

/-- **A real matrix with orthonormal rows is a row selection of an orthogonal matrix.**  If
`V * Vᵀ = 1` for a `q × p` matrix `V` with `q ≤ p`, then `V` consists of the first `q` rows of an
orthogonal `p × p` matrix. -/
theorem exists_mul_transpose_eq_one_and_submatrix_castLE_eq (V : Matrix (Fin q) (Fin p) ℝ)
    (hqp : q ≤ p) (hV : V * Vᵀ = 1) :
    ∃ Q : Matrix (Fin p) (Fin p) ℝ, Q * Qᵀ = 1 ∧ Q.submatrix (Fin.castLE hqp) id = V := by
  classical
  -- Pad `V` with zero rows, and read its rows as vectors of `ℝ ^ p`.
  set W : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.of fun i j => if h : (i : ℕ) < q then V ⟨i, h⟩ j else 0 with hW
  set v : Fin p → EuclideanSpace ℝ (Fin p) :=
    fun i => (EuclideanSpace.equiv (Fin p) ℝ).symm (W i) with hv
  have hinner : ∀ i i' : Fin p, ⟪v i, v i'⟫ = ∑ j, W i j * W i' j := by
    intro i i'
    simp [hv, PiLp.inner_apply, mul_comm]
  set s : Set (Fin p) := {i : Fin p | (i : ℕ) < q} with hs
  have hWrow : ∀ (i : Fin p) (hi : (i : ℕ) < q), W i = V ⟨(i : ℕ), hi⟩ := by
    intro i hi
    funext j
    simp [hW, hi]
  have horth : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨i', hi'⟩
    have hiq : (i : ℕ) < q := hi
    have hiq' : (i' : ℕ) < q := hi'
    have hval : ∑ j, W i j * W i' j = (V * Vᵀ) ⟨(i : ℕ), hiq⟩ ⟨(i' : ℕ), hiq'⟩ := by
      simp [Matrix.mul_apply, hWrow i hiq, hWrow i' hiq']
    rw [Set.domRestrict_apply, Set.domRestrict_apply, hinner, hval, hV]
    simp [Matrix.one_apply, Subtype.ext_iff, Fin.ext_iff]
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin p)) = Fintype.card (Fin p) := by simp
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨Matrix.of fun i j => EuclideanSpace.equiv (Fin p) ℝ (b i) j, ?_, ?_⟩
  · ext i i'
    have hbo := orthonormal_iff_ite.1 b.orthonormal i i'
    rw [PiLp.inner_apply] at hbo
    simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm] using hbo
  · ext i j
    have hmem : Fin.castLE hqp i ∈ s := by simp [hs, i.isLt]
    rw [Matrix.submatrix_apply, id_eq, Matrix.of_apply, hb _ hmem, hv]
    simp [hW]

/-- **A matrix of full row rank is a square factor of its Gram matrix times a row selection of an
orthogonal matrix.**  If `T * Tᵀ = M * Mᵀ` with `T` invertible, then `T⁻¹ * M` has orthonormal
rows, hence selects the first `q` rows of an orthogonal matrix `Q`, and `M = T * Q.submatrix _ id`.
This is the `LQ` decomposition of a matrix of full row rank. -/
theorem exists_mul_transpose_eq_one_and_eq_mul_submatrix_castLE (M : Matrix (Fin q) (Fin p) ℝ)
    (hqp : q ≤ p) {T : Matrix (Fin q) (Fin q) ℝ} (hTdet : T.det ≠ 0) (hT : T * Tᵀ = M * Mᵀ) :
    ∃ Q : Matrix (Fin p) (Fin p) ℝ, Q * Qᵀ = 1 ∧ M = T * Q.submatrix (Fin.castLE hqp) id := by
  have hTu : IsUnit T.det := isUnit_iff_ne_zero.2 hTdet
  have hTtu : IsUnit Tᵀ.det := by rwa [Matrix.det_transpose]
  have hVV : T⁻¹ * M * (T⁻¹ * M)ᵀ = 1 := by
    calc T⁻¹ * M * (T⁻¹ * M)ᵀ = T⁻¹ * (M * Mᵀ) * (T⁻¹)ᵀ := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = T⁻¹ * T * (Tᵀ * (Tᵀ)⁻¹) := by
          rw [← hT, Matrix.transpose_nonsing_inv]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [Matrix.nonsing_inv_mul T hTu, Matrix.mul_nonsing_inv Tᵀ hTtu, Matrix.one_mul]
  obtain ⟨Q, hQ, hQV⟩ := exists_mul_transpose_eq_one_and_submatrix_castLE_eq (T⁻¹ * M) hqp hVV
  refine ⟨Q, hQ, ?_⟩
  rw [hQV, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv T hTu, Matrix.one_mul]

end Matrix
