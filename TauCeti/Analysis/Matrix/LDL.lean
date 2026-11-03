/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.LDL
import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# The diagonals of the LDL decomposition

Mathlib's LDL decomposition writes a positive-definite matrix `S` as `L * D * Lᴴ` with `L` lower
triangular and `D` diagonal, but records nothing about the individual diagonal entries. This file
supplies them: the diagonal of `D` is positive, and both `LDL.lowerInv` and `LDL.lower` carry `1`
on the diagonal, so the lower factor of the decomposition is unitriangular.

## Main results

* `LDL.diagEntries_pos` — the diagonal entries of `D` are positive.
* `LDL.lowerInv_apply_diag` and `LDL.lower_apply_diag` — the lower factor of the LDL
  decomposition and its inverse are unitriangular.
* `Matrix.PosDef.exists_isUpperTriangular_conjTranspose_mul_mul_eq_one` — a positive-definite
  matrix `S` is normalized to `1` by an upper triangular change of basis: `Pᴴ * S * P = 1`.
-/

public section

open scoped ComplexOrder Matrix

namespace TauCeti

variable {𝕜 n : Type*} [RCLike 𝕜] [LinearOrder n]
  [LocallyFiniteOrderBot n] [Fintype n] {S : Matrix n n 𝕜} (hS : S.PosDef)

/-- The diagonal entries in Mathlib's LDL decomposition of a positive-definite matrix are
positive. -/
theorem _root_.LDL.diagEntries_pos (i : n) : 0 < LDL.diagEntries hS i := by
  have hdiag : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hS.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_invertible (LDL.lowerInv hS))
  simpa [LDL.diag] using hdiag.diag_pos (i := i)

/-- The lower factor in Mathlib's LDL decomposition is unitriangular: its inverse is the
Gram-Schmidt matrix, which carries `1` on the diagonal. -/
@[simp]
theorem _root_.LDL.lowerInv_apply_diag (i : n) : LDL.lowerInv hS i i = 1 := by
  let := Sᵀ.toNormedAddCommGroup hS.transpose
  let := Sᵀ.toInnerProductSpace hS.transpose.posSemidef
  rw [LDL.lowerInv]
  simpa only [Pi.basisFun_repr] using
    (Pi.basisFun 𝕜 n).repr_gramSchmidt_self_eq_one i

/-- The lower factor in Mathlib's LDL decomposition carries `1` on the diagonal, being the
inverse of a matrix that does. -/
@[simp]
theorem _root_.LDL.lower_apply_diag (i : n) : LDL.lower hS i i = 1 := by
  have htri : (LDL.lowerInv hS)ᵀ.IsUpperTriangular :=
    (LDL.isLowerTriangular_lowerInv hS).transpose
  have hinv := Matrix.inv_apply_diag_of_isUpperTriangular htri
    (LDL.lowerInv_apply_diag hS i)
  simpa [LDL.lower, ← Matrix.transpose_nonsing_inv] using hinv

end TauCeti

namespace Matrix.PosDef

variable {𝕜 n : Type*} [RCLike 𝕜] [LinearOrder n] [Fintype n] {S : Matrix n n 𝕜}

/-- **A positive-definite matrix is normalized to `1` by an upper triangular change of basis**:
there is an upper triangular `P` with `Pᴴ * S * P = 1`. If `L * S * Lᴴ = D` is the `LDL`
decomposition, then `P = Lᴴ * D^{-1/2}`. -/
theorem exists_isUpperTriangular_conjTranspose_mul_mul_eq_one (hS : S.PosDef) :
    ∃ P : Matrix n n 𝕜, P.IsUpperTriangular ∧ Pᴴ * S * P = 1 := by
  -- Mathlib's `LDL` decomposition is stated for a `LocallyFiniteOrderBot` index type. Every finite
  -- linear order is one, and the conclusion does not depend on the choice of instance.
  let : LocallyFiniteOrderBot n :=
    LocallyFiniteOrderBot.ofIic n (fun a => Finset.univ.filter (· ≤ a)) (by simp)
  have hd : ∀ i, ∃ x : ℝ, 0 < x ∧ (x : 𝕜) = LDL.diagEntries hS i := fun i =>
    RCLike.pos_iff_exists_ofReal.1 (LDL.diagEntries_pos hS i)
  choose x hx hxd using hd
  -- `c = D^{-1/2}`, so that `cᴴ D c = 1`
  set c : n → 𝕜 := fun i => ((Real.sqrt (x i))⁻¹ : ℝ)
  have hc : ∀ i, star (c i) * LDL.diagEntries hS i * c i = 1 := fun i => by
    have h : (Real.sqrt (x i))⁻¹ * x i * (Real.sqrt (x i))⁻¹ = 1 := by
      have h0 := (Real.sqrt_pos.2 (hx i)).ne'
      field_simp
      exact (Real.sq_sqrt (hx i).le).symm
    rw [← hxd i]
    simp only [c, RCLike.star_def, RCLike.conj_ofReal]
    exact_mod_cast h
  refine ⟨(LDL.lowerInv hS)ᴴ * diagonal c, ?_, ?_⟩
  · refine BlockTriangular.mul (fun i j hij => ?_) (blockTriangular_diagonal c)
    have h0 : LDL.lowerInv hS j i = 0 :=
      LDL.isLowerTriangular_lowerInv hS (OrderDual.toDual_lt_toDual.2 hij)
    rw [conjTranspose_apply, h0, star_zero]
  · calc ((LDL.lowerInv hS)ᴴ * diagonal c)ᴴ * S * ((LDL.lowerInv hS)ᴴ * diagonal c)
        = (diagonal c)ᴴ * (LDL.lowerInv hS * S * (LDL.lowerInv hS)ᴴ) * diagonal c := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = 1 := by
          rw [← LDL.diag_eq_lowerInv_conj, LDL.diag, diagonal_conjTranspose,
            diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
          exact congrArg diagonal (funext hc)

end Matrix.PosDef
