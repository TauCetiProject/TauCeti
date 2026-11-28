/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.StdBasis

/-!
# Factoring determinants with fixed columns or rows

Let K be a field, e : L ≃ a ⊕ N an equivalence of finite index sets, and Z : Matrix L N K a
fixed matrix. For any matrix X : Matrix L a K, the determinant of the square matrix
(Matrix.fromCols X Z).submatrix id e depends on X as a constant scalar multiple of
(Y * X).det for a fixed matrix Y : Matrix a L K independent of X.

## Main results

* TauCeti.det_fromCols_eq_zero_of_not_linearIndependent: if the columns of Z are linearly
  dependent, then ((Matrix.fromCols X Z).submatrix id e).det = 0 for all X.
* TauCeti.exists_leftAnnihilator_fromRows_det_ne_zero: if Z has linearly independent columns,
  there exist Y : Matrix a L K and W : Matrix N L K with Y * Z = 0 and
  ((Matrix.fromRows Y W).submatrix e id).det ≠ 0.
* TauCeti.exists_det_fromCols_eq_mul_det: for any Z : Matrix L N K, there exist
  Y : Matrix a L K and γ : K such that
  ((Matrix.fromCols X Z).submatrix id e).det = γ * (Y * X).det for all X.
* TauCeti.exists_det_fromRows_eq_mul_det: dual factorization for Matrix.fromRows.

## Provenance

Adapted from New.exists_det_fromCols_eq_mul_det in
src/New/OneLift/ComparisonOperator/DeterminantProducts.lean of grh-lean
(https://github.com/lsernau/grh-lean, commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC), generalized from ℂ (with Hermitian column clearing)
to an arbitrary field K using kernel complements.
-/

public section

open Matrix Module

namespace TauCeti

variable {K a L N : Type*} [Field K] [Fintype L]

/-- If the columns of Z : Matrix L N K are linearly dependent over K, then the determinant of
(Matrix.fromCols X Z).submatrix id e vanishes for every X : Matrix L a K. -/
theorem det_fromCols_eq_zero_of_not_linearIndependent [DecidableEq L]
    (e : L ≃ a ⊕ N) (Z : Matrix L N K) (hZ : ¬ LinearIndependent K Z.col) (X : Matrix L a K) :
    ((Matrix.fromCols X Z).submatrix id e).det = 0 := by
  classical
  have : Finite a := Finite.of_injective (e.symm ∘ .inl) (e.symm.injective.comp Sum.inl_injective)
  have : Finite N := Finite.of_injective (e.symm ∘ .inr) (e.symm.injective.comp Sum.inr_injective)
  let := Fintype.ofFinite a; let := Fintype.ofFinite N
  rw [Fintype.not_linearIndependent_iff] at hZ
  obtain ⟨v, hv_sum, i₀, hi₀⟩ := hZ
  let w : L → K := fun l ↦ Sum.elim 0 v (e l)
  have hw_ne : w ≠ 0 := fun h0 ↦ by
    have := congrFun h0 (e.symm (.inr i₀)); simp [w, hi₀] at this
  have hmul : ((Matrix.fromCols X Z).submatrix id e) *ᵥ w = 0 := by
    ext l
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq, Pi.zero_apply, w]
    rw [Fintype.sum_equiv e _ (fun s ↦ X.fromCols Z l s * Sum.elim (0 : a → K) v s) (fun _ ↦ rfl)]
    have hl := congrFun hv_sum l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hl
    simpa [Matrix.fromCols, Fintype.sum_sum_type, Matrix.col, mul_comm] using hl
  by_contra hdet
  have hinv := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  exact hw_ne (by
    calc w = 1 *ᵥ w := (Matrix.one_mulVec w).symm
      _ = _ := by rw [← hinv, ← Matrix.mulVec_mulVec, hmul, Matrix.mulVec_zero])

/-- If Z : Matrix L N K has linearly independent columns and e : L ≃ a ⊕ N, there exist
Y : Matrix a L K and W : Matrix N L K such that Y * Z = 0 and
((Matrix.fromRows Y W).submatrix e id).det ≠ 0. -/
theorem exists_leftAnnihilator_fromRows_det_ne_zero [DecidableEq L]
    (e : L ≃ a ⊕ N) (Z : Matrix L N K) (hZ : LinearIndependent K Z.col) :
    ∃ (Y : Matrix a L K) (W : Matrix N L K),
      Y * Z = 0 ∧ ((Matrix.fromRows Y W).submatrix e id).det ≠ 0 := by
  classical
  have : Finite a := Finite.of_injective (e.symm ∘ .inl) (e.symm.injective.comp Sum.inl_injective)
  have : Finite N := Finite.of_injective (e.symm ∘ .inr) (e.symm.injective.comp Sum.inr_injective)
  let := Fintype.ofFinite a; let := Fintype.ofFinite N
  let K₀ := LinearMap.ker (Matrix.mulVecLin Zᵀ)
  obtain ⟨W, hKW⟩ := Submodule.exists_isCompl K₀
  have hcard : Fintype.card L = Fintype.card a + Fintype.card N := by
    simpa using Fintype.card_congr e
  have hrank : finrank K (LinearMap.range (Matrix.mulVecLin Zᵀ)) = Fintype.card N := by
    rw [Matrix.finrank_range_mulVecLin, Matrix.rank_transpose, ← Matrix.finrank_span_range_col,
      finrank_span_eq_card hZ]
  have hfinK : finrank K K₀ = Fintype.card a := by
    have hnull := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin Zᵀ)
    rw [hrank, Module.finrank_pi, hcard] at hnull; exact Nat.add_right_cancel (by
      rw [add_comm]; exact hnull)
  have hfinW : finrank K W = Fintype.card N := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hKW
    rw [hfinK, Module.finrank_pi, hcard] at hsum; omega
  let bK := (Module.finBasisOfFinrankEq K K₀ hfinK).reindex (Fintype.equivFin a).symm
  let bW := (Module.finBasisOfFinrankEq K W hfinW).reindex (Fintype.equivFin N).symm
  let bAll := ((bK.prod bW).map (Submodule.prodEquivOfIsCompl K₀ W hKW)).reindex e.symm
  let Y : Matrix a L K := Matrix.of fun i l ↦ (bK i).val l
  let W₀ : Matrix N L K := Matrix.of fun i l ↦ (bW i).val l
  let U : Matrix L L K := (Matrix.fromRows Y W₀).submatrix e id
  refine ⟨Y, W₀, ?_, ?_⟩
  · ext i j
    simpa [Matrix.vecMul, dotProduct, Matrix.mul_apply, Y] using congrFun (bK i).property j
  · have hUT : Uᵀ = LinearMap.toMatrix (Pi.basisFun K L) (Pi.basisFun K L)
        bAll.equivFun.symm.toLinearMap := by
      ext l i
      simp only [Matrix.transpose_apply, U, Matrix.submatrix_apply, id_eq,
        LinearMap.toMatrix_apply, Pi.basisFun_repr, LinearEquiv.coe_coe, Pi.basisFun_apply]
      have h1 : bAll.equivFun.symm (Pi.single i 1) = bAll i := by simp
      rw [h1]; cases hi : e i <;> simp [Y, W₀, bAll, hi]
    refine IsUnit.ne_zero (by
      rw [← Matrix.det_transpose]
      refine isUnit_det_of_right_inverse (B := LinearMap.toMatrix (Pi.basisFun K L)
        (Pi.basisFun K L) bAll.equivFun.toLinearMap) ?_
      rw [hUT, ← LinearMap.toMatrix_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
        LinearEquiv.refl_toLinearMap, LinearMap.toMatrix_id])

/-- For any matrix Z : Matrix L N K over a field K and equivalence e : L ≃ a ⊕ N, there exist
Y : Matrix a L K and γ : K such that
((Matrix.fromCols X Z).submatrix id e).det = γ * (Y * X).det for all X : Matrix L a K. -/
theorem exists_det_fromCols_eq_mul_det [Fintype a] [DecidableEq a] [DecidableEq L]
    (e : L ≃ a ⊕ N) (Z : Matrix L N K) :
    ∃ (Y : Matrix a L K) (γ : K), ∀ X : Matrix L a K,
      ((Matrix.fromCols X Z).submatrix id e).det = γ * (Y * X).det := by
  classical
  have : Finite N := Finite.of_injective (e.symm ∘ .inr) (e.symm.injective.comp Sum.inr_injective)
  let := Fintype.ofFinite N
  by_cases hZ : LinearIndependent K Z.col
  · obtain ⟨Y, W₀, hYZ, hU_det⟩ := exists_leftAnnihilator_fromRows_det_ne_zero e Z hZ
    let U : Matrix L L K := (Matrix.fromRows Y W₀).submatrix e id
    refine ⟨Y, (W₀ * Z).det / U.det, fun X ↦ ?_⟩
    have hblock : U * (Matrix.fromCols X Z).submatrix id e =
        (Matrix.fromBlocks (Y * X) 0 (W₀ * X) (W₀ * Z)).submatrix e e := by
      ext i j; cases hi : e i <;> cases hj : e j <;> simp [U, Matrix.mul_apply, ← hYZ, hi, hj]
    have hdet : U.det * ((Matrix.fromCols X Z).submatrix id e).det =
        (Y * X).det * (W₀ * Z).det := by
      rw [← Matrix.det_mul, hblock, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]
    rw [div_mul_eq_mul_div, eq_div_iff hU_det, mul_comm _ U.det, hdet, mul_comm]
  · exact ⟨0, 0, fun X ↦ by simp [det_fromCols_eq_zero_of_not_linearIndependent e Z hZ X]⟩

/-- Dual factorization for stacked rows: for any Z : Matrix N L K over a field K and
e : L ≃ a ⊕ N, there exist Y : Matrix L a K and γ : K such that
((Matrix.fromRows X Z).submatrix e id).det = γ * (X * Y).det for all X : Matrix a L K. -/
theorem exists_det_fromRows_eq_mul_det [Fintype a] [DecidableEq a] [DecidableEq L]
    (e : L ≃ a ⊕ N) (Z : Matrix N L K) :
    ∃ (Y : Matrix L a K) (γ : K), ∀ X : Matrix a L K,
      ((Matrix.fromRows X Z).submatrix e id).det = γ * (X * Y).det := by
  obtain ⟨Y, γ, hY⟩ := exists_det_fromCols_eq_mul_det e Zᵀ
  refine ⟨Yᵀ, γ, fun X ↦ ?_⟩
  have htr : ((Matrix.fromRows X Z).submatrix e id)ᵀ = (Matrix.fromCols Xᵀ Zᵀ).submatrix id e := by
    ext i j; cases hj : e j <;> simp [hj]
  rw [← Matrix.det_transpose, htr, hY Xᵀ, ← Matrix.det_transpose (Y * Xᵀ),
    Matrix.transpose_mul, Matrix.transpose_transpose]

end TauCeti
