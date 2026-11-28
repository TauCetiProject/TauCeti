/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
import TauCeti.GroupTheory.Perm.Inversion
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Orientation signs of real Clifford coordinate permutations

This module computes the determinants of coordinate-reindexing isometries on the positive-definite
real forms `TauCeti.realCliffordForm n 0`, separating permutation-sign and permutation-matrix
dependencies from `TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic`.

## Main results

* `TauCeti.det_realCliffordFormZeroReindex`: determinant of a coordinate permutation
  `realCliffordFormZeroReindex σ` is the sign of `σ`.
* `TauCeti.det_realCliffordFormZeroReindex_trans_congr`: determinant of a coordinate reindexing
  `realCliffordFormZeroReindex e` followed by the rank cast `realCliffordFormCongr h rfl` is the
  sign of the forward permutation `e.symm.trans (finCongr h)`.
* `TauCeti.det_realCliffordBlockSwapIsometry` and
  `TauCeti.det_realCliffordBlockSwapIsometry_self`: determinants of block swaps
  `ℝ^(p + q) → ℝ^(q + p)` (identified back to `ℝ^(p + q)` by
  `realCliffordFormCongr (add_comm q p) rfl`) and `ℝ^(k + k)`.
* `TauCeti.det_realCliffordMiddleSwapIsometry`: determinant of the middle-block exchange
  `realCliffordMiddleSwapIsometry p q` composed with the order-preserving coordinate cast
  `realCliffordFormCongr (add_add_add_comm p p q q) rfl`.
-/

public section

open QuadraticMap

namespace TauCeti

/-- The determinant of the coordinate-permutation isometry `realCliffordFormZeroReindex σ` is the
sign of the permutation `σ`. -/
theorem det_realCliffordFormZeroReindex (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    LinearMap.det (realCliffordFormZeroReindex σ).toLinearMap =
      ((Equiv.Perm.sign σ : ℤ) : ℝ) := by
  have hlin : (realCliffordFormZeroReindex σ).toLinearMap =
      Matrix.toLin' (σ.permMatrix ℝ) :=
    LinearMap.ext fun x ↦ funext fun i ↦ by
      rw [LinearEquiv.coe_toLinearMap, IsometryEquiv.coe_toLinearEquiv,
        realCliffordFormZeroReindex_apply, Matrix.toLin'_apply, Matrix.permMatrix_mulVec,
        Function.comp_apply]
  rw [hlin, LinearMap.det_toLin', Matrix.det_permutation]

/-- Composing a coordinate reindexing `realCliffordFormZeroReindex e` with the order-preserving
rank cast `realCliffordFormCongr h rfl` has determinant equal to the sign of the forward permutation
`e.symm.trans (finCongr h)`. -/
theorem det_realCliffordFormZeroReindex_trans_congr {m n : ℕ} (e : Fin n ≃ Fin m)
    (h : n = m) :
    LinearMap.det ((realCliffordFormZeroReindex e).trans
        (realCliffordFormCongr h rfl)).toLinearMap =
      ((Equiv.Perm.sign (e.symm.trans (finCongr h)) : ℤ) : ℝ) := by
  let σ : Equiv.Perm (Fin m) := (finCongr h.symm).trans e
  have hσ : (realCliffordFormZeroReindex e).trans (realCliffordFormCongr h rfl) =
      realCliffordFormZeroReindex σ := by
    refine DFunLike.ext _ _ fun x ↦ funext fun (i : Fin m) ↦ ?_
    rw [QuadraticMap.IsometryEquiv.trans_apply, realCliffordFormCongr_apply,
      realCliffordFormZeroReindex_apply, realCliffordFormZeroReindex_apply]
    exact congrArg (fun j ↦ x (e j)) (Fin.ext (by simp [finCongr]))
  have hinv : σ = (e.symm.trans (finCongr h))⁻¹ := by
    ext i
    simp [σ, Equiv.Perm.inv_def, finCongr]
  rw [hσ, det_realCliffordFormZeroReindex, hinv, Equiv.Perm.sign_inv]

/-- Swapping the first `p` and last `q` coordinates of `ℝ^(p + q)` via
`realCliffordBlockSwapIsometry p q`, followed by identifying the target `ℝ^(q + p)` with
`ℝ^(p + q)` via the order-preserving coordinate cast `realCliffordFormCongr (add_comm q p) rfl`,
has determinant `(-1) ^ (p * q)`. -/
theorem det_realCliffordBlockSwapIsometry (p q : ℕ) :
    LinearMap.det ((realCliffordBlockSwapIsometry p q).trans
        (realCliffordFormCongr (add_comm q p) rfl)).toLinearMap =
      (-1 : ℝ) ^ (p * q) := by
  have hswap : realCliffordBlockSwapIsometry p q =
      realCliffordFormZeroReindex (finAddFlip : Fin (q + p) ≃ Fin (p + q)) :=
    DFunLike.ext _ _ fun x ↦ funext fun (i : Fin (q + p)) ↦ by
      rw [realCliffordBlockSwapIsometry_apply, realCliffordFormZeroReindex_apply]
  have hflip : (finAddFlip : Fin (q + p) ≃ Fin (p + q)).symm = finAddFlip := by
    ext i; simp [finAddFlip]
  rw [hswap, det_realCliffordFormZeroReindex_trans_congr,
    hflip, sign_finAddFlip_trans_finCongr]
  simp

/-- Swapping the two `k`-blocks of `ℝ^(k + k)` has determinant `(-1) ^ k`. -/
theorem det_realCliffordBlockSwapIsometry_self (k : ℕ) :
    LinearMap.det (realCliffordBlockSwapIsometry k k).toLinearMap = (-1 : ℝ) ^ k := by
  have h : (realCliffordBlockSwapIsometry k k).trans
      (realCliffordFormCongr (add_comm k k) rfl) = realCliffordBlockSwapIsometry k k :=
    DFunLike.ext _ _ fun _ ↦ by
      rw [realCliffordFormCongr_rfl, QuadraticMap.IsometryEquiv.trans_apply,
        QuadraticMap.IsometryEquiv.refl_apply]
  rw [← h, det_realCliffordBlockSwapIsometry]
  rcases Nat.even_or_odd k with hk | hk
  · rw [(hk.mul_left k).neg_one_pow, hk.neg_one_pow]
  · rw [(hk.mul hk).neg_one_pow, hk.neg_one_pow]

/-- **The determinant of the middle-block exchange `realCliffordMiddleSwapIsometry p q`**, composed
with the order-preserving coordinate cast `realCliffordFormCongr (add_add_add_comm p p q q) rfl`
identifying `ℝ^((p + p) + (q + q))` with `ℝ^((p + q) + (p + q))`, is `(-1) ^ (p * q)`. -/
theorem det_realCliffordMiddleSwapIsometry (p q : ℕ) :
    LinearMap.det ((realCliffordMiddleSwapIsometry p q).trans
        (realCliffordFormCongr (add_add_add_comm p p q q) rfl)).toLinearMap =
      (-1) ^ (p * q) := by
  have hswap : realCliffordMiddleSwapIsometry p q =
      realCliffordFormZeroReindex (finSumFinSumFinComm p p q q) :=
    DFunLike.ext _ _ fun x ↦ funext fun (i : Fin ((p + p) + (q + q))) ↦ by
      rw [realCliffordMiddleSwapIsometry_apply, realCliffordFormZeroReindex_apply]
  rw [hswap, det_realCliffordFormZeroReindex_trans_congr,
    finSumFinSumFinComm_symm, sign_finSumFinSumFinComm_trans_finCongr]
  simp [mul_comm]

end TauCeti
