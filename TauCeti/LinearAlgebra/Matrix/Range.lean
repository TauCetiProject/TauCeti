/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Finiteness.Basic

import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.Data.Matrix.Mul

/-!
# Factoring matrices through a column range

A matrix `L'` factors as `L * G` whenever each of its columns belongs to the range of
matrix-vector multiplication by `L`. The column index type of `L'` need not be finite. We also
give a criterion, splitting off the top row, for the column range of a matrix to be a given
submodule.

Over an arbitrary semiring `R` (not necessarily commutative), this file also collects the basic
properties of row ranges `LinearMap.range M.vecMulLinear` and right-module column ranges
`LinearMap.range (M.mulVecBilin R Rᵐᵒᵖ)` (over `Rᵐᵒᵖ`): functoriality under entrywise ring
homomorphisms, block-diagonal decompositions, the equivalence between row ranges over `Rᵐᵒᵖ` and
column ranges over `R`, finiteness, `Matrix.submatrix`, `Matrix.reindex`, the identity matrix
`1 : Matrix m m R`, and column-range `finrank` formulas under `StrongRankCondition Rᵐᵒᵖ`.

## Main definitions

* `Matrix.rangeVecMulLinearMap` and `Matrix.rangeMulVecBilinMap`: semilinear maps on row and
  column ranges induced by applying a ring homomorphism coordinatewise.
* `Matrix.rangeVecMulLinearFromBlocksEquiv` and `Matrix.rangeMulVecBilinFromBlocksEquiv`: product
  decompositions for the row and column ranges of `Matrix.fromBlocks e 0 0 f`.
* `Matrix.rangeVecMulLinearTransposeMapOpEquiv`: `Rᵐᵒᵖ`-linear isomorphism identifying the row
  range of `eᵀ.map MulOpposite.op` with the column range of `e`.
* `Matrix.rangeMulVecBilinSubmatrixEquiv` and `Matrix.rangeMulVecBilinReindexEquiv`: `Rᵐᵒᵖ`-linear
  isomorphisms of column ranges under `Matrix.submatrix` and `Matrix.reindex`.
* `Matrix.rangeMulVecBilinOneEquiv`: the column range of `1 : Matrix m m R` is `m → Rᵐᵒᵖ`.

## Main result

* `Matrix.col_mem_range_mulVecLin`: every column of `L` lies in the range of `L.mulVecLin`.
* `Matrix.row_mem_range_vecMulLinear`: every row of `e` lies in the range of `e.vecMulLinear`.
* `Matrix.col_mem_range_mulVecBilin`: every column of `M` lies in the range of
  `M.mulVecBilin R Rᵐᵒᵖ`.
* `Matrix.mem_range_vecMulLinear_fromBlocks_iff` and `Matrix.mem_range_mulVecBilin_fromBlocks_iff`:
  membership in the row and column ranges of a block-diagonal matrix.
* `Matrix.mem_range_mulVecBilin_iff_op_comp`: membership in the column range of `M` in terms of
  the row range of `Mᵀ.map op`.
* `Matrix.finite_range_mulVecBilin`: the column range of a matrix with finitely many columns is a
  finitely generated right `R`-module.
* `Matrix.finrank_range_mulVecBilin_one` and `Matrix.finrank_range_mulVecBilin_single_one`:
  column-range `finrank` of `1` and of diagonal matrix units `Eᵢᵢ` under
  `StrongRankCondition Rᵐᵒᵖ`.
* `Matrix.exists_mul_eq_of_range_le`: construct the right factor from column preimages.
* `Matrix.mul_left_cancel_of_mulVec_injective`: cancel an injective left factor even for
  matrices with an empty output-column index type.
* `Matrix.range_mulVecLin_eq_of_succ`: a matrix with columns in a submodule `L` of `R^(n+1)` has
  column range `L` if it reaches every vector of `L` below the top row and every vector of `L`
  supported on the top row.
-/

public section

namespace Matrix

section LeftCancellation

variable {R m ι κ : Type*} [NonUnitalSemiring R] [Fintype ι]

/-- If matrix-vector multiplication by `L` is injective, multiplication by `L`
cancels on the left, even when the right-hand matrices have no columns. -/
theorem mul_left_cancel_of_mulVec_injective
    {L : Matrix m ι R} (hL : Function.Injective L.mulVec)
    {X Y : Matrix ι κ R} (hXY : L * X = L * Y) : X = Y := by
  classical
  rcases isEmpty_or_nonempty κ with hEmpty | hNonempty
  · ext i j
    exact (hEmpty.false j).elim
  · let : Inhabited κ := ⟨Classical.choice hNonempty⟩
    exact (mul_right_injective_iff_mulVec_injective.mpr hL) hXY

end LeftCancellation

variable {R m ι κ : Type*} [CommSemiring R] [Fintype ι]

/-- Every column of `L` lies in the range of matrix-vector multiplication by `L`. -/
theorem col_mem_range_mulVecLin (L : Matrix m ι R) (j : ι) :
    L.col j ∈ LinearMap.range L.mulVecLin := by
  classical
  exact ⟨Pi.single j 1, by rw [mulVecLin_apply, mulVec_single_one]⟩

/-- If every column of `L'` lies in the range of `L`, then `L' = L * G` for some `G`.
The index type of the columns of `L'` need not be finite. -/
theorem exists_mul_eq_of_range_le {L : Matrix m ι R} {L' : Matrix m κ R}
    (h : ∀ j : κ, L'.col j ∈ LinearMap.range L.mulVecLin) :
    ∃ G : Matrix ι κ R, L * G = L' := by
  classical
  have hpre (j : κ) : ∃ v : ι → R, L.mulVec v = L'.col j := h j
  choose v hv using hpre
  refine ⟨Matrix.of fun i j => v j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (hv j) i

section Succ

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- A matrix `H` with columns in a submodule `L` of `R^(n+1)` has column range `L` if every vector
of `L` agrees with a vector of the column range below the top row, and every vector of `L`
supported on the top row lies in the column range. -/
theorem range_mulVecLin_eq_of_succ {n : ℕ} {L : Submodule R (Fin (n + 1) → R)}
    {H : Matrix (Fin (n + 1)) ι R} (hcol : ∀ j, H.col j ∈ L)
    (htail : ∀ x ∈ L, ∃ c, ∀ i : Fin n, (H *ᵥ c) i.succ = x i.succ)
    (hsingle : ∀ a, Pi.single 0 a ∈ L → Pi.single 0 a ∈ LinearMap.range H.mulVecLin) :
    LinearMap.range H.mulVecLin = L := by
  have hle : LinearMap.range H.mulVecLin ≤ L := by
    rw [range_mulVecLin, Submodule.span_le, Set.range_subset_iff]
    exact hcol
  refine le_antisymm hle fun x hx ↦ ?_
  obtain ⟨c, hc⟩ := htail x hx
  -- The difference of `x` and `H *ᵥ c` is supported on the top row.
  have hy : x - H *ᵥ c = Pi.single 0 ((x - H *ᵥ c) 0) := by
    ext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp [hc i]
  have hmem := hsingle _ (hy ▸ sub_mem hx (hle ⟨c, rfl⟩))
  rw [← hy] at hmem
  simpa using add_mem hmem (LinearMap.mem_range_self H.mulVecLin c)

end Succ

section RowRange

open LinearMap

variable {A : Type*} [Semiring A] {ι κ ι' κ' : Type*} [Fintype ι]

/-- Each row of a matrix lies in the range of right multiplication by it: it is the image of the
corresponding standard basis vector. -/
theorem row_mem_range_vecMulLinear (e : Matrix ι κ A) (i : ι) :
    e i ∈ range e.vecMulLinear := by
  classical
  exact ⟨Pi.single i 1, Matrix.single_one_vecMul i e⟩

/-- The `f`-semilinear map between the ranges of right multiplication of row vectors by a matrix
`e` and by its entrywise image `e.map f` under a ring homomorphism `f`, applying `f` to every
coordinate. For an idempotent `e` this is the map `Aⁿ e → Bⁿ f(e)`. -/
def rangeVecMulLinearMap {B : Type*} [Semiring B] (e : Matrix ι ι' A) (f : A →+* B) :
    range e.vecMulLinear →ₛₗ[f] range (e.map f).vecMulLinear where
  toFun v := ⟨f ∘ v, by
    obtain ⟨u, hu⟩ := v.property
    exact ⟨f ∘ u, funext fun i ↦ by simp [← hu, RingHom.map_vecMul]⟩⟩
  map_add' _ _ := Subtype.ext <| funext fun _ ↦ by simp
  map_smul' _ _ := Subtype.ext <| funext fun _ ↦ by simp

@[simp]
theorem coe_rangeVecMulLinearMap_apply {B : Type*} [Semiring B] (e : Matrix ι ι' A) (f : A →+* B)
    (v : range e.vecMulLinear) : (e.rangeVecMulLinearMap f v : ι' → B) = f ∘ v :=
  (rfl)

section FromBlocks

variable [Fintype κ]

/-- A row vector lies in the range of right multiplication by the block-diagonal matrix
`Matrix.fromBlocks e 0 0 f` exactly when its two parts lie in the ranges of `e` and of `f`. -/
theorem mem_range_vecMulLinear_fromBlocks_iff {e : Matrix ι ι' A} {f : Matrix κ κ' A}
    {v : ι' ⊕ κ' → A} :
    v ∈ range (fromBlocks e 0 0 f).vecMulLinear ↔
      v ∘ Sum.inl ∈ range e.vecMulLinear ∧ v ∘ Sum.inr ∈ range f.vecMulLinear := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨⟨u ∘ Sum.inl, ?_⟩, ⟨u ∘ Sum.inr, ?_⟩⟩ <;>
      rw [vecMulLinear_apply, vecMulLinear_apply, ← Sum.elim_comp_inl_inr u, vecMul_fromBlocks] <;>
      simp
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨Sum.elim a b, ?_⟩
    rw [← Sum.elim_comp_inl_inr v, ← ha, ← hb]
    simp [vecMul_fromBlocks]

/-- **Block sums of matrices.** The range of right multiplication by the block-diagonal matrix
`Matrix.fromBlocks e 0 0 f` is the product of the ranges of `e` and of `f`. -/
def rangeVecMulLinearFromBlocksEquiv (e : Matrix ι ι' A) (f : Matrix κ κ' A) :
    range (fromBlocks e 0 0 f).vecMulLinear ≃ₗ[A]
      range e.vecMulLinear × range f.vecMulLinear where
  toFun v := (⟨(v : ι' ⊕ κ' → A) ∘ Sum.inl, (mem_range_vecMulLinear_fromBlocks_iff.1 v.property).1⟩,
    ⟨(v : ι' ⊕ κ' → A) ∘ Sum.inr, (mem_range_vecMulLinear_fromBlocks_iff.1 v.property).2⟩)
  invFun p := ⟨Sum.elim p.1 p.2, mem_range_vecMulLinear_fromBlocks_iff.2 ⟨p.1.property,
      p.2.property⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subtype.ext (Sum.elim_comp_inl_inr _)
  right_inv _ := rfl

@[simp]
theorem coe_rangeVecMulLinearFromBlocksEquiv_apply_fst (e : Matrix ι ι' A) (f : Matrix κ κ' A)
    (v : range (fromBlocks e 0 0 f).vecMulLinear) :
    ((rangeVecMulLinearFromBlocksEquiv e f v).1 : ι' → A) = (v : ι' ⊕ κ' → A) ∘ Sum.inl :=
  (rfl)

@[simp]
theorem coe_rangeVecMulLinearFromBlocksEquiv_apply_snd (e : Matrix ι ι' A) (f : Matrix κ κ' A)
    (v : range (fromBlocks e 0 0 f).vecMulLinear) :
    ((rangeVecMulLinearFromBlocksEquiv e f v).2 : κ' → A) = (v : ι' ⊕ κ' → A) ∘ Sum.inr :=
  (rfl)

@[simp]
theorem coe_rangeVecMulLinearFromBlocksEquiv_symm_apply (e : Matrix ι ι' A) (f : Matrix κ κ' A)
    (p : range e.vecMulLinear × range f.vecMulLinear) :
    ((rangeVecMulLinearFromBlocksEquiv e f).symm p : ι' ⊕ κ' → A) =
      Sum.elim (p.1 : ι' → A) (p.2 : κ' → A) :=
  (rfl)

end FromBlocks

end RowRange

section ColumnRange

open LinearMap MulOpposite

variable {R : Type*} [Semiring R] {ι ι' κ κ' : Type*}

section Fintype

variable [Fintype ι]

/-- Each column of a matrix lies in the range of its right-module column action: it is the image
of the corresponding standard basis vector. -/
theorem col_mem_range_mulVecBilin (M : Matrix ι' ι R) (j : ι) :
    M.col j ∈ range (M.mulVecBilin R Rᵐᵒᵖ) := by
  classical
  exact ⟨Pi.single j 1, by rw [mulVecBilin_apply, mulVec_single_one]⟩

/-- **Columns as rows over the opposite ring.** For `e : Matrix ι' ι R`, the column range
`range (e.mulVecBilin R Rᵐᵒᵖ)` is `Rᵐᵒᵖ`-linearly isomorphic via coordinatewise `unop` to the
row range of `eᵀ.map op` over `Rᵐᵒᵖ`. -/
def rangeVecMulLinearTransposeMapOpEquiv (e : Matrix ι' ι R) :
    range (eᵀ.map MulOpposite.op).vecMulLinear ≃ₗ[Rᵐᵒᵖ] range (mulVecBilin R Rᵐᵒᵖ e) :=
  let L' : (ι' → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (ι' → R) :=
    .piCongrRight fun _ ↦ (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  let L : (ι → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (ι → R) :=
    .piCongrRight fun _ ↦ (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  have hL : L'.toLinearMap ∘ₗ (eᵀ.map MulOpposite.op).vecMulLinear =
      mulVecBilin R Rᵐᵒᵖ e ∘ₗ L.toLinearMap := by
    ext v i; simp [L, L', vecMul, mulVec, dotProduct]
  (L'.submoduleMap _).trans <| .ofEq _ _ <| by
    rw [← range_comp, hL, range_comp_of_range_eq_top _ L.range]

@[simp]
theorem coe_rangeVecMulLinearTransposeMapOpEquiv_apply (e : Matrix ι' ι R)
    (v : range (eᵀ.map MulOpposite.op).vecMulLinear) :
    (rangeVecMulLinearTransposeMapOpEquiv e v : ι' → R) = MulOpposite.unop ∘ v :=
  (rfl)

@[simp]
theorem coe_rangeVecMulLinearTransposeMapOpEquiv_symm_apply (M : Matrix ι' ι R)
    (v : range (M.mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeVecMulLinearTransposeMapOpEquiv M).symm v : ι' → Rᵐᵒᵖ) = op ∘ v := by
  ext i
  have h := congrFun (congrArg (fun x : range (M.mulVecBilin R Rᵐᵒᵖ) ↦ (x : ι' → R))
    ((rangeVecMulLinearTransposeMapOpEquiv M).apply_symm_apply v)) i
  rw [coe_rangeVecMulLinearTransposeMapOpEquiv_apply] at h
  exact (op_unop _).symm.trans (congrArg op h)

/-- A column vector `v` lies in the column range of `M` iff `op ∘ v` lies in the row range of
`Mᵀ.map op`. -/
theorem mem_range_mulVecBilin_iff_op_comp {M : Matrix ι' ι R} {v : ι' → R} :
    v ∈ range (M.mulVecBilin R Rᵐᵒᵖ) ↔ op ∘ v ∈ range (M.transpose.map op).vecMulLinear := by
  refine ⟨fun hv ↦ ?_, fun hw ↦ ?_⟩
  · simpa only [coe_rangeVecMulLinearTransposeMapOpEquiv_symm_apply] using
      ((rangeVecMulLinearTransposeMapOpEquiv M).symm ⟨v, hv⟩).property
  · have h : (rangeVecMulLinearTransposeMapOpEquiv M ⟨op ∘ v, hw⟩ : ι' → R) = v := by
      ext i; simp [coe_rangeVecMulLinearTransposeMapOpEquiv_apply]
    exact h ▸ (rangeVecMulLinearTransposeMapOpEquiv M ⟨op ∘ v, hw⟩).property

/-- The column range of any matrix with finitely many columns is finitely generated over `Rᵐᵒᵖ`. -/
instance finite_range_mulVecBilin (M : Matrix ι' ι R) :
    Module.Finite Rᵐᵒᵖ (range (M.mulVecBilin R Rᵐᵒᵖ)) :=
  Module.Finite.equiv (rangeVecMulLinearTransposeMapOpEquiv M)

/-- Applying `f : R →+* S` entrywise gives a `RingHom.op f`-semilinear map between the column
ranges of `M` and `M.map f`. -/
def rangeMulVecBilinMap {S : Type*} [Semiring S] (M : Matrix ι' ι R) (f : R →+* S) :
    range (M.mulVecBilin R Rᵐᵒᵖ) →ₛₗ[RingHom.op f] range ((M.map f).mulVecBilin S Sᵐᵒᵖ) :=
  ((rangeVecMulLinearTransposeMapOpEquiv (M.map f)).toLinearMap.comp
    ((LinearEquiv.ofEq _ _ (congrArg (fun N ↦ range N.vecMulLinear)
      (transpose_map_op_map_ringHom_op M f))).toLinearMap.comp
      ((M.transpose.map op).rangeVecMulLinearMap (RingHom.op f)))).comp
    (rangeVecMulLinearTransposeMapOpEquiv M).symm.toLinearMap

@[simp]
theorem coe_rangeMulVecBilinMap_apply {S : Type*} [Semiring S] (M : Matrix ι' ι R) (f : R →+* S)
    (v : range (M.mulVecBilin R Rᵐᵒᵖ)) :
    (M.rangeMulVecBilinMap f v : ι' → S) = f ∘ v := by
  ext i; simp [rangeMulVecBilinMap]

/-- Reindexing rows and columns via `Matrix.submatrix` induces an `Rᵐᵒᵖ`-linear isomorphism
between column ranges, acting by precomposition with `σ`. -/
def rangeMulVecBilinSubmatrixEquiv {ι₂ ι₂' : Type*} [Fintype ι₂] (M : Matrix ι' ι R)
    (σ : ι₂' ≃ ι') (τ : ι₂ ≃ ι) :
    range (M.mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] range ((M.submatrix σ τ).mulVecBilin R Rᵐᵒᵖ) where
  toFun v := ⟨(v : ι' → R) ∘ σ, by
    obtain ⟨u, hu⟩ := v.property
    exact ⟨u ∘ τ, by simp [mulVecBilin_apply, submatrix_mulVec_equiv, Function.comp_assoc, ← hu]⟩⟩
  invFun w := ⟨(w : ι₂' → R) ∘ σ.symm, by
    obtain ⟨u, hu⟩ := w.property
    refine ⟨u ∘ τ.symm, ?_⟩
    rw [mulVecBilin_apply]
    conv_lhs => rw [← show (M.submatrix σ τ).submatrix σ.symm τ.symm = M by simp]
    rw [submatrix_mulVec_equiv]
    simpa [Function.comp_assoc] using congrArg (· ∘ σ.symm) hu⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := Subtype.ext <| funext fun i ↦ by simp
  right_inv w := Subtype.ext <| funext fun i₂ ↦ by simp

@[simp]
theorem coe_rangeMulVecBilinSubmatrixEquiv_apply {ι₂ ι₂' : Type*} [Fintype ι₂]
    (M : Matrix ι' ι R) (σ : ι₂' ≃ ι') (τ : ι₂ ≃ ι) (v : range (M.mulVecBilin R Rᵐᵒᵖ)) :
    (M.rangeMulVecBilinSubmatrixEquiv σ τ v : ι₂' → R) = (v : ι' → R) ∘ σ :=
  (rfl)

@[simp]
theorem coe_rangeMulVecBilinSubmatrixEquiv_symm_apply {ι₂ ι₂' : Type*} [Fintype ι₂]
    (M : Matrix ι' ι R) (σ : ι₂' ≃ ι') (τ : ι₂ ≃ ι)
    (w : range ((M.submatrix σ τ).mulVecBilin R Rᵐᵒᵖ)) :
    ((M.rangeMulVecBilinSubmatrixEquiv σ τ).symm w : ι' → R) = (w : ι₂' → R) ∘ σ.symm :=
  (rfl)

/-- Reindexing rows and columns along `σ` and `τ` induces an `Rᵐᵒᵖ`-linear isomorphism between
column ranges, acting by precomposition with `σ.symm`. -/
def rangeMulVecBilinReindexEquiv {ι₂ ι₂' : Type*} [Fintype ι₂] (M : Matrix ι' ι R)
    (σ : ι' ≃ ι₂') (τ : ι ≃ ι₂) :
    range (M.mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] range ((M.reindex σ τ).mulVecBilin R Rᵐᵒᵖ) :=
  M.rangeMulVecBilinSubmatrixEquiv σ.symm τ.symm

@[simp]
theorem rangeMulVecBilinReindexEquiv_eq_submatrixEquiv {ι₂ ι₂' : Type*} [Fintype ι₂]
    (M : Matrix ι' ι R) (σ : ι' ≃ ι₂') (τ : ι ≃ ι₂) :
    M.rangeMulVecBilinReindexEquiv σ τ = M.rangeMulVecBilinSubmatrixEquiv σ.symm τ.symm :=
  (rfl)

theorem coe_rangeMulVecBilinReindexEquiv_apply {ι₂ ι₂' : Type*} [Fintype ι₂]
    (M : Matrix ι' ι R) (σ : ι' ≃ ι₂') (τ : ι ≃ ι₂) (v : range (M.mulVecBilin R Rᵐᵒᵖ)) :
    (M.rangeMulVecBilinReindexEquiv σ τ v : ι₂' → R) = (v : ι' → R) ∘ σ.symm :=
  (rfl)

theorem coe_rangeMulVecBilinReindexEquiv_symm_apply {ι₂ ι₂' : Type*} [Fintype ι₂]
    (M : Matrix ι' ι R) (σ : ι' ≃ ι₂') (τ : ι ≃ ι₂)
    (w : range ((M.reindex σ τ).mulVecBilin R Rᵐᵒᵖ)) :
    ((M.rangeMulVecBilinReindexEquiv σ τ).symm w : ι' → R) = (w : ι₂' → R) ∘ σ :=
  (rfl)

end Fintype

section FromBlocks

variable [Fintype ι] [Fintype κ]

/-- A column vector lies in the column range of `Matrix.fromBlocks e 0 0 f` iff its two halves
lie in the column ranges of `e` and `f`. -/
theorem mem_range_mulVecBilin_fromBlocks_iff {e : Matrix ι' ι R} {f : Matrix κ' κ R}
    {v : ι' ⊕ κ' → R} :
    v ∈ range ((fromBlocks e 0 0 f).mulVecBilin R Rᵐᵒᵖ) ↔
      v ∘ Sum.inl ∈ range (e.mulVecBilin R Rᵐᵒᵖ) ∧
        v ∘ Sum.inr ∈ range (f.mulVecBilin R Rᵐᵒᵖ) := by
  rw [mem_range_mulVecBilin_iff_op_comp]
  simp only [fromBlocks_transpose, transpose_zero, fromBlocks_map, Matrix.map_zero _ op_zero]
  rw [mem_range_vecMulLinear_fromBlocks_iff, mem_range_mulVecBilin_iff_op_comp,
    mem_range_mulVecBilin_iff_op_comp]
  rfl

/-- **Block sums on column ranges.** The column range of `Matrix.fromBlocks e 0 0 f` is the
product of the column ranges of `e` and `f`. -/
def rangeMulVecBilinFromBlocksEquiv (e : Matrix ι' ι R) (f : Matrix κ' κ R) :
    range ((fromBlocks e 0 0 f).mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ]
      range (e.mulVecBilin R Rᵐᵒᵖ) × range (f.mulVecBilin R Rᵐᵒᵖ) :=
  (rangeVecMulLinearTransposeMapOpEquiv (fromBlocks e 0 0 f)).symm.trans <|
    (LinearEquiv.ofEq _ _ (congrArg (fun N : Matrix (ι ⊕ κ) (ι' ⊕ κ') Rᵐᵒᵖ ↦ range N.vecMulLinear)
      (by simp [fromBlocks_transpose, fromBlocks_map]))).trans <|
      (rangeVecMulLinearFromBlocksEquiv (e.transpose.map op) (f.transpose.map op)).trans <|
        (rangeVecMulLinearTransposeMapOpEquiv e).prodCongr
          (rangeVecMulLinearTransposeMapOpEquiv f)

@[simp]
theorem coe_rangeMulVecBilinFromBlocksEquiv_apply_fst (e : Matrix ι' ι R) (f : Matrix κ' κ R)
    (v : range ((fromBlocks e 0 0 f).mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeMulVecBilinFromBlocksEquiv e f v).1 : ι' → R) = (v : ι' ⊕ κ' → R) ∘ Sum.inl := by
  ext i; simp [rangeMulVecBilinFromBlocksEquiv]

@[simp]
theorem coe_rangeMulVecBilinFromBlocksEquiv_apply_snd (e : Matrix ι' ι R) (f : Matrix κ' κ R)
    (v : range ((fromBlocks e 0 0 f).mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeMulVecBilinFromBlocksEquiv e f v).2 : κ' → R) = (v : ι' ⊕ κ' → R) ∘ Sum.inr := by
  ext i; simp [rangeMulVecBilinFromBlocksEquiv]

@[simp]
theorem coe_rangeMulVecBilinFromBlocksEquiv_symm_apply (e : Matrix ι' ι R) (f : Matrix κ' κ R)
    (p : range (e.mulVecBilin R Rᵐᵒᵖ) × range (f.mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeMulVecBilinFromBlocksEquiv e f).symm p : ι' ⊕ κ' → R) =
      Sum.elim (p.1 : ι' → R) (p.2 : κ' → R) := by
  ext (i | i) <;> simp [rangeMulVecBilinFromBlocksEquiv]

end FromBlocks

end ColumnRange

/-- The column range of `1 : Matrix m m R` is `Rᵐᵒᵖ`-linearly isomorphic to `m → Rᵐᵒᵖ`. -/
def rangeMulVecBilinOneEquiv (m R : Type*) [Semiring R] [Fintype m] [DecidableEq m] :
    LinearMap.range ((1 : Matrix m m R).mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (m → Rᵐᵒᵖ) where
  toFun v := MulOpposite.op ∘ v
  invFun v := ⟨MulOpposite.unop ∘ v, ⟨MulOpposite.unop ∘ v, by simp⟩⟩
  map_add' _ _ := rfl
  map_smul' r v := funext fun i ↦ MulOpposite.op_smul r ((v : m → R) i)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem rangeMulVecBilinOneEquiv_apply {m R : Type*} [Semiring R] [Fintype m] [DecidableEq m]
    (v : LinearMap.range ((1 : Matrix m m R).mulVecBilin R Rᵐᵒᵖ)) :
    rangeMulVecBilinOneEquiv m R v = MulOpposite.op ∘ (v : m → R) :=
  (rfl)

@[simp]
theorem coe_rangeMulVecBilinOneEquiv_symm_apply {m R : Type*} [Semiring R] [Fintype m]
    [DecidableEq m] (v : m → Rᵐᵒᵖ) :
    ((rangeMulVecBilinOneEquiv m R).symm v : m → R) = MulOpposite.unop ∘ v :=
  (rfl)

/-- When `Rᵐᵒᵖ` has the strong rank condition, `range ((1 : Matrix m m R).mulVecBilin R Rᵐᵒᵖ)`
has right `R`-rank `Fintype.card m`. -/
theorem finrank_range_mulVecBilin_one (R : Type*) [Semiring R] [StrongRankCondition Rᵐᵒᵖ]
    (m : Type*) [Fintype m] [DecidableEq m] :
    Module.finrank Rᵐᵒᵖ (LinearMap.range ((1 : Matrix m m R).mulVecBilin R Rᵐᵒᵖ)) =
      Fintype.card m :=
  (rangeMulVecBilinOneEquiv m R).finrank_eq.trans (Module.finrank_fintype_fun_eq_card Rᵐᵒᵖ)

/-- When `Rᵐᵒᵖ` has the strong rank condition, the column range of `Eᵢᵢ` has right `R`-rank `1`.
-/
theorem finrank_range_mulVecBilin_single_one (R : Type*) [Semiring R] [StrongRankCondition Rᵐᵒᵖ]
    {m : Type*} [Fintype m] [DecidableEq m] (i : m) :
    Module.finrank Rᵐᵒᵖ (LinearMap.range ((single i i (1 : R)).mulVecBilin R Rᵐᵒᵖ)) = 1 := by
  let ψ : LinearMap.range ((single i i (1 : R)).mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ :=
    { toFun := fun w ↦ MulOpposite.op ((w : m → R) i)
      invFun := fun r ↦ ⟨Pi.single i (MulOpposite.unop r), ⟨Pi.single i (MulOpposite.unop r), by
        ext j; by_cases hj : j = i <;> simp [mulVec_apply, hj]⟩⟩
      map_add' := fun _ _ ↦ MulOpposite.op_add _ _
      map_smul' := fun r w ↦ by simp
      left_inv := fun w ↦ Subtype.ext <| by
        obtain ⟨v, hv⟩ := w.property
        ext j; have hvj := congrFun hv j
        by_cases hj : j = i
        · subst hj; simp
        · simp [mulVecBilin_apply, mulVec_apply, hj] at hvj; simp [hj, ← hvj]
      right_inv := fun _ ↦ by simp }
  exact ψ.finrank_eq.trans (Module.finrank_self Rᵐᵒᵖ)

end Matrix
