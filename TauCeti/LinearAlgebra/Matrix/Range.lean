/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Factoring matrices through a column range

A matrix `L'` factors as `L * G` whenever each of its columns belongs to the range of
matrix-vector multiplication by `L`. The column index type of `L'` need not be finite. We also
give a criterion, splitting off the top row, for the column range of a matrix to be a given
submodule.

Over an arbitrary semiring `R` (not necessarily commutative), this file also collects the basic
properties of right-module column ranges `LinearMap.range (M.mulVecBilin R Rᵐᵒᵖ)` (over `Rᵐᵒᵖ`)
under `Matrix.submatrix`, `Matrix.reindex`, and for the identity matrix `1 : Matrix m m R`.

## Main definitions

* `Matrix.rangeMulVecBilinSubmatrixEquiv` and `Matrix.rangeMulVecBilinReindexEquiv`: `Rᵐᵒᵖ`-linear
  isomorphisms of column ranges under `Matrix.submatrix` and `Matrix.reindex`.
* `Matrix.rangeMulVecBilinOneEquiv`: the column range of `1 : Matrix m m R` is `m → Rᵐᵒᵖ`.

## Main result

* `Matrix.col_mem_range_mulVecLin`: every column of `L` lies in the range of `L.mulVecLin`.
* `Matrix.row_mem_range_vecMulLinear`: every row of `e` lies in the range of `e.vecMulLinear`.
* `Matrix.col_mem_range_mulVecBilin`: every column of `M` lies in the range of
  `M.mulVecBilin R Rᵐᵒᵖ`.
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

/-- Reindexing the rows and columns of a matrix along equivalences `σ` and `τ` via
`Matrix.submatrix` induces an `Rᵐᵒᵖ`-linear isomorphism between their column ranges, acting by
precomposition with `σ`. This is the `simp`-normal form of `rangeMulVecBilinReindexEquiv`. -/
def rangeMulVecBilinSubmatrixEquiv {ι₂ ι₂' : Type*} [Fintype ι₂] (M : Matrix ι' ι R)
    (σ : ι₂' ≃ ι') (τ : ι₂ ≃ ι) :
    range (M.mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] range ((M.submatrix σ τ).mulVecBilin R Rᵐᵒᵖ) where
  toFun v := ⟨(v : ι' → R) ∘ σ, by
    obtain ⟨u, hu⟩ := v.property
    refine ⟨u ∘ τ, ?_⟩
    simp [mulVecBilin_apply, submatrix_mulVec_equiv, Function.comp_assoc, ← hu]⟩
  invFun w := ⟨(w : ι₂' → R) ∘ σ.symm, by
    obtain ⟨u, hu⟩ := w.property
    refine ⟨u ∘ τ.symm, ?_⟩
    rw [mulVecBilin_apply]
    calc M *ᵥ (u ∘ τ.symm)
        = (M.submatrix σ τ).submatrix σ.symm τ.symm *ᵥ (u ∘ τ.symm) := by simp
      _ = ((M.submatrix σ τ) *ᵥ ((u ∘ τ.symm) ∘ τ.symm.symm)) ∘ σ.symm :=
          submatrix_mulVec_equiv _ _ _ _
      _ = (w : ι₂' → R) ∘ σ.symm := by
          rw [show (u ∘ τ.symm) ∘ τ.symm.symm = u by ext; simp, ← mulVecBilin_apply R Rᵐᵒᵖ, hu]⟩
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

/-- Reindexing the rows and columns of a matrix along bijections `σ` and `τ` induces an
`Rᵐᵒᵖ`-linear isomorphism between their column ranges, acting by precomposition with `σ.symm`. -/
def rangeMulVecBilinReindexEquiv {ι₂ ι₂' : Type*} [Fintype ι₂] (M : Matrix ι' ι R)
    (σ : ι' ≃ ι₂') (τ : ι ≃ ι₂) :
    range (M.mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] range ((M.reindex σ τ).mulVecBilin R Rᵐᵒᵖ) :=
  M.rangeMulVecBilinSubmatrixEquiv σ.symm τ.symm

/-- `rangeMulVecBilinReindexEquiv` simplifies to `rangeMulVecBilinSubmatrixEquiv` with inverted
equivalences. -/
@[simp]
theorem rangeMulVecBilinReindexEquiv_eq_submatrixEquiv {ι₂ ι₂' : Type*} [Fintype ι₂]
    (M : Matrix ι' ι R) (σ : ι' ≃ ι₂') (τ : ι ≃ ι₂) :
    M.rangeMulVecBilinReindexEquiv σ τ = M.rangeMulVecBilinSubmatrixEquiv σ.symm τ.symm :=
  (rfl)

/-- Coordinate computation for `rangeMulVecBilinReindexEquiv`. Not marked `@[simp]` because
`rangeMulVecBilinReindexEquiv_eq_submatrixEquiv` and `Matrix.reindex_apply` rewrite the equivalence
and its codomain type to `rangeMulVecBilinSubmatrixEquiv`; see
`coe_rangeMulVecBilinSubmatrixEquiv_apply` for the `simp`-normal form. -/
theorem coe_rangeMulVecBilinReindexEquiv_apply {ι₂ ι₂' : Type*} [Fintype ι₂]
    (M : Matrix ι' ι R) (σ : ι' ≃ ι₂') (τ : ι ≃ ι₂) (v : range (M.mulVecBilin R Rᵐᵒᵖ)) :
    (M.rangeMulVecBilinReindexEquiv σ τ v : ι₂' → R) = (v : ι' → R) ∘ σ.symm :=
  (rfl)

/-- Coordinate computation for `(rangeMulVecBilinReindexEquiv _ _ _).symm`. Not marked `@[simp]`
because `rangeMulVecBilinReindexEquiv_eq_submatrixEquiv` and `Matrix.reindex_apply` rewrite the
equivalence and its domain type to `rangeMulVecBilinSubmatrixEquiv`; see
`coe_rangeMulVecBilinSubmatrixEquiv_symm_apply` for the `simp`-normal form. -/
theorem coe_rangeMulVecBilinReindexEquiv_symm_apply {ι₂ ι₂' : Type*} [Fintype ι₂]
    (M : Matrix ι' ι R) (σ : ι' ≃ ι₂') (τ : ι ≃ ι₂)
    (w : range ((M.reindex σ τ).mulVecBilin R Rᵐᵒᵖ)) :
    ((M.rangeMulVecBilinReindexEquiv σ τ).symm w : ι' → R) = (w : ι₂' → R) ∘ σ :=
  (rfl)

end Fintype

end ColumnRange

/-- The column range of the identity matrix `1 : Matrix m m R` is `Rᵐᵒᵖ`-linearly isomorphic to
the standard free `Rᵐᵒᵖ`-module `m → Rᵐᵒᵖ`. -/
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

end Matrix
