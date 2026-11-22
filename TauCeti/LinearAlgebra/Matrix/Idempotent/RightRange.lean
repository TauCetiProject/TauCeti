/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Idempotent

import Mathlib.RingTheory.Finiteness.Basic
import TauCeti.Data.Matrix.Mul

/-!
# Finitely generated projective right modules from column ranges of idempotent matrices

Let `R` be a semiring, not necessarily commutative. A matrix `M : Matrix m n R` acts on column
vectors `n → R` on the left by `v ↦ M *ᵥ v`, and this action is linear for the right `R`-module
structure (`Module Rᵐᵒᵖ`), given by `M.mulVecBilin R Rᵐᵒᵖ : (n → R) →ₗ[Rᵐᵒᵖ] (m → R)`.

Rather than repeating the row-vector arguments of `TauCeti.LinearAlgebra.Matrix.Idempotent`, this
file transfers finiteness, functoriality, block-sum decompositions, projectivity, and projective
presentations across `Matrix.rangeVecMulLinearTransposeMapOpEquiv`, which identifies the row range
of `Mᵀ.map op` in `m → Rᵐᵒᵖ` with the column range of `M` in `m → R`.

## Main definitions

* `Matrix.rangeMulVecBilinMap`: semilinear map on column ranges induced by applying a ring
  homomorphism coordinatewise.
* `Matrix.rangeMulVecBilinFromBlocksEquiv`: product decomposition for the column range of
  `Matrix.fromBlocks e 0 0 f`.

## Main results

* `Matrix.mem_range_mulVecBilin_iff_op_comp`: membership in the column range of `M` in terms of
  the row range of `Mᵀ.map op`.
* `Matrix.finite_range_mulVecBilin`: the column range of a matrix with finitely many columns is a
  finitely generated right `R`-module.
* `Matrix.mem_range_mulVecBilin_fromBlocks_iff`: membership in the column range of a block-diagonal
  matrix.
* `IsIdempotentElem.mulVecBilin`: left multiplication of column vectors by an idempotent matrix is
  an idempotent `Rᵐᵒᵖ`-linear endomorphism.
* `IsIdempotentElem.mem_range_mulVecBilin_iff`: the column range of an idempotent matrix consists
  of its fixed column vectors.
* `IsIdempotentElem.projective_range_mulVecBilin`: the column range of an idempotent matrix is
  projective.
* `IsIdempotentElem.eq_sum_smul_col`: every vector in the column range of an idempotent matrix `e`
  is a right-linear combination of the columns of `e`.
* `Module.Finite.exists_linearEquiv_range_mulVecBilin`: every finitely generated projective right
  `R`-module is `Rᵐᵒᵖ`-linearly isomorphic to the column range of an idempotent matrix over `R`.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. A. Weibel, *The K-book*, Chapter I, §2, and Chapter II, §2.
* B. Blackadar, *K-Theory for Operator Algebras*, §4.6.
-/

public section

open LinearMap Matrix MulOpposite

namespace Matrix

variable {R : Type*} [Semiring R] {ι ι' κ κ' : Type*}

section Fintype

variable [Fintype ι]

@[simp]
theorem coe_rangeVecMulLinearTransposeMapOpEquiv_symm_apply (M : Matrix ι' ι R)
    (v : range (M.mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeVecMulLinearTransposeMapOpEquiv M).symm v : ι' → Rᵐᵒᵖ) = op ∘ v := by
  ext i
  have h := congrFun (congrArg (fun x : range (M.mulVecBilin R Rᵐᵒᵖ) ↦ (x : ι' → R))
    ((rangeVecMulLinearTransposeMapOpEquiv M).apply_symm_apply v)) i
  rw [coe_rangeVecMulLinearTransposeMapOpEquiv_apply] at h
  exact (op_unop _).symm.trans (congrArg op h)

/-- A column vector `v` lies in the column range of `M` if and only if `op ∘ v` lies in the row
range of `Mᵀ.map op`. -/
theorem mem_range_mulVecBilin_iff_op_comp {M : Matrix ι' ι R} {v : ι' → R} :
    v ∈ range (M.mulVecBilin R Rᵐᵒᵖ) ↔ op ∘ v ∈ range (M.transpose.map op).vecMulLinear := by
  refine ⟨fun hv ↦ ?_, fun hw ↦ ?_⟩
  · simpa only [coe_rangeVecMulLinearTransposeMapOpEquiv_symm_apply] using
      ((rangeVecMulLinearTransposeMapOpEquiv M).symm ⟨v, hv⟩).property
  · have h : (rangeVecMulLinearTransposeMapOpEquiv M ⟨op ∘ v, hw⟩ : ι' → R) = v := by
      ext i
      simp [coe_rangeVecMulLinearTransposeMapOpEquiv_apply]
    exact h ▸ (rangeVecMulLinearTransposeMapOpEquiv M ⟨op ∘ v, hw⟩).property

/-- The column range of any matrix with finitely many columns is a finitely generated right
`R`-module. -/
instance finite_range_mulVecBilin (M : Matrix ι' ι R) :
    Module.Finite Rᵐᵒᵖ (range (M.mulVecBilin R Rᵐᵒᵖ)) :=
  Module.Finite.equiv (rangeVecMulLinearTransposeMapOpEquiv M)

/-- Applying a ring homomorphism `f : R →+* S` to every coordinate gives an `(RingHom.op f)`-
semilinear map between the column ranges of `M` and `M.map f`. -/
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
  ext i
  simp [rangeMulVecBilinMap]

end Fintype

section FromBlocks

variable [Fintype ι] [Fintype κ]

/-- A column vector lies in the column range of `Matrix.fromBlocks e 0 0 f` if and only if its two
halves lie in the column ranges of `e` and `f`. -/
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

/-- **Block sums of matrices on column ranges.** The right-module column range of
`Matrix.fromBlocks e 0 0 f` is the product of the column ranges of `e` and `f`. -/
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
  ext i
  simp [rangeMulVecBilinFromBlocksEquiv]

@[simp]
theorem coe_rangeMulVecBilinFromBlocksEquiv_apply_snd (e : Matrix ι' ι R) (f : Matrix κ' κ R)
    (v : range ((fromBlocks e 0 0 f).mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeMulVecBilinFromBlocksEquiv e f v).2 : κ' → R) = (v : ι' ⊕ κ' → R) ∘ Sum.inr := by
  ext i
  simp [rangeMulVecBilinFromBlocksEquiv]

@[simp]
theorem coe_rangeMulVecBilinFromBlocksEquiv_symm_apply (e : Matrix ι' ι R) (f : Matrix κ' κ R)
    (p : range (e.mulVecBilin R Rᵐᵒᵖ) × range (f.mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeMulVecBilinFromBlocksEquiv e f).symm p : ι' ⊕ κ' → R) =
      Sum.elim (p.1 : ι' → R) (p.2 : κ' → R) := by
  ext (i | i) <;> simp [rangeMulVecBilinFromBlocksEquiv]

end FromBlocks

end Matrix

section ColumnRange

variable {R : Type*} [Semiring R] {ι : Type*} [Fintype ι]

/-- Left multiplication of column vectors by an idempotent matrix is an idempotent `Rᵐᵒᵖ`-linear
endomorphism. -/
theorem IsIdempotentElem.mulVecBilin {e : Matrix ι ι R} (he : IsIdempotentElem e) :
    IsIdempotentElem (e.mulVecBilin R Rᵐᵒᵖ) := by
  ext v : 1
  simp [mul_apply_eq_comp, Matrix.mulVec_mulVec, he.eq]

/-- The column range of an idempotent matrix `e` consists of the column vectors fixed by `e`. -/
theorem IsIdempotentElem.mem_range_mulVecBilin_iff {e : Matrix ι ι R} (he : IsIdempotentElem e)
    {v : ι → R} : v ∈ range (e.mulVecBilin R Rᵐᵒᵖ) ↔ e *ᵥ v = v :=
  he.mulVecBilin.mem_range_iff

/-- The column range of an idempotent matrix over `R` is a projective right `R`-module. -/
theorem IsIdempotentElem.projective_range_mulVecBilin {e : Matrix ι ι R}
    (he : IsIdempotentElem e) : Module.Projective Rᵐᵒᵖ (range (e.mulVecBilin R Rᵐᵒᵖ)) :=
  letI : Module.Projective Rᵐᵒᵖ (range (e.transpose.map op).vecMulLinear) :=
    he.matrix_transpose_map_op.projective_range_vecMulLinear
  Module.Projective.of_equiv (rangeVecMulLinearTransposeMapOpEquiv e)

/-- Every vector `v` in the column range of an idempotent matrix `e` is the right-linear
combination `∑ j, op (v j) • e.col j` of the columns of `e`. -/
theorem IsIdempotentElem.eq_sum_smul_col {e : Matrix ι ι R} (he : IsIdempotentElem e)
    (v : range (e.mulVecBilin R Rᵐᵒᵖ)) :
    v = ∑ j, op ((v : ι → R) j) •
      (⟨e.col j, e.col_mem_range_mulVecBilin j⟩ : range (e.mulVecBilin R Rᵐᵒᵖ)) := by
  ext1
  rw [Submodule.coe_sum]
  ext i
  simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, col_apply, op_smul_eq_mul]
  exact congrFun (he.mem_range_mulVecBilin_iff.mp v.property).symm i

end ColumnRange

namespace Module.Finite

variable (R P : Type*) [Semiring R] [AddCommMonoid P] [Module Rᵐᵒᵖ P] [Module.Finite Rᵐᵒᵖ P]
  [Module.Projective Rᵐᵒᵖ P]

/-- **Finitely generated projective right modules come from idempotent matrices.** Every finitely
generated projective right `R`-module is `Rᵐᵒᵖ`-linearly isomorphic to the column range of an
idempotent square matrix over `R`. -/
theorem exists_linearEquiv_range_mulVecBilin :
    ∃ (n : ℕ) (e : Matrix (Fin n) (Fin n) R), IsIdempotentElem e ∧
      Nonempty (P ≃ₗ[Rᵐᵒᵖ] LinearMap.range (e.mulVecBilin R Rᵐᵒᵖ)) := by
  obtain ⟨n, e', he', ⟨ψ⟩⟩ := exists_linearEquiv_range_vecMulLinear Rᵐᵒᵖ P
  let e : Matrix (Fin n) (Fin n) R := (RingEquiv.mopMatrix e').unop
  have he : IsIdempotentElem e := by
    rw [IsIdempotentElem, ← op_inj, op_mul, op_unop]
    exact (he'.map RingEquiv.mopMatrix).eq
  have htr : e.transpose.map op = e' :=
    RingEquiv.mopMatrix.symm_apply_apply e'
  exact ⟨n, e, he, ⟨ψ.trans (htr ▸ rangeVecMulLinearTransposeMapOpEquiv e)⟩⟩

end Module.Finite
