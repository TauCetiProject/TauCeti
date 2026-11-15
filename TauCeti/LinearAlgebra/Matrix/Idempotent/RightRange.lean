/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Opposite
public import TauCeti.LinearAlgebra.Matrix.Idempotent.Basic

/-!
# Finitely generated projective right modules from column ranges of idempotent matrices

Let `R` be a semiring, not necessarily commutative. A matrix `M : Matrix m n R` acts on column
vectors `n → R` on the left by `v ↦ M *ᵥ v`, and this action is linear for the right `R`-module
structure (`Module Rᵐᵒᵖ`), given by `M.mulVecBilin R Rᵐᵒᵖ : (n → R) →ₗ[Rᵐᵒᵖ] (m → R)`.

For an idempotent matrix `e : Matrix ι ι R`, its column range `e R^ι` consists of the column
vectors fixed by `e`. It is a direct summand of `ι → R`, hence a finitely generated projective
right `R`-module, and every finitely generated projective right `R`-module arises in this way.

Rather than repeating the row-vector arguments of `TauCeti.LinearAlgebra.Matrix.Idempotent.Basic`,
this file intertwines left multiplication by `M` on `n → R` with right multiplication by
`Mᵀ.map op` on `n → Rᵐᵒᵖ` (`Matrix.rangeMulVecBilinEquivRangeVecMulLinear`), deduced from
`Matrix.op_comp_mulVec`, and transfers existence and block-sum decompositions across that
`Rᵐᵒᵖ`-linear isomorphism.

## Main definitions

* `Matrix.rangeMulVecBilinEquivRangeVecMulLinear`: the `Rᵐᵒᵖ`-linear isomorphism between the
  column range of `M` and the row range of `Mᵀ.map op`.
* `Matrix.rangeMulVecBilinMap`: applying a ring homomorphism `f` coordinatewise maps the column
  range of `M` semilinearly along `RingHom.op f` to the column range of `M.map f`.
* `Matrix.rangeMulVecBilinFromBlocksEquiv`: the column range of `Matrix.fromBlocks e 0 0 f` is the
  product of the column ranges of `e` and `f`.

## Main results

* `IsIdempotentElem.projective_range`: the range of an idempotent endomorphism of a projective
  module is projective.
* `IsIdempotentElem.mem_range_mulVecBilin_iff`: the column range of an idempotent matrix consists
  of its fixed column vectors.
* `IsIdempotentElem.projective_range_vecMulLinear` and
  `IsIdempotentElem.projective_range_mulVecBilin`: the row and column ranges of an idempotent
  matrix are projective.
* `Module.Finite.exists_linearEquiv_range_mulVecBilin`: every finitely generated projective right
  `R`-module is `Rᵐᵒᵖ`-linearly isomorphic to the column range of an idempotent matrix over `R`.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. A. Weibel, *The K-book*, Chapter I, §2, and Chapter II, §2.
* B. Blackadar, *K-Theory for Operator Algebras*, §4.6.
-/

public section

open LinearMap Matrix MulOpposite

section ProjectiveRange

/-- The range of an idempotent endomorphism of a projective module is a direct summand, hence
projective. -/
theorem IsIdempotentElem.projective_range {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Module.Projective R M] {f : M →ₗ[R] M} (hf : IsIdempotentElem f) :
    Module.Projective R (range f) :=
  Module.Projective.of_split (range f).subtype f.rangeRestrict <|
    LinearMap.ext fun v ↦ Subtype.ext (hf.mem_range_iff.mp v.2)

end ProjectiveRange

section ColumnRange

/-- Applying `MulOpposite.op` to each coordinate intertwines matrix-vector multiplication by `M`
with vector-matrix multiplication by `Mᵀ.map op`. -/
theorem Matrix.op_comp_mulVec {R m n : Type*} [NonUnitalNonAssocSemiring R] [Fintype n]
    (M : Matrix m n R) (v : n → R) :
    op ∘ (M *ᵥ v) = (op ∘ v) ᵥ* M.transpose.map op := by
  ext i
  simp [mulVec, vecMul, dotProduct]

/-- Transpose followed by entrywise `MulOpposite.op` preserves idempotence of matrices. -/
theorem IsIdempotentElem.transpose_map_op {R ι : Type*} [Mul R] [AddCommMonoid R] [Fintype ι]
    {e : Matrix ι ι R} (he : IsIdempotentElem e) :
    IsIdempotentElem (e.transpose.map op) := by
  have hop : IsIdempotentElem (op e) := by
    rw [IsIdempotentElem, ← op_mul, he.eq]
  exact hop.map RingEquiv.mopMatrix.symm

variable {R : Type*} [Semiring R] {ι ι' κ κ' : Type*}

section Fintype

variable [Fintype ι]

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

/-- The row range of an idempotent matrix over `R` is a projective left `R`-module. -/
theorem IsIdempotentElem.projective_range_vecMulLinear {e : Matrix ι ι R}
    (he : IsIdempotentElem e) : Module.Projective R (range e.vecMulLinear) :=
  he.vecMulLinear.projective_range

namespace Matrix

/-- Each column of a matrix lies in the range of its right-module column action: it is the image
of the corresponding standard basis vector. -/
theorem col_mem_range_mulVecBilin (M : Matrix ι' ι R) (j : ι) :
    M.col j ∈ range (M.mulVecBilin R Rᵐᵒᵖ) := by
  classical
  exact ⟨Pi.single j 1, by rw [mulVecBilin_apply, mulVec_single_one]⟩

/-- Coordinatewise `MulOpposite.op` identifies the right-module column range of `M` with the
left-module row range of `Mᵀ.map op` over `Rᵐᵒᵖ`. -/
def rangeMulVecBilinEquivRangeVecMulLinear (M : Matrix ι' ι R) :
    range (M.mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] range (M.transpose.map op).vecMulLinear where
  toFun v := ⟨op ∘ v, by
    obtain ⟨u, hu⟩ := v.2
    exact ⟨op ∘ u, by rw [vecMulLinear_apply, ← M.op_comp_mulVec u, ← hu]; rfl⟩⟩
  invFun w := ⟨unop ∘ w, by
    obtain ⟨u, hu⟩ := w.2
    refine ⟨unop ∘ u, ?_⟩
    apply (opLinearEquiv Rᵐᵒᵖ).injective.comp_left
    change op ∘ (M *ᵥ (unop ∘ u)) = op ∘ unop ∘ w
    rw [M.op_comp_mulVec]
    exact congrArg (fun x : ι' → Rᵐᵒᵖ ↦ x) hu⟩
  map_add' _ _ := rfl
  map_smul' r v := Subtype.ext <| funext fun i ↦ op_smul r ((v : ι' → R) i)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_rangeMulVecBilinEquivRangeVecMulLinear_apply (M : Matrix ι' ι R)
    (v : range (M.mulVecBilin R Rᵐᵒᵖ)) :
    (M.rangeMulVecBilinEquivRangeVecMulLinear v : ι' → Rᵐᵒᵖ) = op ∘ v :=
  (rfl)

@[simp]
theorem coe_rangeMulVecBilinEquivRangeVecMulLinear_symm_apply (M : Matrix ι' ι R)
    (w : range (M.transpose.map op).vecMulLinear) :
    (M.rangeMulVecBilinEquivRangeVecMulLinear.symm w : ι' → R) = unop ∘ w :=
  (rfl)

/-- A column vector `v` lies in the column range of `M` if and only if `op ∘ v` lies in the row
range of `Mᵀ.map op`. -/
theorem mem_range_mulVecBilin_iff_op_comp {M : Matrix ι' ι R} {v : ι' → R} :
    v ∈ range (M.mulVecBilin R Rᵐᵒᵖ) ↔ op ∘ v ∈ range (M.transpose.map op).vecMulLinear :=
  ⟨fun hv ↦ (M.rangeMulVecBilinEquivRangeVecMulLinear ⟨v, hv⟩).2,
    fun hw ↦ (M.rangeMulVecBilinEquivRangeVecMulLinear.symm ⟨op ∘ v, hw⟩).2⟩

/-- The column range of any matrix with finitely many columns is a finitely generated right
`R`-module. -/
instance finite_range_mulVecBilin (M : Matrix ι' ι R) :
    Module.Finite Rᵐᵒᵖ (range (M.mulVecBilin R Rᵐᵒᵖ)) :=
  Module.Finite.equiv M.rangeMulVecBilinEquivRangeVecMulLinear.symm

/-- Applying a ring homomorphism `f : R →+* S` to every coordinate gives an `(RingHom.op f)`-
semilinear map between the column ranges of `M` and `M.map f`. -/
def rangeMulVecBilinMap {S : Type*} [Semiring S] (M : Matrix ι' ι R) (f : R →+* S) :
    range (M.mulVecBilin R Rᵐᵒᵖ) →ₛₗ[RingHom.op f] range ((M.map f).mulVecBilin S Sᵐᵒᵖ) where
  toFun v := ⟨f ∘ v, by
    obtain ⟨u, hu⟩ := v.2
    exact ⟨f ∘ u, funext fun i ↦ by simp [← hu, RingHom.map_mulVec]⟩⟩
  map_add' _ _ := Subtype.ext <| funext fun _ ↦ by simp
  map_smul' r v := Subtype.ext <| funext fun i ↦ by
    induction r using MulOpposite.rec'
    simp

@[simp]
theorem coe_rangeMulVecBilinMap_apply {S : Type*} [Semiring S] (M : Matrix ι' ι R) (f : R →+* S)
    (v : range (M.mulVecBilin R Rᵐᵒᵖ)) :
    (M.rangeMulVecBilinMap f v : ι' → S) = f ∘ v :=
  (rfl)

end Matrix

/-- The column range of an idempotent matrix over `R` is a projective right `R`-module. -/
theorem IsIdempotentElem.projective_range_mulVecBilin {e : Matrix ι ι R}
    (he : IsIdempotentElem e) : Module.Projective Rᵐᵒᵖ (range (e.mulVecBilin R Rᵐᵒᵖ)) :=
  letI : Module.Projective Rᵐᵒᵖ (range (e.transpose.map op).vecMulLinear) :=
    he.transpose_map_op.projective_range_vecMulLinear
  Module.Projective.of_equiv e.rangeMulVecBilinEquivRangeVecMulLinear.symm

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
  exact congrFun (he.mem_range_mulVecBilin_iff.mp v.2).symm i

end Fintype

namespace Matrix

section FromBlocks

variable [Fintype ι'] [Fintype κ']

/-- A column vector lies in the column range of `Matrix.fromBlocks e 0 0 f` if and only if its two
halves lie in the column ranges of `e` and `f`. -/
theorem mem_range_mulVecBilin_fromBlocks_iff {e : Matrix ι ι' R} {f : Matrix κ κ' R}
    {v : ι ⊕ κ → R} :
    v ∈ range ((fromBlocks e 0 0 f).mulVecBilin R Rᵐᵒᵖ) ↔
      v ∘ Sum.inl ∈ range (e.mulVecBilin R Rᵐᵒᵖ) ∧
        v ∘ Sum.inr ∈ range (f.mulVecBilin R Rᵐᵒᵖ) := by
  have htr : (fromBlocks e 0 0 f).transpose.map op =
      fromBlocks (e.transpose.map op) 0 0 (f.transpose.map op) := by
    ext (_ | _) (_ | _) <;> simp
  rw [mem_range_mulVecBilin_iff_op_comp, htr, mem_range_vecMulLinear_fromBlocks_iff,
    mem_range_mulVecBilin_iff_op_comp, mem_range_mulVecBilin_iff_op_comp]
  rfl

/-- **Block sums of matrices on column ranges.** The right-module column range of
`Matrix.fromBlocks e 0 0 f` is the product of the column ranges of `e` and `f`. -/
def rangeMulVecBilinFromBlocksEquiv (e : Matrix ι ι' R) (f : Matrix κ κ' R) :
    range ((fromBlocks e 0 0 f).mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ]
      range (e.mulVecBilin R Rᵐᵒᵖ) × range (f.mulVecBilin R Rᵐᵒᵖ) where
  toFun v := (⟨(v : ι ⊕ κ → R) ∘ Sum.inl, (mem_range_mulVecBilin_fromBlocks_iff.mp v.2).1⟩,
    ⟨(v : ι ⊕ κ → R) ∘ Sum.inr, (mem_range_mulVecBilin_fromBlocks_iff.mp v.2).2⟩)
  invFun p := ⟨Sum.elim p.1 p.2, mem_range_mulVecBilin_fromBlocks_iff.mpr ⟨p.1.2, p.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subtype.ext (Sum.elim_comp_inl_inr _)
  right_inv _ := rfl

@[simp]
theorem coe_rangeMulVecBilinFromBlocksEquiv_apply_fst (e : Matrix ι ι' R) (f : Matrix κ κ' R)
    (v : range ((fromBlocks e 0 0 f).mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeMulVecBilinFromBlocksEquiv e f v).1 : ι → R) = (v : ι ⊕ κ → R) ∘ Sum.inl :=
  (rfl)

@[simp]
theorem coe_rangeMulVecBilinFromBlocksEquiv_apply_snd (e : Matrix ι ι' R) (f : Matrix κ κ' R)
    (v : range ((fromBlocks e 0 0 f).mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeMulVecBilinFromBlocksEquiv e f v).2 : κ → R) = (v : ι ⊕ κ → R) ∘ Sum.inr :=
  (rfl)

@[simp]
theorem coe_rangeMulVecBilinFromBlocksEquiv_symm_apply (e : Matrix ι ι' R) (f : Matrix κ κ' R)
    (p : range (e.mulVecBilin R Rᵐᵒᵖ) × range (f.mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeMulVecBilinFromBlocksEquiv e f).symm p : ι ⊕ κ → R) =
      Sum.elim (p.1 : ι → R) (p.2 : κ → R) :=
  (rfl)

end FromBlocks

end Matrix

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
  exact ⟨n, e, he, ⟨ψ.trans (htr ▸ e.rangeMulVecBilinEquivRangeVecMulLinear.symm)⟩⟩

end Module.Finite
