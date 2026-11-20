/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Idempotent.Basic

import TauCeti.Data.Matrix.Mul

/-!
# Finitely generated projective right modules from column ranges of idempotent matrices

Let `R` be a semiring, not necessarily commutative. A matrix `M : Matrix m n R` acts on column
vectors `n → R` on the left by `v ↦ M *ᵥ v`, and this action is linear for the right `R`-module
structure (`Module Rᵐᵒᵖ`), given by `M.mulVecBilin R Rᵐᵒᵖ : (n → R) →ₗ[Rᵐᵒᵖ] (m → R)`.

For an idempotent matrix `e : Matrix ι ι R`, its column range `e R^ι` consists of the column
vectors fixed by `e`. It is a retract of `ι → R` (and a complemented direct summand when `R` is a
ring), hence a finitely generated projective right `R`-module, and every finitely generated
projective right `R`-module arises in this way.

Rather than repeating the row-vector arguments of `TauCeti.LinearAlgebra.Matrix.Idempotent.Basic`,
this file transfers projectivity and existence across the `Rᵐᵒᵖ`-linear isomorphism
`Matrix.rangeMulVecBilinEquivRangeVecMulLinear` (defined in `TauCeti.LinearAlgebra.Matrix.Range`),
which identifies the column range of `M` in `m → R` with the row range of `Mᵀ.map op` in
`m → Rᵐᵒᵖ`. General column-range lemmas that do not assume idempotence live in
`TauCeti.LinearAlgebra.Matrix.Range`.

## Main results

* `IsIdempotentElem.transpose_map_op`: transpose followed by entrywise `MulOpposite.op` preserves
  idempotence of matrices.
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

section ColumnRange

/-- Transpose followed by entrywise `MulOpposite.op` preserves idempotence of matrices. -/
theorem IsIdempotentElem.transpose_map_op {R ι : Type*} [Mul R] [AddCommMonoid R] [Fintype ι]
    {e : Matrix ι ι R} (he : IsIdempotentElem e) :
    IsIdempotentElem (e.transpose.map op) := by
  rw [IsIdempotentElem, transpose_map_op_mul, he.eq]

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
  exact ⟨n, e, he, ⟨ψ.trans (htr ▸ e.rangeMulVecBilinEquivRangeVecMulLinear.symm)⟩⟩

end Module.Finite
