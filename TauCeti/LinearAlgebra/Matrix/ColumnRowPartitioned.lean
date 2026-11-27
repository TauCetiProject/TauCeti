/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# Linear independence of rows in partitioned matrices, and standard frames

This file proves that the rows of a column-partitioned matrix `[A | B]` are linearly independent
as soon as the rows of one of its blocks are: two distinct combinations of the rows already
differ on the columns of that block, so no nontrivial combination of the rows vanishes.

The main instance is a block that is an identity matrix, whose rows are linearly independent by
`Matrix.linearIndependent_row_one`. Consequently a matrix in systematic form has full row rank,
which is what turns a row count into a dimension: over a field, `[I | A]` has as many rows as the
dimension of the code it generates, and `[B | I]` has as many rows as the codimension of the code
it checks.

Sums of partitioned matrices are computed blockwise (`Matrix.fromCols_add`,
`Matrix.fromRows_add`), as for `Matrix.fromBlocks_add`.

It also identifies the row-partitioned matrix `(0; 1)`, reindexed along an equivalence
`e : ι ≃ n₁ ⊕ n₂`, with the frame of the standard basis columns `e⁻¹ (inr j)` of `ι`.

Over a field, `A.mulVec` is surjective exactly when the rows of `A` are linearly independent
(`Matrix.mulVec_surjective_iff_linearIndependent_row`). Stacking one more row `r` under a matrix
`A` of full row rank therefore keeps the row rank full exactly when `r` is not a combination
`c ᵥ* A` of the rows of `A`. For a Jacobian matrix this is the transversality test for a
hyperplane section: the hyperplane `ℓ = 0` is transverse to the zero set exactly where `ℓ` is not
a combination of the gradients of the equations.

## Main declarations

* `Matrix.linearIndependent_row_fromCols_of_left`,
  `Matrix.linearIndependent_row_fromCols_of_right`: the rows of `[A | B]` are linearly
  independent when those of `A`, respectively `B`, are.
* `Matrix.linearIndependent_row_one_fromCols`: the rows of `[I | A]` are linearly independent.
* `Matrix.linearIndependent_row_fromCols_one`: the rows of `[B | I]` are linearly
  independent.
* `Matrix.fromCols_add` and `Matrix.fromRows_add`: sums of partitioned matrices are blockwise.
* `Matrix.fromRows_zero_one_submatrix_equiv`: reindexed along `e : ι ≃ n₁ ⊕ n₂`, the matrix
  `(0; 1)` is the frame of the standard basis columns `e⁻¹ (inr j)`.
* `Matrix.mulVec_surjective_fromRows_replicateRow_iff`: if `A` has full row rank, the matrix
  `(A; r)` has full row rank exactly when `r` is not of the form `c ᵥ* A`.
-/

public section

namespace Matrix

section Add

variable {R m m₁ m₂ n n₁ n₂ : Type*} [Add R]

@[simp]
theorem fromCols_add (A₁ B₁ : Matrix m n₁ R) (A₂ B₂ : Matrix m n₂ R) :
    fromCols A₁ A₂ + fromCols B₁ B₂ = fromCols (A₁ + B₁) (A₂ + B₂) := by
  ext i (j | j) <;> rfl

@[simp]
theorem fromRows_add (A₁ B₁ : Matrix m₁ n R) (A₂ B₂ : Matrix m₂ n R) :
    fromRows A₁ A₂ + fromRows B₁ B₂ = fromRows (A₁ + B₁) (A₂ + B₂) := by
  ext (i | i) j <;> rfl

end Add

variable {R m n₁ n₂ : Type*} [Semiring R]

/-- If the rows of the left block `A` are linearly independent, so are the rows of `[A | B]`. -/
theorem linearIndependent_row_fromCols_of_left {A : Matrix m n₁ R}
    (hA : LinearIndependent R A.row) (B : Matrix m n₂ R) :
    LinearIndependent R (fromCols A B).row :=
  .of_comp (LinearMap.funLeft R R Sum.inl) <| by convert hA using 1; ext; simp

/-- If the rows of the right block `B` are linearly independent, so are the rows of `[A | B]`. -/
theorem linearIndependent_row_fromCols_of_right {B : Matrix m n₂ R}
    (hB : LinearIndependent R B.row) (A : Matrix m n₁ R) :
    LinearIndependent R (fromCols A B).row :=
  .of_comp (LinearMap.funLeft R R Sum.inr) <| by convert hB using 1; ext; simp

/-- The rows of a systematic matrix `[I | A]` are linearly independent. -/
theorem linearIndependent_row_one_fromCols [DecidableEq m] (A : Matrix m n₂ R) :
    LinearIndependent R (fromCols (1 : Matrix m m R) A).row :=
  linearIndependent_row_fromCols_of_left linearIndependent_row_one A

/-- The rows of a systematic matrix `[B | I]` are linearly independent. -/
theorem linearIndependent_row_fromCols_one [DecidableEq m] (B : Matrix m n₁ R) :
    LinearIndependent R (fromCols B (1 : Matrix m m R)).row :=
  linearIndependent_row_fromCols_of_right linearIndependent_row_one B

/-- Reindexed along an equivalence `e : ι ≃ n₁ ⊕ n₂`, the matrix `(0; 1)` is the frame of the
standard basis columns `e⁻¹ (inr j)`, `j : n₂`. -/
theorem fromRows_zero_one_submatrix_equiv {R ι n₁ n₂ : Type*} [Zero R] [One R] [DecidableEq ι]
    [DecidableEq n₂] (e : ι ≃ n₁ ⊕ n₂) :
    (fromRows (0 : Matrix n₁ n₂ R) (1 : Matrix n₂ n₂ R)).submatrix e id =
      (1 : Matrix ι ι R).submatrix id (e.symm ∘ Sum.inr) := by
  ext i j
  obtain ⟨i, rfl⟩ := e.symm.surjective i
  rcases i with i | i <;> simp [Matrix.one_apply, Function.comp_def, id_eq]

section Field

variable {K m n : Type*} [Field K] [Fintype n]

/-- Stacking a row `r` under a matrix `A` whose `mulVec` is surjective keeps `mulVec` surjective
exactly when `r` is not a linear combination `c ᵥ* A` of the rows of `A`. -/
theorem mulVec_surjective_fromRows_replicateRow_iff [Fintype m] {A : Matrix m n K}
    (hA : A.mulVec.Surjective) (r : n → K) :
    (A.fromRows (replicateRow Unit r)).mulVec.Surjective ↔ r ∉ Set.range (· ᵥ* A) := by
  rw [mulVec_surjective_iff_linearIndependent_row] at hA ⊢
  have hrow : (A.fromRows (replicateRow Unit r)).row = Sum.elim A.row fun _ ↦ r := by
    ext (i | i) j <;> simp
  rw [hrow, linearIndependent_sum]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Set.range_const, hA, true_and,
    linearIndependent_unique_iff (v := fun _ : Unit ↦ r)]
  have hspan : (Set.range fun c : m → K ↦ c ᵥ* A) = Submodule.span K (Set.range A.row) := by
    rw [← range_vecMulLinear, LinearMap.coe_range, coe_vecMulLinear]
  rw [hspan, SetLike.mem_coe, Submodule.disjoint_span_singleton]
  exact ⟨fun ⟨hr, h⟩ hmem ↦ hr (h hmem), fun h ↦ ⟨fun hr ↦ h (hr ▸ zero_mem _),
    fun hmem ↦ (h hmem).elim⟩⟩

end Field

end Matrix
