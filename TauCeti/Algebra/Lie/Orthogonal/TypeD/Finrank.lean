/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.LinearAlgebra.Matrix.Alternating

/-!
# The dimension of the split even orthogonal Lie algebra

Mathlib's split type-`D` Lie algebra `LieAlgebra.Orthogonal.typeD ι K` consists of the matrices
that are skew-adjoint for the symmetric form `JD ι K = [[0, 1], [1, 0]]`. Since `JD ι K` squares
to the identity, left multiplication by it identifies these matrices with the skew-symmetric
matrices on `ι ⊕ ι`. When `2 ≠ 0`, a skew-symmetric matrix is determined by its entries above the
diagonal, and these are arbitrary.

## Main results

* `TauCeti.LieAlgebra.Orthogonal.finrank_typeD`: over a field with `2 ≠ 0`, the split type-`D`
  Lie algebra on `2n` coordinates has dimension `(2n).choose 2 = n(2n - 1)`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 18.
-/

public section

open Matrix LieAlgebra.Orthogonal

namespace TauCeti.LieAlgebra.Orthogonal

variable (ι K : Type*) [Fintype ι] [DecidableEq ι] [Field K]

/-- The split type-`D` Lie algebra on `2n` coordinates has dimension `(2n).choose 2 = n(2n - 1)`
over every field in which `2 ≠ 0`. -/
theorem finrank_typeD [NeZero (2 : K)] :
    Module.finrank K (typeD ι K) = (2 * Fintype.card ι).choose 2 := by
  let _ : LinearOrder (ι ⊕ ι) := LinearOrder.lift' _ (Fintype.equivFin (ι ⊕ ι)).injective
  have h2 := (NeZero.ne (2 : K)).isUnit.eq_zero_of_add_self_eq_zero
  have hJt : (JD ι K)ᵀ = JD ι K := by simp [JD, fromBlocks_transpose]
  have hJJ : JD ι K * JD ι K = 1 := by simp [JD, fromBlocks_multiply, fromBlocks_one]
  have hmem (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) : X ∈ typeD ι K ↔ Xᵀ * JD ι K = JD ι K * -X := by
    simp only [typeD, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule,
      Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  -- Left multiplication by `JD` sends `typeD` to the skew-symmetric matrices.
  have hskew (X : typeD ι K) :
      (JD ι K * (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K))ᵀ = -(JD ι K * (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K)) := by
    rw [transpose_mul, hJt, (hmem X).mp X.property, Matrix.mul_neg]
  let f : typeD ι K →ₗ[K] ({p : (ι ⊕ ι) × (ι ⊕ ι) // p.1 < p.2} → K) :=
    { toFun X p := (JD ι K * (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K)) p.val.1 p.val.2
      map_add' X Y := by ext; simp [Matrix.mul_add]
      map_smul' a X := by ext; simp }
  have hf : Function.Bijective f := by
    refine ⟨fun X Y hXY ↦ Subtype.ext ?_, fun c ↦ ?_⟩
    · have h := ext_of_lt_of_transpose_eq_neg (hskew X) (hskew Y)
        (diag_eq_zero_of_transpose_eq_neg (hskew X) h2)
        (diag_eq_zero_of_transpose_eq_neg (hskew Y) h2) fun a b hab ↦ congrFun hXY ⟨(a, b), hab⟩
      simpa [← Matrix.mul_assoc, hJJ] using congrArg (JD ι K * ·) h
    · refine ⟨⟨JD ι K * ofStrictUpper c, ?_⟩, funext fun p ↦ ?_⟩
      · rw [hmem, transpose_mul, hJt, Matrix.mul_assoc, hJJ, Matrix.mul_one, Matrix.mul_neg,
          ← Matrix.mul_assoc, hJJ, Matrix.one_mul, transpose_ofStrictUpper]
      · simp [f, ← Matrix.mul_assoc, hJJ]
  rw [(LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_sum, two_mul]

end TauCeti.LieAlgebra.Orthogonal
