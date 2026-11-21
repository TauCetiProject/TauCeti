/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Choi matrices

The Choi matrix uses `Matrix.comp` to flatten the block matrix of images of the
input matrix units. Its indices agree with the column stacking of `Matrix.vec`,
with the input index first. Choi matrices respect pointwise finite sums and
determine linear maps on finite matrices.

For a map `X ↦ A * X * B`, the Choi matrix is the outer product of `A.vec`
and `(Bᵀ).vec`. For a Kraus summand, the second factor is the entrywise conjugate
of the first. This identity relates Kraus decompositions to decompositions of
positive semidefinite Choi matrices into outer products.

## References

* M.-D. Choi, *Completely positive linear maps on complex matrices*, Linear Algebra and
  its Applications 10 (1975), 285–290, proof of Theorem 1 and Theorem 2.
-/

public section

open scoped BigOperators Matrix

namespace TauCeti

/-- The Choi matrix of a map on matrices, with input-output coordinate order. -/
def choiMatrix {m n R : Type*} [DecidableEq n] [Zero R] [One R]
    (Φ : Matrix n n R → Matrix m m R) : Matrix (n × m) (n × m) R :=
  Matrix.comp _ _ _ _ _ (Matrix.of fun i j => Φ (Matrix.single i j 1))

/-- The Choi matrix flattens the block matrix of images of the input matrix units. -/
theorem choiMatrix_def {m n R : Type*} [DecidableEq n] [Zero R] [One R]
    (Φ : Matrix n n R → Matrix m m R) :
    choiMatrix Φ = Matrix.comp n n m m R (Matrix.of fun i j => Φ (Matrix.single i j 1)) := by
  simp only [choiMatrix]

/-- The first coordinates select an input matrix unit, and the second coordinates select an
entry of its image under `Φ`. -/
@[simp]
theorem choiMatrix_apply {m n R : Type*} [DecidableEq n] [Zero R] [One R]
    (Φ : Matrix n n R → Matrix m m R) (p q : n × m) :
    choiMatrix Φ p q = Φ (Matrix.single p.fst q.fst 1) p.snd q.snd := by
  simp only [choiMatrix, Matrix.comp_apply, Matrix.of_apply]

/-- Forming a Choi matrix commutes with finite pointwise sums of matrix-valued maps. -/
theorem choiMatrix_sum {ι m n R : Type*} [DecidableEq n] [AddCommMonoid R] [One R]
    (s : Finset ι) (Φ : ι → Matrix n n R → Matrix m m R) :
    choiMatrix (fun X => ∑ i ∈ s, Φ i X) = ∑ i ∈ s, choiMatrix (Φ i) := by
  ext p q
  simp only [choiMatrix_apply, Matrix.sum_apply]

/-- A linear map on finite matrices is determined by its Choi matrix. -/
theorem choiMatrix_injective {m n R : Type*} [Finite n] [DecidableEq n] [Semiring R] :
    Function.Injective (fun Φ : Matrix n n R →ₗ[R] Matrix m m R => choiMatrix Φ) := by
  let := Fintype.ofFinite n
  intro Φ Ψ h
  apply (Matrix.stdBasis R n n).ext
  rintro ⟨i, j⟩
  rw [Matrix.stdBasis_eq_single]
  ext a b
  simpa only [choiMatrix_apply] using congrFun (congrFun h (i, a)) (j, b)

-- The proof needs the zero of the sums and the zero absorbed by multiplication to be the same
-- element.
/-- The Choi matrix of `X ↦ A * X * B` is the outer product of `A.vec` and `(Bᵀ).vec`. -/
theorem choiMatrix_mul_mul {m n R : Type*} [Fintype n] [DecidableEq n]
    [NonAssocSemiring R] (A : Matrix m n R) (B : Matrix n m R) :
    choiMatrix (fun X : Matrix n n R => A * X * B) =
      Matrix.vecMulVec A.vec (Bᵀ).vec := by
  apply Matrix.ext
  rintro ⟨i, a⟩ ⟨j, b⟩
  have hrow : (A * Matrix.single i j (1 : R)) a = Pi.single j (A a i) := by
    rw [Matrix.mul_single_eq_updateCol_zero]
    ext k
    simp [Matrix.updateCol_apply, Pi.single_apply]
  rw [choiMatrix_apply, Matrix.mul_apply']
  simp only [hrow, single_dotProduct, Matrix.vecMulVec_apply, Matrix.vec, Matrix.transpose_apply]

end TauCeti

namespace Matrix

/-- The Choi matrix of `X ↦ K * X * Kᴴ` is the outer product of the vectorized operator
with its entrywise conjugate. -/
theorem choiMatrix_mul_mul_conjTranspose {m n R : Type*} [Fintype n] [DecidableEq n]
    [NonAssocSemiring R] [Star R] (K : Matrix m n R) :
    TauCeti.choiMatrix (fun X : Matrix n n R => K * X * Kᴴ) =
      Matrix.vecMulVec K.vec (star K.vec) := by
  rw [TauCeti.choiMatrix_mul_mul, Matrix.conjTranspose_transpose, Matrix.star_vec]

end Matrix
