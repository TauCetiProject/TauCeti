/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Choi matrices

The Choi matrix uses `Matrix.comp` to flatten the block matrix of images of the
input matrix units. Its indices agree with the column stacking of `Matrix.vec`,
with the input index first. For a single Kraus summand, it is the outer product
of the vectorized operator with its entrywise conjugate. This identity relates
Kraus decompositions to decompositions of positive semidefinite Choi matrices
into outer products.

## References

* M.-D. Choi, *Completely positive linear maps on complex matrices*, Linear Algebra and
  its Applications 10 (1975), 285–290, proof of Theorem 1 and Theorem 2.
-/

public section

open scoped Matrix

namespace TauCeti

/-- The Choi matrix of a map on matrices, with input-output coordinate order. -/
def choiMatrix {m n R : Type*} [DecidableEq n] [Zero R] [One R]
    (Φ : Matrix n n R → Matrix m m R) : Matrix (n × m) (n × m) R :=
  Matrix.comp _ _ _ _ _ (Matrix.of fun i j => Φ (Matrix.single i j 1))

/-- An entry of the Choi matrix is the corresponding image of a matrix unit. -/
@[simp]
theorem choiMatrix_apply {m n R : Type*} [DecidableEq n] [Zero R] [One R]
    (Φ : Matrix n n R → Matrix m m R) (p q : n × m) :
    choiMatrix Φ p q = Φ (Matrix.single p.fst q.fst 1) p.snd q.snd := (rfl)

/-- The Choi matrix of `X ↦ K * X * Kᴴ` is the outer product of the vectorized operator
with its entrywise conjugate. -/
theorem choiMatrix_mul_mul_conjTranspose {m n R : Type*} [Fintype n] [DecidableEq n]
    [NonAssocSemiring R] [Star R] (K : Matrix m n R) :
    choiMatrix (fun X : Matrix n n R => K * X * Kᴴ) =
      Matrix.vecMulVec K.vec (star K.vec) := by
  ext p q
  simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, ite_mul]

end TauCeti
