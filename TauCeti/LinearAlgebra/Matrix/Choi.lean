/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Choi matrices

The Choi matrix uses `Matrix.comp` to flatten the block matrix of images of the
input matrix units. Its indices agree with the column stacking of `Matrix.vec`,
with the input index first. Choi matrices respect pointwise zero, addition, finite sums
and scalar multiplication. They determine linear maps with finite input index types and
arbitrary output index types.
`choiMatrixAddEquiv` reconstructs such a linear map from the blocks of its Choi matrix.

For a map `X ↦ A * X * B`, the Choi matrix is the outer product of `A.vec`
and `(Bᵀ).vec`. For a Kraus summand, the second factor is the entrywise conjugate
of the first. This identity relates Kraus decompositions to decompositions of
positive semidefinite Choi matrices into outer products.

## References

* M.-D. Choi, *Completely positive linear maps on complex matrices*, Linear Algebra and
  its Applications 10 (1975), 285–290, proof of Theorem 1 (p. 286), used to state Theorem 2.
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

/-- The Choi matrix of the pointwise zero map is zero. -/
@[simp]
theorem choiMatrix_zero {m n R : Type*} [DecidableEq n] [Zero R] [One R] :
    choiMatrix (0 : Matrix n n R → Matrix m m R) = 0 := by
  ext p q
  simp only [choiMatrix_apply, Pi.zero_apply, Matrix.zero_apply]

/-- The Choi matrix of the zero linear map is zero. -/
@[simp]
theorem choiMatrix_zero_linearMap {m n R : Type*} [DecidableEq n] [Semiring R] :
    choiMatrix (0 : Matrix n n R →ₗ[R] Matrix m m R) = 0 := by
  rw [(LinearMap.coe_zero_iff _).2 rfl, choiMatrix_zero]

/-- Forming a Choi matrix commutes with pointwise addition of matrix-valued maps. -/
@[simp]
theorem choiMatrix_add {m n R : Type*} [DecidableEq n] [Zero R] [One R] [Add R]
    (Φ Ψ : Matrix n n R → Matrix m m R) :
    choiMatrix (Φ + Ψ) = choiMatrix Φ + choiMatrix Ψ := by
  ext p q
  simp only [choiMatrix_apply, Pi.add_apply, Matrix.add_apply]

/-- Forming a Choi matrix commutes with finite pointwise sums of matrix-valued maps. -/
@[simp]
theorem choiMatrix_sum {ι m n R : Type*} [DecidableEq n] [AddCommMonoid R] [One R]
    (s : Finset ι) (Φ : ι → Matrix n n R → Matrix m m R) :
    choiMatrix (∑ i ∈ s, Φ i) = ∑ i ∈ s, choiMatrix (Φ i) := by
  ext p q
  simp only [choiMatrix_apply, Finset.sum_apply, Matrix.sum_apply]

/-- Forming a Choi matrix commutes with pointwise scaling of a matrix-valued map. -/
@[simp]
theorem choiMatrix_smul {S m n R : Type*} [DecidableEq n] [Zero R] [One R] [SMul S R]
    (c : S) (Φ : Matrix n n R → Matrix m m R) :
    choiMatrix (c • Φ) = c • choiMatrix Φ := by
  ext p q
  simp only [choiMatrix_apply, Pi.smul_apply, Matrix.smul_apply]

/-- The additive equivalence sending a linear map with a finite input index type to its
Choi matrix. The output index type is arbitrary. The inverse reconstructs the linear map
that sends each matrix unit to the corresponding block. -/
noncomputable def choiMatrixAddEquiv {m n R : Type*} [Finite n] [Semiring R] :
    (Matrix n n R →ₗ[R] Matrix m m R) ≃+ Matrix (n × m) (n × m) R :=
  let := Fintype.ofFinite n
  ((Matrix.stdBasis R n n).constr ℕ).symm.toAddEquiv.trans <|
    (AddEquiv.curry n n (Matrix m m R)).trans <|
      Matrix.ofAddEquiv.trans (Matrix.compAddEquiv n n m m R)

/-- The forward direction of `choiMatrixAddEquiv` forms the Choi matrix. -/
@[simp]
theorem _root_.LinearMap.choiMatrixAddEquiv_apply {m n R : Type*} [Finite n] [DecidableEq n]
    [Semiring R] (Φ : Matrix n n R →ₗ[R] Matrix m m R) :
    choiMatrixAddEquiv Φ = choiMatrix Φ := by
  let := Fintype.ofFinite n
  apply Matrix.ext
  rintro ⟨i, a⟩ ⟨j, b⟩
  simp [choiMatrixAddEquiv, Function.curry, Matrix.stdBasis_eq_single]

/-- The Choi matrix of the linear map reconstructed from `C` is `C`. -/
@[simp]
theorem _root_.Matrix.choiMatrix_choiMatrixAddEquiv_symm {m n R : Type*} [Finite n] [DecidableEq n]
    [Semiring R] (C : Matrix (n × m) (n × m) R) :
    choiMatrix (choiMatrixAddEquiv.symm C) = C := by
  simpa only [LinearMap.choiMatrixAddEquiv_apply] using choiMatrixAddEquiv.apply_symm_apply C

/-- Reconstructing a linear map from its Choi matrix recovers the original map. -/
@[simp]
theorem _root_.LinearMap.choiMatrixAddEquiv_symm_choiMatrix {m n R : Type*} [Finite n]
    [DecidableEq n] [Semiring R] (Φ : Matrix n n R →ₗ[R] Matrix m m R) :
    choiMatrixAddEquiv.symm (choiMatrix Φ) = Φ := by
  simpa only [LinearMap.choiMatrixAddEquiv_apply] using choiMatrixAddEquiv.symm_apply_apply Φ

/-- A linear map with a finite input index type is determined by its Choi matrix.
The output index type is arbitrary. -/
theorem choiMatrix_injective {m n R : Type*} [Finite n] [DecidableEq n] [Semiring R] :
    Function.Injective (fun Φ : Matrix n n R →ₗ[R] Matrix m m R => choiMatrix Φ) := by
  intro Φ Ψ h
  apply choiMatrixAddEquiv.injective
  simpa only [LinearMap.choiMatrixAddEquiv_apply] using h

/-- Two linear maps with finite input index type have equal Choi matrices exactly when
the maps are equal. -/
@[simp]
theorem choiMatrix_inj {m n R : Type*} [Finite n] [DecidableEq n] [Semiring R]
    {Φ Ψ : Matrix n n R →ₗ[R] Matrix m m R} :
    choiMatrix Φ = choiMatrix Ψ ↔ Φ = Ψ :=
  choiMatrix_injective.eq_iff

/-- The reconstructed linear map sends the `(i, j)` matrix unit to the `(i, j)` block. -/
@[simp]
theorem _root_.Matrix.choiMatrixAddEquiv_symm_apply_single {m n R : Type*} [Finite n]
    [DecidableEq n] [Semiring R] (C : Matrix (n × m) (n × m) R) (i j : n) :
    choiMatrixAddEquiv.symm C (Matrix.single i j 1) =
      C.submatrix (fun a => (i, a)) (fun b => (j, b)) := by
  ext a b
  simpa only [LinearMap.choiMatrixAddEquiv_apply, choiMatrix_apply, Matrix.submatrix_apply] using
    congrArg (fun M : Matrix (n × m) (n × m) R => M (i, a) (j, b))
      (choiMatrixAddEquiv.apply_symm_apply C)

end TauCeti

namespace Matrix

-- The proof needs the zero of the sums and the zero absorbed by multiplication to be the same
-- element.
/-- The Choi matrix of `X ↦ A * X * B` is the outer product of `A.vec` and `(Bᵀ).vec`. -/
theorem choiMatrix_mul_mul {m n R : Type*} [Fintype n] [DecidableEq n]
    [NonAssocSemiring R] (A : Matrix m n R) (B : Matrix n m R) :
    TauCeti.choiMatrix (fun X : Matrix n n R => A * X * B) =
      Matrix.vecMulVec A.vec (Bᵀ).vec := by
  apply Matrix.ext
  rintro ⟨i, a⟩ ⟨j, b⟩
  have hrow : (A * Matrix.single i j (1 : R)) a = Pi.single j (A a i) := by
    rw [Matrix.mul_single_eq_updateCol_zero]
    ext k
    simp [Matrix.updateCol_apply, Pi.single_apply]
  rw [TauCeti.choiMatrix_apply, Matrix.mul_apply']
  simp only [hrow, single_dotProduct, Matrix.vecMulVec_apply, Matrix.vec, Matrix.transpose_apply]

/-- The Choi matrix of `X ↦ K * X * Kᴴ` is the outer product of the vectorized operator
with its entrywise conjugate. -/
theorem choiMatrix_mul_mul_conjTranspose {m n R : Type*} [Fintype n] [DecidableEq n]
    [NonAssocSemiring R] [Star R] (K : Matrix m n R) :
    TauCeti.choiMatrix (fun X : Matrix n n R => K * X * Kᴴ) =
      Matrix.vecMulVec K.vec (star K.vec) := by
  rw [K.choiMatrix_mul_mul Kᴴ, Matrix.conjTranspose_transpose, Matrix.star_vec]

end Matrix
