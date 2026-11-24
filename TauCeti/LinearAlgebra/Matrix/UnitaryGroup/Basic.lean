/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.UnitaryGroup
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Coordinate action and diagonal stabilizers of unitary matrices

`Matrix.UnitaryGroup.toLinearEquiv_apply` describes the linear equivalence associated to a unitary
matrix by its matrix-vector action, and `Matrix.permMatrix_mem_unitary` records that
permutation matrices over a possibly noncommutative star semiring are unitary. Accordingly
`Matrix.permutationUnitary` is `Matrix.permMatrixHom` with values in the unitary matrices.

`Matrix.mem_unitary_iff_conjTranspose` characterizes `unitary (Matrix n n R)` via the conjugate
transpose over any star semiring, and `Matrix.conjTranspose_mul_mul_mem_unitary` transfers
unitarity along a possibly rectangular matrix whose conjugate transpose is a two-sided inverse.

`Matrix.diagonal_update_one_mem_unitary_iff` says that a diagonal matrix with all diagonal entries
`1` except one is unitary exactly when that entry is. Multiplying one column `j` of a unitary
matrix `A` by `star (det A)` therefore keeps it unitary and makes its determinant
`det A * star (det A) = 1`: this is `Matrix.UnitaryGroup.toSpecialUnitaryAt j A`, a special unitary
matrix with the same columns as `A` away from `j`
(`Matrix.UnitaryGroup.toSpecialUnitaryAt_mulVec_single`).

`Matrix.star_mulVec_dotProduct_mulVec_of_mem_unitaryGroup` says that a unitary matrix preserves
the Hermitian dot product `star x ⬝ᵥ y`.

For a diagonal with distinct entries, two unitary frames give the same conjugate exactly
when their relative frame is diagonal. This is the sign ambiguity for orthogonal frames
and the phase ambiguity for complex unitary frames in Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), §4.1.
-/

public section

universe u v

namespace Matrix.UnitaryGroup

variable {R : Type u} [CommRing R] [StarRing R]
variable {n : Type v} [Fintype n] [DecidableEq n]

/-- The linear equivalence associated to a unitary matrix acts by matrix-vector
multiplication. -/
@[simp]
theorem toLinearEquiv_apply (U : Matrix.unitaryGroup n R) (x : n → R) :
    Matrix.UnitaryGroup.toLinearEquiv U x = Matrix.toLin' (U : Matrix n n R) x := rfl

end Matrix.UnitaryGroup

namespace Matrix

/-- Over any star semiring, a square matrix belongs to `unitary (Matrix n n R)` if and only if its
conjugate transpose is a two-sided inverse. -/
theorem mem_unitary_iff_conjTranspose {R n : Type*} [Semiring R] [StarRing R]
    [Fintype n] [DecidableEq n] {U : Matrix n n R} :
    U ∈ unitary (Matrix n n R) ↔ Uᴴ * U = 1 ∧ U * Uᴴ = 1 := by
  rw [Unitary.mem_iff, star_eq_conjTranspose]

/-- Conjugation by a possibly rectangular matrix with conjugate-transpose inverse preserves
unitarity over a possibly noncommutative star semiring. -/
theorem conjTranspose_mul_mul_mem_unitary
    {R m n : Type*} [Semiring R] [StarRing R]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : Matrix m n R) (hP : Pᴴ * P = 1) (hP' : P * Pᴴ = 1)
    {X : Matrix m m R} (hX : X ∈ unitary (Matrix m m R)) :
    Pᴴ * X * P ∈ unitary (Matrix n n R) := by
  have hcancel (Y Z : Matrix m m R) :
      (Pᴴ * Y * P) * (Pᴴ * Z * P) = Pᴴ * (Y * Z) * P := by
    calc
      _ = Pᴴ * (Y * (P * Pᴴ) * Z) * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP', Matrix.mul_one]
  rw [mem_unitary_iff_conjTranspose] at hX ⊢
  constructor <;>
    simp only [conjTranspose_mul, conjTranspose_conjTranspose,
      ← Matrix.mul_assoc Pᴴ Xᴴ P, hcancel, hX.1, hX.2, Matrix.mul_one, hP]

/-- A diagonal matrix whose diagonal entries are all `1` except the `i`-th one is unitary exactly
when its `i`-th diagonal entry is unitary. -/
theorem diagonal_update_one_mem_unitary_iff {n α : Type*} [Fintype n] [DecidableEq n]
    [Semiring α] [StarRing α] {a : α} {i : n} :
    diagonal (Function.update (1 : n → α) i a) ∈ unitary (Matrix n n α) ↔ a ∈ unitary α := by
  simp [Pi.mem_unitary_iff, Function.forall_update_iff]

/-- A unitary matrix preserves the Hermitian dot product. -/
theorem star_mulVec_dotProduct_mulVec_of_mem_unitaryGroup {n α : Type*} [Fintype n]
    [DecidableEq n] [CommRing α] [StarRing α] {A : Matrix n n α} (hA : A ∈ unitaryGroup n α)
    (x y : n → α) : star (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = star x ⬝ᵥ y := by
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose,
    (mem_unitaryGroup_iff' (A := A)).mp hA, vecMul_one]

namespace UnitaryGroup

variable {R : Type u} [CommRing R] [StarRing R]
variable {n : Type v} [Fintype n] [DecidableEq n]

/-- The unitary matrix `A` with its column `j` multiplied by `star (det A)`. It is unitary, and its
determinant is `det A * star (det A) = 1` since `det A` is a unitary scalar, so it is special
unitary. Its columns other than `j` are those of `A`
(`Matrix.UnitaryGroup.toSpecialUnitaryAt_mulVec_single`). -/
def toSpecialUnitaryAt (j : n) (A : unitaryGroup n R) : specialUnitaryGroup n R :=
  ⟨A.val * diagonal (Function.update 1 j (star (A : Matrix n n R).det)),
    mem_specialUnitaryGroup_iff.2 ⟨mul_mem A.property
      (diagonal_update_one_mem_unitary_iff.2 (Unitary.star_mem (det_of_mem_unitary A.property))), by
        rw [det_mul, det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ j)]
        simpa using (det_of_mem_unitary A.property).2⟩⟩

theorem coe_toSpecialUnitaryAt (j : n) (A : unitaryGroup n R) :
    (toSpecialUnitaryAt j A : Matrix n n R) =
      A.val * diagonal (Function.update 1 j (star (A : Matrix n n R).det)) :=
  (rfl)

/-- Away from the column `j`, the columns of `toSpecialUnitaryAt j A` are those of `A`. -/
theorem toSpecialUnitaryAt_mulVec_single {j k : n} (hk : k ≠ j) (A : unitaryGroup n R) :
    (toSpecialUnitaryAt j A : Matrix n n R) *ᵥ Pi.single k 1 = A.val *ᵥ Pi.single k 1 := by
  rw [coe_toSpecialUnitaryAt, ← mulVec_mulVec, diagonal_mulVec_single,
    Function.update_of_ne hk, Pi.one_apply, one_mul]

/-- A special unitary matrix is its own correction. -/
@[simp]
theorem toSpecialUnitaryAt_of_det_eq_one (j : n) {A : unitaryGroup n R}
    (hA : (A : Matrix n n R).det = 1) : (toSpecialUnitaryAt j A : Matrix n n R) = A := by
  simp [coe_toSpecialUnitaryAt, hA]

end UnitaryGroup

variable {R : Type u} [Semiring R] [StarRing R]
variable {n : Type v} [Fintype n] [DecidableEq n]

/-- A permutation matrix is unitary: its conjugate transpose is the permutation matrix of the
inverse permutation. -/
@[simp]
theorem permMatrix_mem_unitary (σ : Equiv.Perm n) :
    σ.permMatrix R ∈ unitary (Matrix n n R) := by
  simp [Unitary.mem_iff, star_eq_conjTranspose, ← permMatrix_mul]

/-- A permutation as a unitary matrix: `permutationUnitary σ` is the permutation matrix of `σ⁻¹`,
which makes this a homomorphism with Mathlib's convention for multiplication in `Equiv.Perm`. -/
def permutationUnitary : Equiv.Perm n →* unitary (Matrix n n R) :=
  (permMatrixHom (R := R)).codRestrict _ fun σ => by
    rw [permMatrixHom_apply]
    exact permMatrix_mem_unitary σ⁻¹

/-- The matrix underlying `permutationUnitary σ` is the permutation matrix of `σ⁻¹`. -/
@[simp]
theorem coe_permutationUnitary (σ : Equiv.Perm n) :
    (permutationUnitary (R := R) σ : Matrix n n R) = σ⁻¹.permMatrix R :=
  (rfl)

section DiagonalStabilizer

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]
  [CommSemiring R] [IsLeftCancelMulZero R] [StarRing R]

/-- A diagonal with distinct entries has exactly the diagonal unitary frames in its stabilizer. -/
theorem conjStarAlgAut_diagonal_eq_iff {d : ι → R} (hd : Function.Injective d)
    (U : unitary (Matrix ι ι R)) :
    Unitary.conjStarAlgAut ℕ _ U (diagonal d) = diagonal d ↔ Matrix.IsDiag (U : Matrix ι ι R) := by
  rw [Unitary.conjStarAlgAut_apply]
  constructor
  · intro h
    apply TauCeti.isDiag_of_commute_diagonal hd
    calc
      diagonal d * (U : Matrix ι ι R) = (U * diagonal d * (star U : Matrix ι ι R)) * U := by rw [h]
      _ = U * diagonal d := by simp [Matrix.mul_assoc]
  · intro h
    have hcomm : Commute (U : Matrix ι ι R) (diagonal d) := by
      rw [← h.diagonal_diag]
      exact Matrix.commute_diagonal _ _
    rw [hcomm.eq]
    simp [Matrix.mul_assoc]

/-- Two frames give the same conjugate of a simple diagonal exactly when they differ
by a right diagonal unitary. -/
theorem conjStarAlgAut_diagonal_eq_conjStarAlgAut_iff {d : ι → R} (hd : Function.Injective d)
    (U V : unitary (Matrix ι ι R)) :
    Unitary.conjStarAlgAut ℕ _ U (diagonal d) = Unitary.conjStarAlgAut ℕ _ V (diagonal d) ↔
      Matrix.IsDiag ((star V * U : unitary (Matrix ι ι R)) : Matrix ι ι R) := by
  rw [← conjStarAlgAut_diagonal_eq_iff hd, Unitary.conjStarAlgAut_mul_apply]
  have hV : Unitary.conjStarAlgAut ℕ (Matrix ι ι R) (star V)
      (Unitary.conjStarAlgAut ℕ _ V (diagonal d)) = diagonal d := by
    rw [← Unitary.conjStarAlgAut_mul_apply]
    simp
  conv_rhs => rhs; rw [← hV]
  exact (Unitary.conjStarAlgAut ℕ (Matrix ι ι R) (star V)).injective.eq_iff.symm

end DiagonalStabilizer

end Matrix
