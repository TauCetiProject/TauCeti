/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Coordinate action of unitary matrices

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

/-- Reindexing unitary matrices along a bijection `e : n ≃ m`, as a group isomorphism
`Matrix.unitaryGroup n R ≃* Matrix.unitaryGroup m R`. -/
def reindexEquiv {m : Type*} [Fintype m] [DecidableEq m] (e : n ≃ m) :
    unitaryGroup n R ≃* unitaryGroup m R where
  toFun U := ⟨reindex e e (U : Matrix n n R), submatrix_equiv_mem_unitary.2 U.property⟩
  invFun V := ⟨reindex e.symm e.symm (V : Matrix m m R),
    submatrix_equiv_mem_unitary.2 V.property⟩
  left_inv U := Subtype.ext (by simp [reindex_apply])
  right_inv V := Subtype.ext (by simp [reindex_apply])
  map_mul' U V := Subtype.ext (by
    simp only [Submonoid.coe_mul, reindex_apply, submatrix_mul_equiv])

/-- The matrix underlying `reindexEquiv e U` is `Matrix.reindex e e U`. -/
@[simp]
theorem coe_reindexEquiv {m : Type*} [Fintype m] [DecidableEq m] (e : n ≃ m)
    (U : unitaryGroup n R) :
    (reindexEquiv e U : Matrix m m R) = reindex e e (U : Matrix n n R) :=
  (rfl)

/-- The matrix underlying `(reindexEquiv e).symm V` is `Matrix.reindex e.symm e.symm V`. -/
@[simp]
theorem coe_reindexEquiv_symm {m : Type*} [Fintype m] [DecidableEq m] (e : n ≃ m)
    (V : unitaryGroup m R) :
    ((reindexEquiv e).symm V : Matrix n n R) = reindex e.symm e.symm (V : Matrix m m R) :=
  (rfl)

end UnitaryGroup

section SpecialUnitary

variable (n : Type*) (R : Type*) [Fintype n] [DecidableEq n] [CommRing R] [StarRing R]

/-- The special unitary group `SU(n)` as a subgroup of `Matrix.unitaryGroup n R`. -/
def UnitaryGroup.specialUnitarySubgroup : Subgroup (unitaryGroup n R) where
  carrier := {U | (U : Matrix n n R).det = 1}
  mul_mem' {A B} hA hB := by
    change ((A : Matrix n n R) * (B : Matrix n n R)).det = 1
    rw [det_mul, hA, hB, mul_one]
  one_mem' := det_one
  inv_mem' {A} hA := by
    have hmul : (A : Matrix n n R) * ((A⁻¹ : unitaryGroup n R) : Matrix n n R) = 1 := by
      simpa only [Submonoid.coe_mul, OneMemClass.coe_one] using
        congrArg Subtype.val (mul_inv_cancel A)
    have hdet := congrArg Matrix.det hmul
    rw [det_mul, hA, one_mul, det_one] at hdet
    exact hdet

/-- A unitary matrix lies in `specialUnitarySubgroup` iff its determinant is `1`. -/
@[simp]
theorem UnitaryGroup.mem_specialUnitarySubgroup_iff {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [StarRing R] {U : unitaryGroup n R} :
    U ∈ UnitaryGroup.specialUnitarySubgroup n R ↔ (U : Matrix n n R).det = 1 :=
  Iff.rfl

end SpecialUnitary

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

end Matrix
