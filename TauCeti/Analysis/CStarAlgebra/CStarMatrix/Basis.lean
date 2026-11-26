/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Matrix units and corner embeddings on `CStarMatrix`

This file develops elementary matrix units `CStarMatrix.single i j a` (wrapping `Matrix.single`),
their algebraic, amplification, and reindexing identities, the `(i, i)`-corner non-unital
`⋆`-algebra homomorphism `CStarMatrix.singleₙₐ`, and the operator-norm identity
`‖single i j a‖ = ‖a‖` over non-unital C⋆-algebras.

## Main definitions

* `CStarMatrix.single`: the matrix in `CStarMatrix m n A` with `a` at `(i, j)` and `0` elsewhere.
* `CStarMatrix.singleₙₐ`: the `(i, i)`-corner embedding `a ↦ single i i a` as a non-unital
  `⋆`-algebra homomorphism `A →⋆ₙₐ[R] CStarMatrix n n A`.
* `CStarMatrix.matrixUnit`: the scalar matrix unit `e_ij = single i j 1` in `CStarMatrix n n ℂ`.

## Main results

* `CStarMatrix.single_mul_single_same`, `CStarMatrix.single_mul_single_of_ne`: matrix-unit
  multiplication rules.
* `CStarMatrix.norm_single`: `‖single i j a‖ = ‖a‖`, with scalar specialization
  `CStarMatrix.norm_matrixUnit` (`‖matrixUnit i j‖ = 1`).

## References

* M. Rørdam, F. Larsen, N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, LMS Student
  Texts 49, Cambridge University Press (2000), Chapter 2.
-/

public section

namespace CStarMatrix

section Zero

variable {m n R A B : Type*} [DecidableEq m] [DecidableEq n]

/-- The matrix in `CStarMatrix m n A` with `a` at `(i, j)` and `0` elsewhere. -/
def single [Zero A] (i : m) (j : n) (a : A) : CStarMatrix m n A :=
  ofMatrix (Matrix.single i j a)

@[simp] theorem ofMatrix_symm_single [Zero A] (i : m) (j : n) (a : A) :
    ofMatrix.symm (single i j a) = Matrix.single i j a := (rfl)

/-- `ofMatrix` sends `Matrix.single` to `CStarMatrix.single`. -/
theorem ofMatrix_single [Zero A] (i : m) (j : n) (a : A) :
    ofMatrix (Matrix.single i j a) = single i j a := (rfl)

@[grind =]
theorem single_apply [Zero A] (i : m) (j : n) (a : A) (i' : m) (j' : n) :
    single i j a i' j' = if i = i' ∧ j = j' then a else 0 :=
  Matrix.single_apply i j a i' j'

@[simp] theorem single_apply_same [Zero A] (i : m) (j : n) (a : A) : single i j a i j = a :=
  Matrix.single_apply_same i j a

@[simp] theorem single_apply_of_ne [Zero A] {i i' : m} {j j' : n} (h : ¬(i = i' ∧ j = j')) (a : A) :
    single i j a i' j' = 0 :=
  Matrix.single_apply_of_ne i j a i' j' h

@[simp] theorem single_zero [Zero A] (i : m) (j : n) : single i j (0 : A) = 0 :=
  ofMatrix.symm.injective <| Matrix.single_zero i j

@[simp] theorem smul_single [Zero A] [SMulZeroClass R A] (r : R) (i : m) (j : n) (a : A) :
    r • single i j a = single i j (r • a) :=
  ofMatrix.symm.injective <| Matrix.smul_single r i j a

theorem single_add [AddZeroClass A] (i : m) (j : n) (a b : A) :
    single i j (a + b) = single i j a + single i j b :=
  ofMatrix.symm.injective <| Matrix.single_add i j a b

theorem single_neg [NegZeroClass A] (i : m) (j : n) (a : A) :
    single i j (-a) = -single i j a := by ext; simp [single_apply, neg_ite]

@[simp] theorem neg_single [NegZeroClass A] (i : m) (j : n) (a : A) :
    -single i j a = single i j (-a) := (single_neg i j a).symm

theorem single_sub [SubNegZeroMonoid A] (i : m) (j : n) (a b : A) :
    single i j (a - b) = single i j a - single i j b := by
  ext; simp only [single_apply, sub_apply]; split_ifs <;> simp

@[simp] theorem map_single [Zero A] [Zero B] {F : Type*} [FunLike F A B] [ZeroHomClass F A B]
    (i : m) (j : n) (a : A) (f : F) : (single i j a).map f = single i j (f a) :=
  ofMatrix.symm.injective <| Matrix.map_single i j a f

@[simp] theorem conjTranspose_single [AddMonoid A] [StarAddMonoid A] (i : m) (j : n) (a : A) :
    (single i j a).conjTranspose = single j i (star a) :=
  ofMatrix.symm.injective <| Matrix.conjTranspose_single i j a

end Zero

section Algebraic

variable {l m n o p R A : Type*}

@[simp] theorem star_single [DecidableEq n] [AddMonoid A] [StarAddMonoid A] (i j : n) (a : A) :
    star (single i j a) = single j i (star a) :=
  conjTranspose_single i j a

@[simp] theorem single_mul_single_same [Fintype m] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    [NonUnitalNonAssocSemiring A] (i : l) (j : m) (k : n) (a b : A) :
    single i j a * single j k b = single i k (a * b) :=
  ofMatrix.symm.injective <| Matrix.single_mul_single_same a i j k b

@[simp] theorem single_mul_single_of_ne [Fintype m] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    [NonUnitalNonAssocSemiring A] (i : l) {j j' : m} (k : n) (h : j ≠ j') (a b : A) :
    single i j a * single j' k b = 0 :=
  ofMatrix.symm.injective <| Matrix.single_mul_single_of_ne a i j j' h b

@[simp] theorem reindexₗ_single [DecidableEq m] [DecidableEq n] [DecidableEq o] [DecidableEq p]
    [Semiring R] [AddCommMonoid A] [Module R A] (eₘ : m ≃ o) (eₙ : n ≃ p) (i : m) (j : n) (a : A) :
    reindexₗ R A eₘ eₙ (single i j a) = single (eₘ i) (eₙ j) a :=
  ofMatrix.symm.injective <| by simp [Matrix.reindex_apply]

@[simp] theorem reindexₐ_single [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A] (e : m ≃ n) (i j : m) (a : A) :
    reindexₐ R A e (single i j a) = single (e i) (e j) a := by
  rw [reindexₐ_eq_reindexₗ, reindexₗ_single]

section CornerHom

variable [Fintype n] [DecidableEq n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [StarAddMonoid A]

/-- The `(i, i)`-corner embedding `a ↦ single i i a` as a non-unital `⋆`-algebra homomorphism. -/
def singleₙₐ (R : Type*) [Semiring R] [Module R A] (i : n) : A →⋆ₙₐ[R] CStarMatrix n n A where
  toFun a := single i i a
  map_smul' r a := (smul_single r i i a).symm
  map_zero' := single_zero i i
  map_add' a b := single_add i i a b
  map_mul' a b := (single_mul_single_same i i i a b).symm
  map_star' a := (star_single i i a).symm

@[simp] theorem singleₙₐ_apply (i : n) (a : A) : singleₙₐ R (A := A) i a = single i i a := (rfl)

theorem singleₙₐ_injective (i : n) : Function.Injective (singleₙₐ R (A := A) i) :=
  fun _ _ h => by simpa using congrArg (fun M => M i i) h

end CornerHom

end Algebraic

/-- Every matrix unit `single i j a` has operator norm `‖a‖`. -/
@[simp]
theorem norm_single {m n A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (i : m) (j : n) (a : A) :
    ‖single i j a‖ = ‖a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_conjTranspose_mul_self,
    conjTranspose_single, single_mul_single_same, sq, ← CStarRing.norm_star_mul_self]
  exact NonUnitalStarAlgHom.norm_map (singleₙₐ ℂ j) (singleₙₐ_injective j) (star a * a)

section MatrixUnit

variable {n : Type*} [DecidableEq n]

/-- The matrix unit `e_ij` of `M_n(ℂ)`, with entry `1` at `(i, j)` and `0` elsewhere. -/
def matrixUnit (i j : n) : CStarMatrix n n ℂ :=
  single i j 1

/-- Reading `e_ij` as an ordinary matrix gives `Matrix.single i j 1`. -/
@[simp]
theorem ofMatrix_symm_matrixUnit (i j : n) :
    ofMatrix.symm (matrixUnit i j) = Matrix.single i j 1 :=
  (rfl)

/-- The entries of `e_ij`. -/
theorem matrixUnit_apply (i j k l : n) :
    matrixUnit i j k l = if i = k ∧ j = l then 1 else 0 :=
  single_apply i j 1 k l

/-- The `(i, j)` entry of `e_ij` is `1`. -/
@[simp]
theorem matrixUnit_apply_same (i j : n) : matrixUnit i j i j = 1 :=
  single_apply_same i j 1

/-- The entries of `e_ij` away from `(i, j)` vanish. -/
@[simp]
theorem matrixUnit_apply_of_ne {i j k l : n} (h : ¬(i = k ∧ j = l)) : matrixUnit i j k l = 0 :=
  single_apply_of_ne h 1

/-- The adjoint of `e_ij` is `e_ji`. -/
@[simp]
theorem star_matrixUnit (i j : n) : star (matrixUnit i j) = matrixUnit j i := by
  simp [matrixUnit]

variable [Fintype n]

/-- `e_ij` is the image of `Matrix.single i j 1` under `CStarMatrix.ofMatrixStarAlgEquiv`. -/
theorem matrixUnit_eq_ofMatrixStarAlgEquiv (i j : n) :
    matrixUnit i j = ofMatrixStarAlgEquiv (Matrix.single i j 1) :=
  (rfl)

/-- Matrix units multiply as `e_ij e_jk = e_ik`. -/
@[simp]
theorem matrixUnit_mul_matrixUnit (i j k : n) :
    matrixUnit i j * matrixUnit j k = matrixUnit i k := by
  simp [matrixUnit]

/-- Matrix units multiply as `e_ij e_kl = 0` when `j ≠ k`. -/
@[simp]
theorem matrixUnit_mul_matrixUnit_of_ne (i : n) {j k : n} (l : n) (h : j ≠ k) :
    matrixUnit i j * matrixUnit k l = 0 :=
  single_mul_single_of_ne i l h 1 1

/-- The diagonal matrix unit `e_ii` is a self-adjoint idempotent. -/
theorem isStarProjection_matrixUnit (i : n) : IsStarProjection (matrixUnit i i) :=
  ⟨matrixUnit_mul_matrixUnit i i i, star_matrixUnit i i⟩

open scoped ComplexOrder in
/-- A matrix unit has norm one. -/
@[simp]
theorem norm_matrixUnit (i j : n) : ‖matrixUnit i j‖ = 1 := by
  simp [matrixUnit]

end MatrixUnit

end CStarMatrix
