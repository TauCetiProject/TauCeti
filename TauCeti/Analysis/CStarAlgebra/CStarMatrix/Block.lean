/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.LinearAlgebra.Matrix.DotProduct
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic

/-!
# Block calculus, norms, reindexing, and rotations for C⋆-matrices

This file develops the matrix calculus for `CStarMatrix` needed to work with projections and
unitaries across varying finite matrix sizes over a (possibly non-unital) C⋆-algebra `A`.

## Main definitions

* `CStarMatrix.fromBlocks`: block matrix construction on `CStarMatrix`.
* `CStarMatrix.inlCornerHom`, `CStarMatrix.inrCornerHom`: the upper-left and lower-right corner
  non-unital ⋆-algebra embeddings `M ↦ diag(M, 0)` and `N ↦ diag(0, N)`.
* `CStarMatrix.blockDiagNonUnitalStarAlgHom`, `CStarMatrix.blockDiagStarAlgHom`: the block-diagonal
  direct sum embedding `(M, N) ↦ diag(M, N)` as a non-unital and unital ⋆-algebra homomorphism.
* `CStarMatrix.mapₐ`: entrywise amplification of a unital ⋆-algebra homomorphism.
* `CStarMatrix.permUnitary`, `CStarMatrix.permUnitaryHom`: permutation unitaries implementing
  finite reindexing by conjugation.
* `CStarMatrix.blockRotation`, `CStarMatrix.blockRotationPath`: the one-parameter rotation group
  `θ ↦ [[cos θ, -sin θ], [sin θ, cos θ]]` in `unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)` joining the
  identity to the block swap `[[0, -1], [1, 0]]`.

## Main results

* `CStarMatrix.norm_fromBlocks_zero₁₂_zero₂₁`: `‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖`.
* `CStarMatrix.norm_fromBlocks_zero₁₁_zero₂₁_zero₂₂`: `‖fromBlocks 0 V 0 0‖ = ‖V‖`.
* `CStarMatrix.norm_conjTranspose_mul_self`, `CStarMatrix.norm_self_mul_conjTranspose`,
  `CStarMatrix.norm_conjTranspose`: rectangular C⋆-identities for `CStarMatrix m n A`.
* `CStarMatrix.conjTranspose_mul_self_nonneg`, `CStarMatrix.self_mul_conjTranspose_nonneg`:
  `0 ≤ Vᴴ * V` and `0 ≤ V * Vᴴ` for rectangular C⋆-matrices `V`.
* `CStarMatrix.permUnitary_conj`: conjugation by `permUnitary σ` agrees with `reindexₐ R A σ`.
* `CStarMatrix.blockRotation_pi_div_two_conj`, `CStarMatrix.joined_one_blockRotation`: the
  rotation path joins `1` to a unitary conjugating `diag(M, N)` to `diag(N, M)`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press, 1998, §4.6.
-/

public section

open Matrix
open scoped ComplexOrder InnerProductSpace Matrix NNReal WithCStarModule

namespace CStarMatrix

/-! ### Rectangular matrix algebra and conjugate transpose -/

section RectangularAlgebra

variable {l m n o R A B C : Type*}

/-- Reading a C⋆-matrix as an ordinary matrix respects rectangular multiplication. -/
@[simp]
theorem ofMatrix_symm_hMul [Fintype m] [Mul A] [AddCommMonoid A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    ofMatrix.symm (M * N) = ofMatrix.symm M * ofMatrix.symm N := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix sends `conjTranspose` to `Matrix.conjTranspose`. -/
@[simp]
theorem ofMatrix_symm_conjTranspose [Star A] (M : CStarMatrix m n A) :
    ofMatrix.symm M.conjTranspose = (ofMatrix.symm M)ᴴ := (rfl)

/-- `ofMatrix` sends `1` to `1`. -/
@[simp]
theorem ofMatrix_one [DecidableEq n] [Zero A] [One A] :
    ofMatrix (1 : Matrix n n A) = (1 : CStarMatrix n n A) := (rfl)

/-- `ofMatrix.symm` sends `1` to `1`. -/
@[simp]
theorem ofMatrix_symm_one [DecidableEq n] [Zero A] [One A] :
    ofMatrix.symm (1 : CStarMatrix n n A) = (1 : Matrix n n A) := (rfl)

/-- `ofMatrix` respects rectangular multiplication. -/
@[simp]
theorem ofMatrix_hMul [Fintype m] [Mul A] [AddCommMonoid A]
    (M : Matrix l m A) (N : Matrix m n A) :
    ofMatrix (M * N) = ofMatrix M * ofMatrix N := (rfl)

/-- `ofMatrix` respects `conjTranspose`. -/
@[simp]
theorem ofMatrix_conjTranspose [Star A] (M : Matrix m n A) :
    ofMatrix Mᴴ = (ofMatrix M).conjTranspose := (rfl)

/-- Associativity of rectangular C⋆-matrix multiplication. -/
protected theorem mul_assoc [Fintype m] [Fintype n] [NonUnitalSemiring A]
    (L : CStarMatrix l m A) (M : CStarMatrix m n A) (N : CStarMatrix n o A) :
    L * M * N = L * (M * N) :=
  Matrix.mul_assoc (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N)

/-- Left identity for rectangular C⋆-matrix multiplication. -/
@[simp]
protected theorem one_mul [Fintype m] [DecidableEq m] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : (1 : CStarMatrix m m A) * M = M :=
  Matrix.one_mul (ofMatrix.symm M)

/-- Right identity for rectangular C⋆-matrix multiplication. -/
@[simp]
protected theorem mul_one [Fintype n] [DecidableEq n] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : M * (1 : CStarMatrix n n A) = M :=
  Matrix.mul_one (ofMatrix.symm M)

/-- Negation pulls out on the left of rectangular C⋆-matrix multiplication. -/
@[simp]
protected theorem neg_mul [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : (-M) * N = -(M * N) :=
  Matrix.neg_mul (ofMatrix.symm M) (ofMatrix.symm N)

/-- Negation pulls out on the right of rectangular C⋆-matrix multiplication. -/
@[simp]
protected theorem mul_neg [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : M * (-N) = -(M * N) :=
  Matrix.mul_neg (ofMatrix.symm M) (ofMatrix.symm N)

/-- Right distributivity over subtraction for rectangular C⋆-matrix multiplication. -/
protected theorem sub_mul [Fintype m] [NonUnitalNonAssocRing A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) : (L - M) * N = L * N - M * N :=
  Matrix.sub_mul (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N)

/-- Left distributivity over subtraction for rectangular C⋆-matrix multiplication. -/
protected theorem mul_sub [Fintype m] [NonUnitalNonAssocRing A]
    (L : CStarMatrix l m A) (M N : CStarMatrix m n A) : L * (M - N) = L * M - L * N :=
  Matrix.mul_sub (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N)

/-- Conjugate transpose is involutive on rectangular C⋆-matrices. -/
@[simp]
theorem conjTranspose_conjTranspose [InvolutiveStar A] (M : CStarMatrix m n A) :
    M.conjTranspose.conjTranspose = M :=
  Matrix.conjTranspose_conjTranspose (ofMatrix.symm M)

/-- Conjugate transpose is additive on rectangular C⋆-matrices. -/
@[simp]
theorem conjTranspose_add [AddMonoid A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M + N).conjTranspose = M.conjTranspose + N.conjTranspose :=
  Matrix.conjTranspose_add (ofMatrix.symm M) (ofMatrix.symm N)

/-- Conjugate transpose commutes with negation on rectangular C⋆-matrices. -/
@[simp]
theorem conjTranspose_neg [AddGroup A] [StarAddMonoid A] (M : CStarMatrix m n A) :
    (-M).conjTranspose = -M.conjTranspose :=
  Matrix.conjTranspose_neg (ofMatrix.symm M)

/-- Conjugate transpose commutes with subtraction on rectangular C⋆-matrices. -/
@[simp]
theorem conjTranspose_sub [AddGroup A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M - N).conjTranspose = M.conjTranspose - N.conjTranspose :=
  Matrix.conjTranspose_sub (ofMatrix.symm M) (ofMatrix.symm N)

/-- Conjugate transpose is conjugate-linear for scalar multiplication. -/
@[simp]
theorem conjTranspose_smul [Star R] [Star A] [SMul R A] [StarModule R A]
    (r : R) (M : CStarMatrix m n A) :
    (r • M).conjTranspose = star r • M.conjTranspose :=
  Matrix.conjTranspose_smul r (ofMatrix.symm M)

/-- Conjugate transpose fixes the identity matrix. -/
@[simp]
theorem conjTranspose_one [DecidableEq n] [NonAssocSemiring A] [StarRing A] :
    (1 : CStarMatrix n n A).conjTranspose = 1 :=
  Matrix.conjTranspose_one

/-- Conjugate transpose reverses rectangular C⋆-matrix multiplication. -/
@[simp]
theorem conjTranspose_mul [Fintype m] [NonUnitalNonAssocSemiring A] [StarRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).conjTranspose = N.conjTranspose * M.conjTranspose :=
  Matrix.conjTranspose_mul (ofMatrix.symm M) (ofMatrix.symm N)

/-- Entrywise `map` composes functorially on `CStarMatrix`. -/
theorem map_comp (M : CStarMatrix m n A) (f : A → B) (g : B → C) :
    (M.map f).map g = M.map (g ∘ f) := by
  ext _ _
  rfl

/-- Entrywise `map` preserves `0` when the entry map preserves `0`. -/
@[simp]
theorem map_zero [Zero A] [Zero B] {f : A → B} (hf : f 0 = 0) :
    (0 : CStarMatrix m n A).map f = 0 := by
  ext _ _
  exact hf

/-- Entrywise `map` preserves `1` when the entry map preserves `0` and `1`. -/
@[simp]
theorem map_one [DecidableEq n] [Zero A] [One A] [Zero B] [One B] {f : A → B}
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) :
    (1 : CStarMatrix n n A).map f = 1 := by
  ext i j
  by_cases h : i = j <;> simp [one_apply, h, hf0, hf1]

/-- Entrywise `map` preserves addition when the entry map does. -/
theorem map_add [Add A] [Add B] (M N : CStarMatrix m n A) {f : A → B}
    (hf : ∀ a b, f (a + b) = f a + f b) :
    (M + N).map f = M.map f + N.map f := by
  ext i j
  exact hf (M i j) (N i j)

/-- Entrywise `map` preserves subtraction when the entry map does. -/
theorem map_sub [Sub A] [Sub B] (M N : CStarMatrix m n A) {f : A → B}
    (hf : ∀ a b, f (a - b) = f a - f b) :
    (M - N).map f = M.map f - N.map f := by
  ext i j
  exact hf (M i j) (N i j)

/-- Entrywise `map` preserves rectangular multiplication for additive multiplicative maps. -/
theorem map_mul [Fintype m] [AddCommMonoid A] [Mul A] [AddCommMonoid B] [Mul B]
    {F : Type*} [FunLike F A B] [AddMonoidHomClass F A B] [MulHomClass F A B]
    (f : F) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).map f = M.map f * N.map f := by
  ext i j
  simp [mul_apply, map_sum, _root_.map_mul]

/-- Entrywise `map` commutes with `conjTranspose` for star-preserving maps. -/
theorem map_conjTranspose [Star A] [Star B] {F : Type*} [FunLike F A B] [StarHomClass F A B]
    (f : F) (M : CStarMatrix m n A) :
    M.conjTranspose.map f = (M.map f).conjTranspose := by
  ext i j
  simp [map_star]

/-- In a proper star-ordered ring, `Mᴴ * M = 0` iff `M = 0` for rectangular C⋆-matrices. -/
@[simp]
theorem conjTranspose_mul_self_eq_zero [Fintype m] [PartialOrder A] [NonUnitalRing A]
    [StarRing A] [StarOrderedRing A] [IsProperStar A] {M : CStarMatrix m n A} :
    M.conjTranspose * M = 0 ↔ M = 0 :=
  Matrix.conjTranspose_mul_self_eq_zero (A := ofMatrix.symm M)

/-- In a proper star-ordered ring, `M * Mᴴ = 0` iff `M = 0` for rectangular C⋆-matrices. -/
@[simp]
theorem self_mul_conjTranspose_eq_zero [Fintype n] [PartialOrder A] [NonUnitalRing A]
    [StarRing A] [StarOrderedRing A] [IsProperStar A] {M : CStarMatrix m n A} :
    M * M.conjTranspose = 0 ↔ M = 0 :=
  Matrix.self_mul_conjTranspose_eq_zero (A := ofMatrix.symm M)

end RectangularAlgebra

/-! ### Block matrices -/

section FromBlocks

variable {m₁ m₂ n₁ n₂ o₁ o₂ R A B : Type*}

/-- Block matrix construction on `CStarMatrix`, delegating to `Matrix.fromBlocks`. -/
def fromBlocks (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M) (ofMatrix.symm N)
    (ofMatrix.symm P) (ofMatrix.symm Q))

/-- Reading `fromBlocks` as an ordinary matrix gives `Matrix.fromBlocks`. -/
@[simp]
theorem ofMatrix_symm_fromBlocks (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    ofMatrix.symm (fromBlocks M N P Q) =
      Matrix.fromBlocks (ofMatrix.symm M) (ofMatrix.symm N)
        (ofMatrix.symm P) (ofMatrix.symm Q) := (rfl)

/-- Upper-left block entry of `fromBlocks`. -/
@[simp]
theorem fromBlocks_apply₁₁ (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) (i : m₁) (j : n₁) :
    fromBlocks M N P Q (Sum.inl i) (Sum.inl j) = M i j := (rfl)

/-- Upper-right block entry of `fromBlocks`. -/
@[simp]
theorem fromBlocks_apply₁₂ (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) (i : m₁) (j : n₂) :
    fromBlocks M N P Q (Sum.inl i) (Sum.inr j) = N i j := (rfl)

/-- Lower-left block entry of `fromBlocks`. -/
@[simp]
theorem fromBlocks_apply₂₁ (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) (i : m₂) (j : n₁) :
    fromBlocks M N P Q (Sum.inr i) (Sum.inl j) = P i j := (rfl)

/-- Lower-right block entry of `fromBlocks`. -/
@[simp]
theorem fromBlocks_apply₂₂ (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) (i : m₂) (j : n₂) :
    fromBlocks M N P Q (Sum.inr i) (Sum.inr j) = Q i j := (rfl)

/-- Two block C⋆-matrices are equal iff their four blocks are equal. -/
@[simp]
theorem fromBlocks_inj {M M' : CStarMatrix m₁ n₁ A} {N N' : CStarMatrix m₁ n₂ A}
    {P P' : CStarMatrix m₂ n₁ A} {Q Q' : CStarMatrix m₂ n₂ A} :
    fromBlocks M N P Q = fromBlocks M' N' P' Q' ↔ M = M' ∧ N = N' ∧ P = P' ∧ Q = Q' :=
  Matrix.fromBlocks_inj

/-- A block matrix of zeros is zero. -/
@[simp]
theorem fromBlocks_zero [Zero A] :
    fromBlocks (0 : CStarMatrix m₁ n₁ A) (0 : CStarMatrix m₁ n₂ A)
      (0 : CStarMatrix m₂ n₁ A) (0 : CStarMatrix m₂ n₂ A) = 0 :=
  Matrix.fromBlocks_zero

/-- The block-diagonal matrix with identity diagonal blocks is `1`. -/
@[simp]
theorem fromBlocks_one [DecidableEq m₁] [DecidableEq m₂] [Zero A] [One A] :
    fromBlocks (1 : CStarMatrix m₁ m₁ A) (0 : CStarMatrix m₁ m₂ A)
      (0 : CStarMatrix m₂ m₁ A) (1 : CStarMatrix m₂ m₂ A) = 1 :=
  Matrix.fromBlocks_one

/-- Block matrix addition is blockwise. -/
@[simp]
theorem fromBlocks_add [Add A] (M M' : CStarMatrix m₁ n₁ A) (N N' : CStarMatrix m₁ n₂ A)
    (P P' : CStarMatrix m₂ n₁ A) (Q Q' : CStarMatrix m₂ n₂ A) :
    fromBlocks M N P Q + fromBlocks M' N' P' Q' =
      fromBlocks (M + M') (N + N') (P + P') (Q + Q') :=
  Matrix.fromBlocks_add _ _ _ _ _ _ _ _

/-- Negation of a block matrix is blockwise. -/
@[simp]
theorem fromBlocks_neg [Neg A] (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    -fromBlocks M N P Q = fromBlocks (-M) (-N) (-P) (-Q) :=
  Matrix.fromBlocks_neg _ _ _ _

/-- Subtraction of block matrices is blockwise. -/
@[simp]
theorem fromBlocks_sub [Sub A] (M M' : CStarMatrix m₁ n₁ A) (N N' : CStarMatrix m₁ n₂ A)
    (P P' : CStarMatrix m₂ n₁ A) (Q Q' : CStarMatrix m₂ n₂ A) :
    fromBlocks M N P Q - fromBlocks M' N' P' Q' =
      fromBlocks (M - M') (N - N') (P - P') (Q - Q') := by
  ext (i | i) (j | j) <;> rfl

/-- Scalar multiplication of a block matrix is blockwise. -/
@[simp]
theorem fromBlocks_smul [SMul R A] (r : R) (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    r • fromBlocks M N P Q = fromBlocks (r • M) (r • N) (r • P) (r • Q) :=
  Matrix.fromBlocks_smul _ _ _ _ _

/-- Conjugate transpose of a block C⋆-matrix. -/
@[simp]
theorem fromBlocks_conjTranspose [Star A] (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    (fromBlocks M N P Q).conjTranspose =
      fromBlocks M.conjTranspose P.conjTranspose N.conjTranspose Q.conjTranspose :=
  Matrix.fromBlocks_conjTranspose _ _ _ _

/-- Star of a square block C⋆-matrix. -/
@[simp]
theorem fromBlocks_star [Star A] (M : CStarMatrix m₁ m₁ A) (N : CStarMatrix m₁ m₂ A)
    (P : CStarMatrix m₂ m₁ A) (Q : CStarMatrix m₂ m₂ A) :
    star (fromBlocks M N P Q) =
      fromBlocks (star M) P.conjTranspose N.conjTranspose (star Q) :=
  fromBlocks_conjTranspose M N P Q

/-- Multiplication of rectangular block C⋆-matrices. -/
@[simp]
theorem fromBlocks_mul [Fintype n₁] [Fintype n₂] [NonUnitalNonAssocSemiring A]
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A)
    (N₁₁ : CStarMatrix n₁ o₁ A) (N₁₂ : CStarMatrix n₁ o₂ A)
    (N₂₁ : CStarMatrix n₂ o₁ A) (N₂₂ : CStarMatrix n₂ o₂ A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ * N₁₁ + M₁₂ * N₂₁) (M₁₁ * N₁₂ + M₁₂ * N₂₂)
        (M₂₁ * N₁₁ + M₂₂ * N₂₁) (M₂₁ * N₁₂ + M₂₂ * N₂₂) :=
  Matrix.fromBlocks_multiply _ _ _ _ _ _ _ _

/-- Entrywise `map` acts blockwise on `fromBlocks`. -/
@[simp]
theorem fromBlocks_map (f : A → B) (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    (fromBlocks M N P Q).map f = fromBlocks (M.map f) (N.map f) (P.map f) (Q.map f) :=
  Matrix.fromBlocks_map _ _ _ _ _

/-- A block-diagonal C⋆-matrix is unitary iff both diagonal blocks are unitary. -/
@[simp]
theorem fromBlocks_zero₁₂_zero₂₁_mem_unitary_iff [Fintype m₁] [Fintype m₂]
    [DecidableEq m₁] [DecidableEq m₂] [Semiring A] [StarRing A]
    {u : CStarMatrix m₁ m₁ A} {v : CStarMatrix m₂ m₂ A} :
    fromBlocks u 0 0 v ∈ unitary (CStarMatrix (m₁ ⊕ m₂) (m₁ ⊕ m₂) A) ↔
      u ∈ unitary (CStarMatrix m₁ m₁ A) ∧ v ∈ unitary (CStarMatrix m₂ m₂ A) := by
  simp only [Unitary.mem_iff, fromBlocks_star, conjTranspose_zero, fromBlocks_mul,
    CStarMatrix.mul_zero, CStarMatrix.zero_mul, add_zero, zero_add, ← fromBlocks_one,
    fromBlocks_inj, true_and]
  tauto

end FromBlocks

/-! ### Corner inclusions, block direct sums, and matrix amplification -/

section Homomorphisms

variable {R m n A B C : Type*}

/-- The upper-left corner embedding `M ↦ diag(M, 0)` as a non-unital ⋆-algebra homomorphism. -/
def inlCornerHom (R m n A : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun M := fromBlocks M 0 0 0
  map_smul' r M := by simp
  map_zero' := by simp
  map_add' M N := by simp
  map_mul' M N := by simp
  map_star' M := by simp

/-- Evaluation of `inlCornerHom`. -/
@[simp]
theorem inlCornerHom_apply [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] (M : CStarMatrix m m A) :
    inlCornerHom R m n A M = fromBlocks M 0 0 0 := (rfl)

/-- The upper-left corner embedding is injective. -/
theorem inlCornerHom_injective [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] :
    Function.Injective (inlCornerHom R m n A) := by
  intro M N h
  simpa using h

/-- The lower-right corner embedding `N ↦ diag(0, N)` as a non-unital ⋆-algebra homomorphism. -/
def inrCornerHom (R m n A : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun N := fromBlocks 0 0 0 N
  map_smul' r N := by simp
  map_zero' := by simp
  map_add' M N := by simp
  map_mul' M N := by simp
  map_star' N := by simp

/-- Evaluation of `inrCornerHom`. -/
@[simp]
theorem inrCornerHom_apply [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] (N : CStarMatrix n n A) :
    inrCornerHom R m n A N = fromBlocks 0 0 0 N := (rfl)

/-- The lower-right corner embedding is injective. -/
theorem inrCornerHom_injective [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] :
    Function.Injective (inrCornerHom R m n A) := by
  intro M N h
  simpa using h

/-- The block-diagonal embedding `(M, N) ↦ diag(M, N)` as a non-unital ⋆-algebra homomorphism. -/
def blockDiagNonUnitalStarAlgHom (R m n A : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun p := fromBlocks p.1 0 0 p.2
  map_smul' r p := by simp
  map_zero' := by simp
  map_add' p q := by simp
  map_mul' p q := by simp
  map_star' p := by simp

/-- Evaluation of `blockDiagNonUnitalStarAlgHom`. -/
@[simp]
theorem blockDiagNonUnitalStarAlgHom_apply [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (p : CStarMatrix m m A × CStarMatrix n n A) :
    blockDiagNonUnitalStarAlgHom R m n A p = fromBlocks p.1 0 0 p.2 := (rfl)

/-- The non-unital block-diagonal embedding is injective. -/
theorem blockDiagNonUnitalStarAlgHom_injective [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (blockDiagNonUnitalStarAlgHom R m n A) := by
  rintro ⟨M₁, N₁⟩ ⟨M₂, N₂⟩ h
  simp only [blockDiagNonUnitalStarAlgHom_apply, fromBlocks_inj, true_and] at h
  exact Prod.ext h.1 h.2

/-- The block-diagonal embedding `(M, N) ↦ diag(M, N)` as a unital ⋆-algebra homomorphism. -/
def blockDiagStarAlgHom (R m n A : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommSemiring R] [Semiring A] [Algebra R A] [StarAddMonoid A] :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun p := fromBlocks p.1 0 0 p.2
  map_one' := fromBlocks_one
  map_mul' p q := by simp
  map_zero' := by simp
  map_add' p q := by simp
  commutes' r := by
    ext (i | i) (j | j) <;> simp [algebraMap_apply]
  map_star' p := by simp

/-- Evaluation of `blockDiagStarAlgHom`. -/
@[simp]
theorem blockDiagStarAlgHom_apply [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommSemiring R] [Semiring A] [Algebra R A] [StarAddMonoid A]
    (p : CStarMatrix m m A × CStarMatrix n n A) :
    blockDiagStarAlgHom R m n A p = fromBlocks p.1 0 0 p.2 := (rfl)

/-- The unital block-diagonal embedding is injective. -/
theorem blockDiagStarAlgHom_injective [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommSemiring R] [Semiring A] [Algebra R A] [StarAddMonoid A] :
    Function.Injective (blockDiagStarAlgHom R m n A) := by
  rintro ⟨M₁, N₁⟩ ⟨M₂, N₂⟩ h
  simp only [blockDiagStarAlgHom_apply, fromBlocks_inj, true_and] at h
  exact Prod.ext h.1 h.2

/-- Non-unital matrix amplification preserves the identity homomorphism. -/
@[simp]
theorem mapₙₐ_id [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A] :
    mapₙₐ (n := n) (NonUnitalStarAlgHom.id R A) =
      NonUnitalStarAlgHom.id R (CStarMatrix n n A) := by
  ext M i j
  rfl

/-- Non-unital matrix amplification respects composition. -/
theorem mapₙₐ_comp [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    [NonUnitalNonAssocSemiring C] [Module R C] [Star C]
    (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) :
    mapₙₐ (n := n) (g.comp f) = (mapₙₐ (n := n) g).comp (mapₙₐ (n := n) f) := by
  ext M i j
  rfl

/-- Non-unital matrix amplification preserves injectivity. -/
theorem mapₙₐ_injective [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    {f : A →⋆ₙₐ[R] B} (hf : Function.Injective f) :
    Function.Injective (mapₙₐ (n := n) f) :=
  map_injective hf

/-- Non-unital matrix amplification acts blockwise on `fromBlocks`. -/
theorem mapₙₐ_fromBlocks [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    (f : A →⋆ₙₐ[R] B) (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix n m A) (M₂₂ : CStarMatrix n n A) :
    mapₙₐ f (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (mapₙₐ f M₁₁) (M₁₂.map f) (M₂₁.map f) (mapₙₐ f M₂₂) :=
  fromBlocks_map f M₁₁ M₁₂ M₂₁ M₂₂

/-- Applying a unital ⋆-algebra homomorphism entrywise to square C⋆-matrices is a unital ⋆-algebra
homomorphism. -/
def mapₐ [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B] (f : A →⋆ₐ[R] B) :
    CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B where
  toFun M := M.map f
  map_one' := map_one (_root_.map_zero f) (_root_.map_one f)
  map_mul' M N := map_mul f M N
  map_zero' := map_zero (_root_.map_zero f)
  map_add' M N := map_add M N (_root_.map_add f)
  commutes' r := by
    ext i j
    by_cases h : i = j
    · simp only [map_apply, algebraMap_apply, h, ↓reduceIte, AlgHomClass.commutes]
    · simp only [map_apply, algebraMap_apply, h, ↓reduceIte, _root_.map_zero]
  map_star' M := map_conjTranspose f M

/-- Evaluation of `mapₐ`. -/
@[simp]
theorem mapₐ_apply [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A]
    [Star A] [Semiring B] [Algebra R B] [Star B] (f : A →⋆ₐ[R] B) (M : CStarMatrix n n A)
    (i j : n) :
    mapₐ f M i j = f (M i j) := (rfl)

/-- Unital matrix amplification preserves the identity homomorphism. -/
@[simp]
theorem mapₐ_id [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] [Star A] :
    mapₐ (n := n) (StarAlgHom.id R A) = StarAlgHom.id R (CStarMatrix n n A) := by
  ext M i j
  rfl

/-- Unital matrix amplification respects composition. -/
theorem mapₐ_comp [Fintype n] [DecidableEq n] [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B]
    [Semiring C] [Algebra R C] [Star C]
    (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    mapₐ (n := n) (g.comp f) = (mapₐ (n := n) g).comp (mapₐ (n := n) f) := by
  ext M i j
  rfl

/-- Unital matrix amplification preserves injectivity. -/
theorem mapₐ_injective [Fintype n] [DecidableEq n] [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
    {f : A →⋆ₐ[R] B} (hf : Function.Injective f) :
    Function.Injective (mapₐ (n := n) f) :=
  map_injective hf

/-- Unital matrix amplification acts blockwise on `fromBlocks`. -/
@[simp]
theorem mapₐ_fromBlocks [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
    (f : A →⋆ₐ[R] B) (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix n m A) (M₂₂ : CStarMatrix n n A) :
    mapₐ f (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (mapₐ f M₁₁) (M₁₂.map f) (M₂₁.map f) (mapₐ f M₂₂) :=
  fromBlocks_map f M₁₁ M₁₂ M₂₁ M₂₂

end Homomorphisms

/-! ### Real continuous functional calculus for unital C⋆-matrices -/

section UnitalCFC

variable {n A : Type*} [Fintype n] [DecidableEq n] [CStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

/-- The unital real continuous functional calculus on `CStarMatrix n n A`, registered directly
because the entrywise real action is definitionally equal to the restriction of the complex action
but not syntactically found by typeclass synthesis. -/
instance instContinuousFunctionalCalculusReal :
    ContinuousFunctionalCalculus ℝ (CStarMatrix n n A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The unital nonnegative real continuous functional calculus on `CStarMatrix n n A`. -/
instance instContinuousFunctionalCalculusNNReal :
    ContinuousFunctionalCalculus ℝ≥0 (CStarMatrix n n A) (0 ≤ ·) :=
  Nonneg.instContinuousFunctionalCalculus

end UnitalCFC

/-! ### Rectangular C⋆-norm, block norms, and positivity -/

section Norms

variable {l m n A B : Type*} [Fintype l] [Fintype m] [NonUnitalCStarAlgebra A]

/-- `toCLM` reverses rectangular matrix multiplication. -/
theorem toCLM_mul (V : CStarMatrix l m A) (W : CStarMatrix m n A) :
    toCLM (V * W) = (toCLM W).comp (toCLM V) := by
  ext x j
  simp only [ContinuousLinearMap.comp_apply, toCLM_apply,
    WithCStarModule.equiv_symm_pi_apply]
  exact congrFun (Matrix.vecMul_vecMul x (ofMatrix.symm V) (ofMatrix.symm W)).symm j

variable [Fintype n] [PartialOrder A] [StarOrderedRing A]

/-- Submultiplicativity of the operator norm for rectangular C⋆-matrices. -/
theorem norm_hMul_le (V : CStarMatrix l m A) (W : CStarMatrix m n A) :
    ‖V * W‖ ≤ ‖V‖ * ‖W‖ := by
  rw [norm_def, toCLM_mul, mul_comm ‖V‖ ‖W‖]
  exact (toCLM W).opNorm_comp_le (toCLM V)

/-- The norm of a block-diagonal C⋆-matrix is the maximum of the norms of its diagonal blocks. -/
@[simp]
theorem norm_fromBlocks_zero₁₂_zero₂₁ (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    ‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖ := by
  have h := NonUnitalStarAlgHom.norm_map (blockDiagNonUnitalStarAlgHom ℂ m n A)
    (blockDiagNonUnitalStarAlgHom_injective (R := ℂ)) (M, N)
  simpa [Prod.norm_def] using h

/-- Embedding into the upper-left corner preserves the C⋆-norm. -/
theorem norm_fromBlocks_zero₁₂_zero₂₁_zero₂₂ (M : CStarMatrix m m A) :
    ‖fromBlocks M (0 : CStarMatrix m n A) (0 : CStarMatrix n m A) (0 : CStarMatrix n n A)‖ =
      ‖M‖ :=
  NonUnitalStarAlgHom.norm_map (inlCornerHom ℂ m n A) (inlCornerHom_injective (R := ℂ)) M

/-- Embedding into the lower-right corner preserves the C⋆-norm. -/
theorem norm_fromBlocks_zero₁₁_zero₁₂_zero₂₁ (N : CStarMatrix n n A) :
    ‖fromBlocks (0 : CStarMatrix m m A) (0 : CStarMatrix m n A) (0 : CStarMatrix n m A) N‖ =
      ‖N‖ :=
  NonUnitalStarAlgHom.norm_map (inrCornerHom ℂ m n A) (inrCornerHom_injective (R := ℂ)) N

/-- Embedding a rectangular matrix into the upper-right off-diagonal block preserves the norm. -/
@[simp]
theorem norm_fromBlocks_zero₁₁_zero₂₁_zero₂₂ (V : CStarMatrix m n A) :
    ‖fromBlocks (0 : CStarMatrix m m A) V (0 : CStarMatrix n m A) (0 : CStarMatrix n n A)‖ =
      ‖V‖ := by
  let B : CStarMatrix (m ⊕ n) (m ⊕ n) A := fromBlocks 0 V 0 0
  refine le_antisymm ?_ ?_
  · rw [norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg V) fun x => ?_
    let xₗ : C⋆ᵐᵒᵈ(A, m → A) := (WithCStarModule.equiv A (m → A)).symm (fun i => x (Sum.inl i))
    have hinner_out : ⟪toCLM B x, toCLM B x⟫_A = ⟪toCLM V xₗ, toCLM V xₗ⟫_A := by
      simp only [toCLM_apply_eq_sum, WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
        Fintype.sum_sum_type, B, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
        CStarModule.inner_zero_right, xₗ]
    have hnorm_out : ‖toCLM B x‖ = ‖toCLM V xₗ‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (toCLM B x),
        CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (toCLM V xₗ), hinner_out]
    have hinner_le : ⟪xₗ, xₗ⟫_A ≤ ⟪x, x⟫_A := by
      rw [WithCStarModule.pi_inner, WithCStarModule.pi_inner, Fintype.sum_sum_type]
      refine le_add_of_le_of_nonneg le_rfl ?_
      exact Finset.sum_nonneg fun j _ => CStarModule.inner_self_nonneg (E := A)
    have hnorm_le : ‖xₗ‖ ≤ ‖x‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) xₗ,
        CStarModule.norm_eq_sqrt_norm_inner_self (A := A) x]
      exact Real.sqrt_le_sqrt (CStarAlgebra.norm_le_norm_of_le_of_nonneg hinner_le
        (CStarModule.inner_self_nonneg (E := C⋆ᵐᵒᵈ(A, m → A))))
    rw [hnorm_out]
    exact ((toCLM V).le_opNorm xₗ).trans (mul_le_mul_of_nonneg_left hnorm_le (norm_nonneg V))
  · rw [norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    let x : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A) :=
      (WithCStarModule.equiv A ((m ⊕ n) → A)).symm (Sum.elim (fun i => y i) 0)
    have hinner_in : ⟪x, x⟫_A = ⟪y, y⟫_A := by
      simp only [WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
        Fintype.sum_sum_type, x, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
        CStarModule.inner_zero_right, Finset.sum_const_zero, add_zero]
    have hnorm_in : ‖x‖ = ‖y‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) x,
        CStarModule.norm_eq_sqrt_norm_inner_self (A := A) y, hinner_in]
    have hinner_out : ⟪toCLM B x, toCLM B x⟫_A = ⟪toCLM V y, toCLM V y⟫_A := by
      simp only [toCLM_apply_eq_sum, WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
        Fintype.sum_sum_type, B, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
        CStarModule.inner_zero_right, x, Sum.elim_inl]
    have hnorm_out : ‖toCLM V y‖ = ‖toCLM B x‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (toCLM V y),
        CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (toCLM B x), hinner_out]
    rw [hnorm_out, ← hnorm_in]
    exact (toCLM B).le_opNorm x

/-- Rectangular C⋆-identity `‖Vᴴ * V‖ = ‖V‖ * ‖V‖`. -/
@[simp]
theorem norm_conjTranspose_mul_self (V : CStarMatrix m n A) :
    ‖V.conjTranspose * V‖ = ‖V‖ * ‖V‖ := by
  have h := CStarRing.norm_star_mul_self
    (x := fromBlocks (0 : CStarMatrix m m A) V (0 : CStarMatrix n m A) (0 : CStarMatrix n n A))
  simpa only [fromBlocks_star, star_zero, conjTranspose_zero, fromBlocks_mul, CStarMatrix.mul_zero,
    CStarMatrix.zero_mul, add_zero, zero_add, norm_fromBlocks_zero₁₁_zero₁₂_zero₂₁,
    norm_fromBlocks_zero₁₁_zero₂₁_zero₂₂] using h

/-- Rectangular C⋆-identity `‖V * Vᴴ‖ = ‖V‖ * ‖V‖`. -/
@[simp]
theorem norm_self_mul_conjTranspose (V : CStarMatrix m n A) :
    ‖V * V.conjTranspose‖ = ‖V‖ * ‖V‖ := by
  have h := CStarRing.norm_self_mul_star
    (x := fromBlocks (0 : CStarMatrix m m A) V (0 : CStarMatrix n m A) (0 : CStarMatrix n n A))
  simpa only [fromBlocks_star, star_zero, conjTranspose_zero, fromBlocks_mul, CStarMatrix.mul_zero,
    CStarMatrix.zero_mul, add_zero, zero_add, norm_fromBlocks_zero₁₂_zero₂₁_zero₂₂,
    norm_fromBlocks_zero₁₁_zero₂₁_zero₂₂] using h

/-- Conjugate transpose is isometric on rectangular C⋆-matrices. -/
@[simp]
theorem norm_conjTranspose (V : CStarMatrix m n A) : ‖V.conjTranspose‖ = ‖V‖ := by
  have hsq : ‖V.conjTranspose‖ * ‖V.conjTranspose‖ = ‖V‖ * ‖V‖ := by
    rw [← norm_conjTranspose_mul_self, conjTranspose_conjTranspose, norm_self_mul_conjTranspose]
  nlinarith [norm_nonneg V, norm_nonneg V.conjTranspose]

/-- For every rectangular C⋆-matrix `V`, `Vᴴ * V` is positive in the spectral order. -/
theorem conjTranspose_mul_self_nonneg (V : CStarMatrix m n A) :
    0 ≤ V.conjTranspose * V := by
  rw [← NonUnitalStarAlgHom.map_le_map_iff (inrCornerHom ℂ m n A)
    (inrCornerHom_injective (R := ℂ)), _root_.map_zero, inrCornerHom_apply]
  have h : fromBlocks (0 : CStarMatrix m m A) 0 0 (V.conjTranspose * V) =
      star (fromBlocks (0 : CStarMatrix m m A) V 0 0) *
        fromBlocks (0 : CStarMatrix m m A) V 0 0 := by
    simp
  rw [h]
  exact star_mul_self_nonneg _

/-- For every rectangular C⋆-matrix `V`, `V * Vᴴ` is positive in the spectral order. -/
theorem self_mul_conjTranspose_nonneg (V : CStarMatrix m n A) :
    0 ≤ V * V.conjTranspose := by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_nonneg V.conjTranspose

/-- Matrix amplification of an injective non-unital ⋆-algebra homomorphism is isometric. -/
theorem norm_mapₙₐ [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {f : A →⋆ₙₐ[ℂ] B} (hf : Function.Injective f) (M : CStarMatrix n n A) :
    ‖mapₙₐ f M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map (mapₙₐ f) (mapₙₐ_injective hf) M

/-- Reindexing a square C⋆-matrix preserves its norm. -/
@[simp]
theorem norm_reindexₐ (e : m ≃ n) (M : CStarMatrix m m A) :
    ‖reindexₐ ℂ A e M‖ = ‖M‖ :=
  StarAlgEquiv.norm_map (reindexₐ ℂ A e) M

end Norms

section Topology

variable {m n A B : Type*} [NonUnitalCStarAlgebra A]

/-- A map into `CStarMatrix m n A` is continuous iff every entry function is continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → CStarMatrix m n A} :
    Continuous f ↔ ∀ i j, Continuous fun x => f x i j := by
  change Continuous (fun x i j => f x i j) ↔ _
  simp only [continuous_pi_iff]

/-- Applying a continuous map entrywise to C⋆-matrices is continuous. -/
theorem continuous_map [NonUnitalCStarAlgebra B] {f : A → B} (hf : Continuous f) :
    Continuous (fun M : CStarMatrix m n A => M.map f) :=
  continuous_iff.mpr fun i j =>
    hf.comp ((continuous_iff.mp continuous_id) i j)

end Topology

/-! ### Reindexing, associativity, commutativity, and permutation unitaries -/

section Reindexing

variable {m₁ m₂ m₃ n R A : Type*}

/-- Reindexing along `Equiv.sumAssoc` reassociates block-diagonal direct sums. -/
theorem reindexₐ_sumAssoc_fromBlocks [Fintype m₁] [Fintype m₂] [Fintype m₃]
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    (M : CStarMatrix m₁ m₁ A) (N : CStarMatrix m₂ m₂ A) (P : CStarMatrix m₃ m₃ A) :
    reindexₐ R A (Equiv.sumAssoc m₁ m₂ m₃)
        (fromBlocks (fromBlocks M 0 0 N) 0 0 P) =
      fromBlocks M 0 0 (fromBlocks N 0 0 P) := by
  ext (i | (i | i)) (j | (j | j)) <;> rfl

/-- Reindexing along `Equiv.sumComm` swaps the diagonal blocks of a block-diagonal matrix. -/
theorem reindexₐ_sumComm_fromBlocks [Fintype m₁] [Fintype m₂]
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    (M : CStarMatrix m₁ m₁ A) (N : CStarMatrix m₂ m₂ A) :
    reindexₐ R A (Equiv.sumComm m₁ m₂) (fromBlocks M 0 0 N) = fromBlocks N 0 0 M := by
  ext (i | i) (j | j) <;> rfl

/-- The permutation unitary implementing `reindexₐ R A σ` by conjugation. -/
def permUnitary [Fintype n] [DecidableEq n] [Semiring A] [StarRing A] (σ : Equiv.Perm n) :
    unitary (CStarMatrix n n A) :=
  ⟨ofMatrix (σ⁻¹.permMatrix A), by
    constructor
    · apply ofMatrix.symm.injective
      simp [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    · apply ofMatrix.symm.injective
      simp [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]⟩

/-- The underlying matrix of `permUnitary σ` is `ofMatrix (σ⁻¹.permMatrix A)`. -/
@[simp]
theorem coe_permUnitary [Fintype n] [DecidableEq n] [Semiring A] [StarRing A] (σ : Equiv.Perm n) :
    (permUnitary (A := A) σ : CStarMatrix n n A) = ofMatrix (σ⁻¹.permMatrix A) := (rfl)

/-- Permutation unitaries form a group homomorphism
`Equiv.Perm n →* unitary (CStarMatrix n n A)`. -/
def permUnitaryHom [Fintype n] [DecidableEq n] [Semiring A] [StarRing A] :
    Equiv.Perm n →* unitary (CStarMatrix n n A) where
  toFun := permUnitary
  map_one' := by
    apply Subtype.ext
    apply ofMatrix.symm.injective
    simp [Matrix.permMatrix_one]
  map_mul' σ τ := by
    apply Subtype.ext
    apply ofMatrix.symm.injective
    simp [_root_.mul_inv_rev, Matrix.permMatrix_mul]

/-- Conjugation by `permUnitary σ` agrees with `reindexₐ R A σ`. -/
theorem permUnitary_conj [Fintype n] [DecidableEq n] [Semiring R] [Semiring A] [Module R A]
    [StarRing A] (σ : Equiv.Perm n) (M : CStarMatrix n n A) :
    (permUnitary (A := A) σ : CStarMatrix n n A) * M *
        star (permUnitary (A := A) σ : CStarMatrix n n A) =
      reindexₐ R A σ M := by
  ext i j
  simp only [coe_permUnitary, star_eq_conjTranspose, ← ofMatrix_conjTranspose,
    Matrix.conjTranspose_permMatrix, inv_inv, reindexₐ_apply]
  have h : ((σ⁻¹.permMatrix A * ofMatrix.symm M) * σ.permMatrix A) i j =
      M (σ.symm i) (σ.symm j) := by
    rw [Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    rfl
  exact h

end Reindexing

/-! ### Explicit 2×2 block rotation unitaries and path -/

section BlockRotation

open scoped unitInterval

variable {n A : Type*} [Fintype n] [DecidableEq n]

/-- The 2×2 block rotation unitary `[[cos θ, -sin θ], [sin θ, cos θ]]` in
`unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)`. -/
noncomputable def blockRotation [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] (θ : ℝ) :
    unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A) :=
  ⟨fromBlocks (Real.cos θ • (1 : CStarMatrix n n A)) (-(Real.sin θ • 1))
    (Real.sin θ • 1) (Real.cos θ • 1), by
    have htrig : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
      simpa [sq] using Real.cos_sq_add_sin_sq θ
    constructor <;>
    · simp only [fromBlocks_star, star_smul, star_trivial, star_one, conjTranspose_neg,
        conjTranspose_smul, conjTranspose_one, fromBlocks_mul, CStarMatrix.neg_mul,
        CStarMatrix.mul_neg, smul_neg, neg_neg, CStarMatrix.smul_mul,
        CStarMatrix.mul_smul, smul_smul, CStarMatrix.one_mul, ← fromBlocks_one, fromBlocks_inj]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        first
        | rw [← add_smul, htrig, one_smul]
        | rw [← add_smul, add_comm, htrig, one_smul]
        | rw [mul_comm (Real.cos θ) (Real.sin θ), neg_add_cancel]
        | rw [mul_comm (Real.cos θ) (Real.sin θ), add_neg_cancel]⟩

/-- Underlying matrix of `blockRotation θ`. -/
@[simp]
theorem coe_blockRotation [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] (θ : ℝ) :
    (blockRotation (n := n) (A := A) θ : CStarMatrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks (Real.cos θ • (1 : CStarMatrix n n A)) (-(Real.sin θ • 1))
        (Real.sin θ • 1) (Real.cos θ • 1) := (rfl)

/-- Rotation by `0` is the identity unitary. -/
@[simp]
theorem blockRotation_zero [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] :
    blockRotation (n := n) (A := A) 0 = 1 := by
  apply Subtype.ext
  simp

/-- Rotation by `π / 2` is the signed block swap `[[0, -1], [1, 0]]`. -/
theorem coe_blockRotation_pi_div_two [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] :
    (blockRotation (n := n) (A := A) (Real.pi / 2) : CStarMatrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks 0 (-1) 1 0 := by
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- Conjugating `diag(M, N)` by the `π / 2` rotation swaps the diagonal blocks to `diag(N, M)`. -/
theorem blockRotation_pi_div_two_conj [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M N : CStarMatrix n n A) :
    (blockRotation (n := n) (A := A) (Real.pi / 2) : CStarMatrix (n ⊕ n) (n ⊕ n) A) *
        fromBlocks M 0 0 N *
        star (blockRotation (n := n) (A := A) (Real.pi / 2) :
          CStarMatrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks N 0 0 M := by
  rw [coe_blockRotation_pi_div_two]
  simp

/-- The block rotation map `θ ↦ blockRotation θ` is continuous on
`CStarMatrix (n ⊕ n) (n ⊕ n) A`. -/
theorem continuous_blockRotation [CStarAlgebra A] :
    Continuous (blockRotation (n := n) (A := A)) := by
  refine Continuous.subtype_mk (continuous_iff.mpr fun i j => ?_) _
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [fromBlocks_apply₁₁, smul_apply]
      fun_prop
    | inr j =>
      simp only [fromBlocks_apply₁₂, neg_apply, smul_apply]
      fun_prop
  | inr i =>
    cases j with
    | inl j =>
      simp only [fromBlocks_apply₂₁, smul_apply]
      fun_prop
    | inr j =>
      simp only [fromBlocks_apply₂₂, smul_apply]
      fun_prop

/-- The continuous path `t ↦ blockRotation (t * θ)` joining `1` to `blockRotation θ` in
`unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)`. -/
noncomputable def blockRotationPath [CStarAlgebra A] (θ : ℝ) :
    Path (1 : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)) (blockRotation θ) where
  toFun t := blockRotation ((t : ℝ) * θ)
  continuous_toFun := continuous_blockRotation.comp (continuous_subtype_val.mul continuous_const)
  source' := by simp
  target' := by simp

/-- Evaluation of `blockRotationPath`. -/
@[simp]
theorem blockRotationPath_apply [CStarAlgebra A] (θ : ℝ) (t : I) :
    blockRotationPath (n := n) (A := A) θ t = blockRotation ((t : ℝ) * θ) := (rfl)

/-- Every block rotation `blockRotation θ` lies in the identity path component of the unitary
group of `CStarMatrix (n ⊕ n) (n ⊕ n) A`. -/
theorem joined_one_blockRotation [CStarAlgebra A] (θ : ℝ) :
    Joined (1 : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)) (blockRotation θ) :=
  ⟨blockRotationPath θ⟩

end BlockRotation

end CStarMatrix

/-- The block-diagonal C⋆-matrix `fromBlocks p 0 0 q` is a star projection when `p` and `q` are. -/
theorem IsStarProjection.fromBlocks_zero₁₂_zero₂₁ {m n A : Type*} [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (CStarMatrix.fromBlocks p 0 0 q) where
  isIdempotentElem := by
    rw [IsIdempotentElem, CStarMatrix.fromBlocks_mul]
    simp [hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]
  isSelfAdjoint := by
    rw [IsSelfAdjoint, CStarMatrix.fromBlocks_star]
    simp [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
