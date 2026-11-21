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
import Mathlib.LinearAlgebra.Matrix.DotProduct
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Block calculus, norms, reindexing, and rotations for C⋆-matrices

Block-matrix calculus, functorial amplification, rectangular C⋆-norms and positivity, permutation
unitaries, and continuous 2×2 block rotations for `CStarMatrix` over a (possibly non-unital)
C⋆-algebra `A`.

## Main definitions and results

* `CStarMatrix.fromBlocks`, `inlCornerHom`, `inrCornerHom`, `blockDiagNonUnitalStarAlgHom`,
  `blockDiagStarAlgHom`, `mapₐ`: block matrices, corner/block-diagonal embeddings, and unital
  matrix amplification.
* `norm_fromBlocks_zero₁₂_zero₂₁`, `norm_fromBlocks_zero₁₁_zero₂₁_zero₂₂`,
  `norm_conjTranspose_mul_self`, `norm_self_mul_conjTranspose`, `norm_conjTranspose`,
  `conjTranspose_mul_self_nonneg`, `self_mul_conjTranspose_nonneg`: block/rectangular norms and
  positivity.
* `permUnitaryHom`, `permUnitary_conj`, `blockRotation`, `blockRotationPath`,
  `blockRotation_pi_div_two_conj`, `joined_one_blockRotation`: permutation and rotation unitaries.

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

@[simp] theorem ofMatrix_one [DecidableEq n] [Zero A] [One A] :
    ofMatrix (1 : Matrix n n A) = (1 : CStarMatrix n n A) := (rfl)

@[simp] theorem ofMatrix_mul [Fintype m] [Mul A] [AddCommMonoid A]
    (M : Matrix l m A) (N : Matrix m n A) :
    ofMatrix (M * N) = ofMatrix M * ofMatrix N := (rfl)

@[simp] theorem ofMatrix_conjTranspose [Star A] (M : Matrix m n A) :
    ofMatrix Mᴴ = (ofMatrix M).conjTranspose := (rfl)

@[simp] protected theorem one_mul [Fintype m] [DecidableEq m] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : (1 : CStarMatrix m m A) * M = M :=
  Matrix.one_mul (ofMatrix.symm M)

@[simp] protected theorem mul_one [Fintype n] [DecidableEq n] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : M * (1 : CStarMatrix n n A) = M :=
  Matrix.mul_one (ofMatrix.symm M)

@[simp] protected theorem neg_mul [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : (-M) * N = -(M * N) :=
  Matrix.neg_mul (ofMatrix.symm M) (ofMatrix.symm N)

@[simp] protected theorem mul_neg [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : M * (-N) = -(M * N) :=
  Matrix.mul_neg (ofMatrix.symm M) (ofMatrix.symm N)

protected theorem sub_mul [Fintype m] [NonUnitalNonAssocRing A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) : (L - M) * N = L * N - M * N :=
  Matrix.sub_mul (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N)

protected theorem mul_sub [Fintype m] [NonUnitalNonAssocRing A]
    (L : CStarMatrix l m A) (M N : CStarMatrix m n A) : L * (M - N) = L * M - L * N :=
  Matrix.mul_sub (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N)

@[simp] theorem conjTranspose_add [AddMonoid A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M + N).conjTranspose = M.conjTranspose + N.conjTranspose :=
  Matrix.conjTranspose_add (ofMatrix.symm M) (ofMatrix.symm N)

@[simp] theorem conjTranspose_neg [AddGroup A] [StarAddMonoid A] (M : CStarMatrix m n A) :
    (-M).conjTranspose = -M.conjTranspose :=
  Matrix.conjTranspose_neg (ofMatrix.symm M)

@[simp] theorem conjTranspose_sub [AddGroup A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M - N).conjTranspose = M.conjTranspose - N.conjTranspose :=
  Matrix.conjTranspose_sub (ofMatrix.symm M) (ofMatrix.symm N)

@[simp] theorem conjTranspose_smul [Star R] [Star A] [SMul R A] [StarModule R A]
    (r : R) (M : CStarMatrix m n A) :
    (r • M).conjTranspose = star r • M.conjTranspose :=
  Matrix.conjTranspose_smul r (ofMatrix.symm M)

@[simp] theorem conjTranspose_one [DecidableEq n] [NonAssocSemiring A] [StarRing A] :
    (1 : CStarMatrix n n A).conjTranspose = 1 := Matrix.conjTranspose_one

@[simp] theorem map_zero [Zero A] [Zero B] {f : A → B} (hf : f 0 = 0) :
    (0 : CStarMatrix m n A).map f = 0 := ext fun _ _ => hf

@[simp] theorem map_one [DecidableEq n] [Zero A] [One A] [Zero B] [One B] {f : A → B}
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) : (1 : CStarMatrix n n A).map f = 1 := by
  ext i j; by_cases h : i = j <;> simp [one_apply, h, hf0, hf1]

theorem map_add [Add A] [Add B] (M N : CStarMatrix m n A) {f : A → B}
    (hf : ∀ a b, f (a + b) = f a + f b) : (M + N).map f = M.map f + N.map f :=
  ext fun i j => hf (M i j) (N i j)

theorem map_sub [Sub A] [Sub B] (M N : CStarMatrix m n A) {f : A → B}
    (hf : ∀ a b, f (a - b) = f a - f b) : (M - N).map f = M.map f - N.map f :=
  ext fun i j => hf (M i j) (N i j)

theorem map_mul [Fintype m] [AddCommMonoid A] [Mul A] [AddCommMonoid B] [Mul B]
    {F : Type*} [FunLike F A B] [AddMonoidHomClass F A B] [MulHomClass F A B]
    (f : F) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).map f = M.map f * N.map f := by
  ext i j; simp [mul_apply, map_sum, _root_.map_mul]

theorem map_conjTranspose [Star A] [Star B] {F : Type*} [FunLike F A B] [StarHomClass F A B]
    (f : F) (M : CStarMatrix m n A) :
    M.conjTranspose.map f = (M.map f).conjTranspose := by
  ext i j; simp [map_star]

/-- In a proper star-ordered ring, `Mᴴ * M = 0` iff `M = 0` for rectangular C⋆-matrices. -/
@[simp] theorem conjTranspose_mul_self_eq_zero [Fintype m] [PartialOrder A] [NonUnitalRing A]
    [StarRing A] [StarOrderedRing A] [IsProperStar A] {M : CStarMatrix m n A} :
    M.conjTranspose * M = 0 ↔ M = 0 :=
  Matrix.conjTranspose_mul_self_eq_zero (A := ofMatrix.symm M)

/-- In a proper star-ordered ring, `M * Mᴴ = 0` iff `M = 0` for rectangular C⋆-matrices. -/
@[simp] theorem self_mul_conjTranspose_eq_zero [Fintype n] [PartialOrder A] [NonUnitalRing A]
    [StarRing A] [StarOrderedRing A] [IsProperStar A] {M : CStarMatrix m n A} :
    M * M.conjTranspose = 0 ↔ M = 0 :=
  Matrix.self_mul_conjTranspose_eq_zero (A := ofMatrix.symm M)

end RectangularAlgebra

/-! ### Block matrices -/

section FromBlocks

variable {m₁ m₂ n₁ n₂ o₁ o₂ R A B : Type*}

/-- Block matrix construction on `CStarMatrix`, delegating to `Matrix.fromBlocks`. -/
@[expose] def fromBlocks (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M) (ofMatrix.symm N)
    (ofMatrix.symm P) (ofMatrix.symm Q))

section Apply

variable (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
  (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A)

@[simp] theorem ofMatrix_symm_fromBlocks :
    ofMatrix.symm (fromBlocks M N P Q) =
      Matrix.fromBlocks (ofMatrix.symm M) (ofMatrix.symm N)
        (ofMatrix.symm P) (ofMatrix.symm Q) := (rfl)

@[simp] theorem fromBlocks_apply₁₁ (i : m₁) (j : n₁) :
    fromBlocks M N P Q (Sum.inl i) (Sum.inl j) = M i j := (rfl)

@[simp] theorem fromBlocks_apply₁₂ (i : m₁) (j : n₂) :
    fromBlocks M N P Q (Sum.inl i) (Sum.inr j) = N i j := (rfl)

@[simp] theorem fromBlocks_apply₂₁ (i : m₂) (j : n₁) :
    fromBlocks M N P Q (Sum.inr i) (Sum.inl j) = P i j := (rfl)

@[simp] theorem fromBlocks_apply₂₂ (i : m₂) (j : n₂) :
    fromBlocks M N P Q (Sum.inr i) (Sum.inr j) = Q i j := (rfl)

end Apply

@[simp] theorem fromBlocks_inj {M M' : CStarMatrix m₁ n₁ A} {N N' : CStarMatrix m₁ n₂ A}
    {P P' : CStarMatrix m₂ n₁ A} {Q Q' : CStarMatrix m₂ n₂ A} :
    fromBlocks M N P Q = fromBlocks M' N' P' Q' ↔ M = M' ∧ N = N' ∧ P = P' ∧ Q = Q' :=
  Matrix.fromBlocks_inj

@[simp] theorem fromBlocks_zero [Zero A] :
    fromBlocks (0 : CStarMatrix m₁ n₁ A) (0 : CStarMatrix m₁ n₂ A)
      (0 : CStarMatrix m₂ n₁ A) (0 : CStarMatrix m₂ n₂ A) = 0 := Matrix.fromBlocks_zero

@[simp] theorem fromBlocks_one [DecidableEq m₁] [DecidableEq m₂] [Zero A] [One A] :
    fromBlocks (1 : CStarMatrix m₁ m₁ A) (0 : CStarMatrix m₁ m₂ A)
      (0 : CStarMatrix m₂ m₁ A) (1 : CStarMatrix m₂ m₂ A) = 1 := Matrix.fromBlocks_one

@[simp] theorem fromBlocks_add [Add A] (M M' : CStarMatrix m₁ n₁ A) (N N' : CStarMatrix m₁ n₂ A)
    (P P' : CStarMatrix m₂ n₁ A) (Q Q' : CStarMatrix m₂ n₂ A) :
    fromBlocks M N P Q + fromBlocks M' N' P' Q' =
      fromBlocks (M + M') (N + N') (P + P') (Q + Q') := Matrix.fromBlocks_add _ _ _ _ _ _ _ _

@[simp] theorem fromBlocks_neg [Neg A] (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    -fromBlocks M N P Q = fromBlocks (-M) (-N) (-P) (-Q) := Matrix.fromBlocks_neg _ _ _ _

@[simp] theorem fromBlocks_sub [Sub A] (M M' : CStarMatrix m₁ n₁ A) (N N' : CStarMatrix m₁ n₂ A)
    (P P' : CStarMatrix m₂ n₁ A) (Q Q' : CStarMatrix m₂ n₂ A) :
    fromBlocks M N P Q - fromBlocks M' N' P' Q' =
      fromBlocks (M - M') (N - N') (P - P') (Q - Q') := by ext (i | i) (j | j) <;> rfl

@[simp] theorem fromBlocks_smul [SMul R A] (r : R) (M : CStarMatrix m₁ n₁ A)
    (N : CStarMatrix m₁ n₂ A) (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    r • fromBlocks M N P Q = fromBlocks (r • M) (r • N) (r • P) (r • Q) :=
  Matrix.fromBlocks_smul _ _ _ _ _

@[simp] theorem fromBlocks_conjTranspose [Star A] (M : CStarMatrix m₁ n₁ A)
    (N : CStarMatrix m₁ n₂ A) (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    (fromBlocks M N P Q).conjTranspose =
      fromBlocks M.conjTranspose P.conjTranspose N.conjTranspose Q.conjTranspose :=
  Matrix.fromBlocks_conjTranspose _ _ _ _

@[simp] theorem fromBlocks_star [Star A] (M : CStarMatrix m₁ m₁ A) (N : CStarMatrix m₁ m₂ A)
    (P : CStarMatrix m₂ m₁ A) (Q : CStarMatrix m₂ m₂ A) :
    star (fromBlocks M N P Q) = fromBlocks (star M) P.conjTranspose N.conjTranspose (star Q) :=
  fromBlocks_conjTranspose M N P Q

@[simp] theorem fromBlocks_mul [Fintype n₁] [Fintype n₂] [NonUnitalNonAssocSemiring A]
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A)
    (N₁₁ : CStarMatrix n₁ o₁ A) (N₁₂ : CStarMatrix n₁ o₂ A)
    (N₂₁ : CStarMatrix n₂ o₁ A) (N₂₂ : CStarMatrix n₂ o₂ A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ * N₁₁ + M₁₂ * N₂₁) (M₁₁ * N₁₂ + M₁₂ * N₂₂)
        (M₂₁ * N₁₁ + M₂₂ * N₂₁) (M₂₁ * N₁₂ + M₂₂ * N₂₂) :=
  Matrix.fromBlocks_multiply _ _ _ _ _ _ _ _

@[simp] theorem fromBlocks_map (f : A → B) (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    (fromBlocks M N P Q).map f = fromBlocks (M.map f) (N.map f) (P.map f) (Q.map f) :=
  Matrix.fromBlocks_map _ _ _ _ _

/-- A block-diagonal C⋆-matrix is unitary iff both diagonal blocks are unitary. -/
@[simp] theorem fromBlocks_zero₁₂_zero₂₁_mem_unitary_iff [Fintype m₁] [Fintype m₂]
    [DecidableEq m₁] [DecidableEq m₂] [Semiring A] [StarRing A]
    {u : CStarMatrix m₁ m₁ A} {v : CStarMatrix m₂ m₂ A} :
    fromBlocks u 0 0 v ∈ unitary (CStarMatrix (m₁ ⊕ m₂) (m₁ ⊕ m₂) A) ↔
      u ∈ unitary (CStarMatrix m₁ m₁ A) ∧ v ∈ unitary (CStarMatrix m₂ m₂ A) := by
  simp only [Unitary.mem_iff, fromBlocks_star, conjTranspose_zero, fromBlocks_mul,
    CStarMatrix.mul_zero, CStarMatrix.zero_mul, add_zero, zero_add, ← fromBlocks_one,
    fromBlocks_inj, true_and]; tauto

end FromBlocks

/-! ### Corner inclusions, block direct sums, and matrix amplification -/

section Homomorphisms

section NonUnitalCorners

variable {R m n A : Type*} [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
  [Module R A] [StarAddMonoid A]

/-- The upper-left corner embedding `M ↦ diag(M, 0)` as a non-unital ⋆-algebra homomorphism. -/
def inlCornerHom (R m n A : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  { toFun := fun M => fromBlocks M 0 0 0, map_smul' := by simp, map_zero' := by simp,
    map_add' := by simp, map_mul' := by simp, map_star' := by simp }

@[simp] theorem inlCornerHom_apply (M : CStarMatrix m m A) :
    inlCornerHom R m n A M = fromBlocks M 0 0 0 := (rfl)

theorem inlCornerHom_injective : Function.Injective (inlCornerHom R m n A) :=
  fun _ _ h => by simpa using h

/-- The lower-right corner embedding `N ↦ diag(0, N)` as a non-unital ⋆-algebra homomorphism. -/
def inrCornerHom (R m n A : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  { toFun := fun N => fromBlocks 0 0 0 N, map_smul' := by simp, map_zero' := by simp,
    map_add' := by simp, map_mul' := by simp, map_star' := by simp }

@[simp] theorem inrCornerHom_apply (N : CStarMatrix n n A) :
    inrCornerHom R m n A N = fromBlocks 0 0 0 N := (rfl)

theorem inrCornerHom_injective : Function.Injective (inrCornerHom R m n A) :=
  fun _ _ h => by simpa using h

/-- The block-diagonal embedding `(M, N) ↦ diag(M, N)` as a non-unital ⋆-algebra homomorphism. -/
def blockDiagNonUnitalStarAlgHom (R m n A : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  { toFun := fun p => fromBlocks p.1 0 0 p.2, map_smul' := by simp, map_zero' := by simp,
    map_add' := by simp, map_mul' := by simp, map_star' := by simp }

@[simp] theorem blockDiagNonUnitalStarAlgHom_apply (p : CStarMatrix m m A × CStarMatrix n n A) :
    blockDiagNonUnitalStarAlgHom R m n A p = fromBlocks p.1 0 0 p.2 := (rfl)

theorem blockDiagNonUnitalStarAlgHom_injective :
    Function.Injective (blockDiagNonUnitalStarAlgHom R m n A) := fun ⟨_, _⟩ ⟨_, _⟩ h => by
  simp only [blockDiagNonUnitalStarAlgHom_apply, fromBlocks_inj, true_and] at h
  exact Prod.ext h.1 h.2

end NonUnitalCorners

section UnitalCorners

variable {R m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CommSemiring R] [Semiring A] [Algebra R A] [StarAddMonoid A]

/-- The block-diagonal embedding `(M, N) ↦ diag(M, N)` as a unital ⋆-algebra homomorphism. -/
def blockDiagStarAlgHom (R m n A : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommSemiring R] [Semiring A] [Algebra R A] [StarAddMonoid A] :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  { toFun := fun p => fromBlocks p.1 0 0 p.2, map_one' := fromBlocks_one, map_mul' := by simp,
    map_zero' := by simp, map_add' := by simp,
    commutes' := fun _ => by ext (i | i) (j | j) <;> simp [algebraMap_apply],
    map_star' := by simp }

@[simp] theorem blockDiagStarAlgHom_apply (p : CStarMatrix m m A × CStarMatrix n n A) :
    blockDiagStarAlgHom R m n A p = fromBlocks p.1 0 0 p.2 := (rfl)

theorem blockDiagStarAlgHom_injective :
    Function.Injective (blockDiagStarAlgHom R m n A) := fun ⟨_, _⟩ ⟨_, _⟩ h => by
  simp only [blockDiagStarAlgHom_apply, fromBlocks_inj, true_and] at h
  exact Prod.ext h.1 h.2

end UnitalCorners

section MapNA

variable {R m n A B C : Type*} [Fintype n] [Semiring R]
  [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
  [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
  [NonUnitalNonAssocSemiring C] [Module R C] [Star C]

@[simp] theorem mapₙₐ_id :
    mapₙₐ (n := n) (NonUnitalStarAlgHom.id R A) =
      NonUnitalStarAlgHom.id R (CStarMatrix n n A) := by ext; rfl

theorem mapₙₐ_comp (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) :
    mapₙₐ (n := n) (g.comp f) = (mapₙₐ (n := n) g).comp (mapₙₐ (n := n) f) := by ext; rfl

end MapNA

section MapA

variable {R m n A B C : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]
  [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
  [Semiring C] [Algebra R C] [Star C]

/-- Entrywise amplification of a unital ⋆-algebra homomorphism to square C⋆-matrices. -/
def mapₐ (f : A →⋆ₐ[R] B) : CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B where
  toFun M := M.map f
  map_one' := map_one (_root_.map_zero f) (_root_.map_one f)
  map_mul' := map_mul f
  map_zero' := map_zero (_root_.map_zero f)
  map_add' M N := map_add M N (_root_.map_add f)
  commutes' _ := by
    ext i j
    by_cases h : i = j <;> simp [algebraMap_apply, h, AlgHomClass.commutes]
  map_star' := map_conjTranspose f

@[simp] theorem mapₐ_apply (f : A →⋆ₐ[R] B) (M : CStarMatrix n n A) (i j : n) :
    mapₐ f M i j = f (M i j) := (rfl)

@[simp] theorem mapₐ_id :
    mapₐ (n := n) (StarAlgHom.id R A) = StarAlgHom.id R (CStarMatrix n n A) := by ext; rfl

theorem mapₐ_comp (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    mapₐ (n := n) (g.comp f) = (mapₐ (n := n) g).comp (mapₐ (n := n) f) := by ext; rfl

end MapA

end Homomorphisms

/-! ### Real continuous functional calculus for unital C⋆-matrices -/

section UnitalCFC

variable {n A : Type*} [Fintype n] [DecidableEq n] [CStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

/-! Like the non-unital case in `CStarMatrix.lean`, the unital real continuous functional calculus
of `CStarMatrix n n A` is not found by instance search because `CStarMatrix.instAlgebra` gives the
entrywise `ℝ`-algebra rather than `Algebra.complexToReal` used by
`IsSelfAdjoint.instContinuousFunctionalCalculus`. Once this instance is registered,
`Nonneg.instContinuousFunctionalCalculus` synthesizes the `ℝ≥0` instance automatically. -/

/-- Unital real continuous functional calculus on `CStarMatrix n n A`. -/
instance instContinuousFunctionalCalculusReal :
    ContinuousFunctionalCalculus ℝ (CStarMatrix n n A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

end UnitalCFC

/-! ### Rectangular C⋆-norm, block norms, and positivity -/

section Norms

variable {l m n A B : Type*} [Fintype l] [Fintype m] [NonUnitalCStarAlgebra A]

/-- `toCLM` reverses rectangular matrix multiplication. -/
theorem toCLM_mul (V : CStarMatrix l m A) (W : CStarMatrix m n A) :
    toCLM (V * W) = (toCLM W).comp (toCLM V) := by
  ext x j
  simp only [ContinuousLinearMap.comp_apply, toCLM_apply, WithCStarModule.equiv_symm_pi_apply]
  exact congrFun (Matrix.vecMul_vecMul x (ofMatrix.symm V) (ofMatrix.symm W)).symm j

variable [Fintype n] [PartialOrder A] [StarOrderedRing A]

/-- Submultiplicativity of the operator norm for rectangular C⋆-matrices. -/
theorem norm_hMul_le (V : CStarMatrix l m A) (W : CStarMatrix m n A) :
    ‖V * W‖ ≤ ‖V‖ * ‖W‖ := by
  rw [norm_def, toCLM_mul, mul_comm ‖V‖ ‖W‖]
  exact (toCLM W).opNorm_comp_le (toCLM V)

/-- The norm of a block-diagonal C⋆-matrix is the maximum of the norms of its diagonal blocks. -/
@[simp] theorem norm_fromBlocks_zero₁₂_zero₂₁ (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    ‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖ := by
  simpa [Prod.norm_def] using NonUnitalStarAlgHom.norm_map (blockDiagNonUnitalStarAlgHom ℂ m n A)
    (blockDiagNonUnitalStarAlgHom_injective (R := ℂ)) (M, N)

/-- Embedding a rectangular matrix into the upper-right off-diagonal block preserves the norm. -/
@[simp] theorem norm_fromBlocks_zero₁₁_zero₂₁_zero₂₂ (V : CStarMatrix m n A) :
    ‖fromBlocks (0 : CStarMatrix m m A) V (0 : CStarMatrix n m A) (0 : CStarMatrix n n A)‖ =
      ‖V‖ := by
  let B : CStarMatrix (m ⊕ n) (m ⊕ n) A := fromBlocks 0 V 0 0
  have hnorm_out (x : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A)) :
      ‖toCLM B x‖ =
        ‖toCLM V ((WithCStarModule.equiv A (m → A)).symm (fun i => x (Sum.inl i)))‖ := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (toCLM B x),
      CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (toCLM V _)]
    congr 2
    simp only [toCLM_apply_eq_sum, WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
      Fintype.sum_sum_type, B, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
      CStarModule.inner_zero_right]
  refine le_antisymm ?_ ?_
  · rw [norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg V) fun x => ?_
    let xₗ : C⋆ᵐᵒᵈ(A, m → A) := (WithCStarModule.equiv A (m → A)).symm (fun i => x (Sum.inl i))
    have hnorm_le : ‖xₗ‖ ≤ ‖x‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) xₗ,
        CStarModule.norm_eq_sqrt_norm_inner_self (A := A) x]
      refine Real.sqrt_le_sqrt (CStarAlgebra.norm_le_norm_of_le_of_nonneg ?_
        (CStarModule.inner_self_nonneg (E := C⋆ᵐᵒᵈ(A, m → A))))
      rw [WithCStarModule.pi_inner, WithCStarModule.pi_inner, Fintype.sum_sum_type]
      exact le_add_of_le_of_nonneg le_rfl (Finset.sum_nonneg fun _ _ =>
        CStarModule.inner_self_nonneg (E := A))
    rw [hnorm_out x]
    exact ((toCLM V).le_opNorm xₗ).trans (mul_le_mul_of_nonneg_left hnorm_le (norm_nonneg V))
  · rw [norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    let x : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A) :=
      (WithCStarModule.equiv A ((m ⊕ n) → A)).symm (Sum.elim (fun i => y i) 0)
    have hnorm_in : ‖x‖ = ‖y‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) x,
        CStarModule.norm_eq_sqrt_norm_inner_self (A := A) y]
      congr 2
      simp only [WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
        Fintype.sum_sum_type, x, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
        CStarModule.inner_zero_right, Finset.sum_const_zero, add_zero]
    have hproj : (WithCStarModule.equiv A (m → A)).symm (fun i => x (Sum.inl i)) = y := by
      ext i; simp [x]
    rw [← hnorm_in, ← hproj, ← hnorm_out x]
    exact (toCLM B).le_opNorm x

/-- Rectangular C⋆-identity `‖Vᴴ * V‖ = ‖V‖ * ‖V‖`. -/
@[simp] theorem norm_conjTranspose_mul_self (V : CStarMatrix m n A) :
    ‖V.conjTranspose * V‖ = ‖V‖ * ‖V‖ := by
  simpa only [fromBlocks_star, star_zero, conjTranspose_zero, fromBlocks_mul, CStarMatrix.mul_zero,
    CStarMatrix.zero_mul, add_zero, zero_add, norm_fromBlocks_zero₁₂_zero₂₁, norm_zero,
    max_eq_right (norm_nonneg _), norm_fromBlocks_zero₁₁_zero₂₁_zero₂₂] using
    CStarRing.norm_star_mul_self
      (x := fromBlocks (0 : CStarMatrix m m A) V 0 (0 : CStarMatrix n n A))

/-- Rectangular C⋆-identity `‖V * Vᴴ‖ = ‖V‖ * ‖V‖`. -/
@[simp] theorem norm_self_mul_conjTranspose (V : CStarMatrix m n A) :
    ‖V * V.conjTranspose‖ = ‖V‖ * ‖V‖ := by
  simpa only [fromBlocks_star, star_zero, conjTranspose_zero, fromBlocks_mul, CStarMatrix.mul_zero,
    CStarMatrix.zero_mul, add_zero, zero_add, norm_fromBlocks_zero₁₂_zero₂₁, norm_zero,
    max_eq_left (norm_nonneg _), norm_fromBlocks_zero₁₁_zero₂₁_zero₂₂] using
    CStarRing.norm_self_mul_star
      (x := fromBlocks (0 : CStarMatrix m m A) V 0 (0 : CStarMatrix n n A))

/-- Conjugate transpose is isometric on rectangular C⋆-matrices. -/
@[simp] theorem norm_conjTranspose (V : CStarMatrix m n A) : ‖V.conjTranspose‖ = ‖V‖ := by
  have hsq : ‖V.conjTranspose‖ * ‖V.conjTranspose‖ = ‖V‖ * ‖V‖ := by
    rw [← norm_conjTranspose_mul_self, conjTranspose_conjTranspose, norm_self_mul_conjTranspose]
  nlinarith [norm_nonneg V, norm_nonneg V.conjTranspose]

/-- For every rectangular C⋆-matrix `V`, `Vᴴ * V` is positive in the spectral order. -/
theorem conjTranspose_mul_self_nonneg (V : CStarMatrix m n A) : 0 ≤ V.conjTranspose * V := by
  rw [← NonUnitalStarAlgHom.map_le_map_iff (inrCornerHom ℂ m n A)
    (inrCornerHom_injective (R := ℂ)), _root_.map_zero, inrCornerHom_apply]
  have h : fromBlocks (0 : CStarMatrix m m A) 0 0 (V.conjTranspose * V) =
      star (fromBlocks (0 : CStarMatrix m m A) V 0 0) * fromBlocks (0 : CStarMatrix m m A) V 0 0 :=
    by simp
  exact h ▸ star_mul_self_nonneg _

/-- For every rectangular C⋆-matrix `V`, `V * Vᴴ` is positive in the spectral order. -/
theorem self_mul_conjTranspose_nonneg (V : CStarMatrix m n A) : 0 ≤ V * V.conjTranspose := by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_nonneg V.conjTranspose

/-- Matrix amplification of an injective non-unital ⋆-algebra homomorphism is isometric. -/
theorem norm_mapₙₐ [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {f : A →⋆ₙₐ[ℂ] B} (hf : Function.Injective f) (M : CStarMatrix n n A) :
    ‖mapₙₐ f M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map (mapₙₐ f) (CStarMatrix.map_injective hf) M

/-- Reindexing a square C⋆-matrix preserves its norm. -/
@[simp] theorem norm_reindexₐ (e : m ≃ n) (M : CStarMatrix m m A) :
    ‖reindexₐ ℂ A e M‖ = ‖M‖ := StarAlgEquiv.norm_map (reindexₐ ℂ A e) M

end Norms

/-! ### Reindexing, associativity, commutativity, and permutation unitaries -/

section Reindexing

variable {m₁ m₂ m₃ n R A : Type*}

/-- Reindexing along `Equiv.sumAssoc` reassociates block-diagonal direct sums. -/
theorem reindexₐ_sumAssoc_fromBlocks [Fintype m₁] [Fintype m₂] [Fintype m₃]
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    (M : CStarMatrix m₁ m₁ A) (N : CStarMatrix m₂ m₂ A) (P : CStarMatrix m₃ m₃ A) :
    reindexₐ R A (Equiv.sumAssoc m₁ m₂ m₃) (fromBlocks (fromBlocks M 0 0 N) 0 0 P) =
      fromBlocks M 0 0 (fromBlocks N 0 0 P) := by
  ext (i | (i | i)) (j | (j | j)) <;> rfl

/-- Reindexing along `Equiv.sumComm` swaps the diagonal blocks of a block-diagonal matrix. -/
theorem reindexₐ_sumComm_fromBlocks [Fintype m₁] [Fintype m₂]
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    (M : CStarMatrix m₁ m₁ A) (N : CStarMatrix m₂ m₂ A) :
    reindexₐ R A (Equiv.sumComm m₁ m₂) (fromBlocks M 0 0 N) = fromBlocks N 0 0 M := by
  ext (i | i) (j | j) <;> rfl

section PermUnitary

variable [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]

/-- Permutation unitaries form a group homomorphism
`Equiv.Perm n →* unitary (CStarMatrix n n A)`. -/
def permUnitaryHom : Equiv.Perm n →* unitary (CStarMatrix n n A) :=
  (Unitary.map (⟨(ofMatrixRingEquiv : Matrix n n A ≃+* CStarMatrix n n A).toMonoidHom,
    fun _ => rfl⟩ : Matrix n n A →⋆* CStarMatrix n n A)).toMonoidHom.comp
    Matrix.permutationUnitary

/-- Conjugation by `permUnitaryHom σ` agrees with `reindexₐ R A σ`. -/
theorem permUnitary_conj [Semiring R] [Module R A] (σ : Equiv.Perm n) (M : CStarMatrix n n A) :
    (permUnitaryHom (A := A) σ : CStarMatrix n n A) * M *
        star (permUnitaryHom (A := A) σ : CStarMatrix n n A) = reindexₐ R A σ M := by
  ext i j
  have hcoe : (permUnitaryHom (A := A) σ : CStarMatrix n n A) = ofMatrix (σ⁻¹.permMatrix A) :=
    congrArg ofMatrix (Matrix.coe_permutationUnitary σ)
  simp only [hcoe, star_eq_conjTranspose, ← ofMatrix_conjTranspose,
    Matrix.conjTranspose_permMatrix, inv_inv, reindexₐ_apply]
  change ((σ⁻¹.permMatrix A * ofMatrix.symm M) * σ.permMatrix A) i j = M (σ.symm i) (σ.symm j)
  rw [Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rfl

end PermUnitary

end Reindexing

/-! ### Explicit 2×2 block rotation unitaries and path -/

section BlockRotation

open scoped unitInterval

variable {n A : Type*} [Fintype n] [DecidableEq n]

section RingRotation

variable [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [StarModule ℝ A]

/-- The 2×2 block rotation unitary `[[cos θ, -sin θ], [sin θ, cos θ]]` in
`unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)`. -/
noncomputable def blockRotation (θ : ℝ) : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A) :=
  ⟨fromBlocks (Real.cos θ • (1 : CStarMatrix n n A)) (-(Real.sin θ • 1))
    (Real.sin θ • 1) (Real.cos θ • 1), by
    have htrig : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
      simpa [sq] using Real.cos_sq_add_sin_sq θ
    constructor <;>
    · simp only [fromBlocks_star, star_smul, star_trivial, star_one, conjTranspose_neg,
        conjTranspose_smul, conjTranspose_one, fromBlocks_mul, CStarMatrix.neg_mul,
        CStarMatrix.mul_neg, smul_neg, neg_neg, CStarMatrix.smul_mul, CStarMatrix.mul_smul,
        smul_smul, CStarMatrix.one_mul, ← fromBlocks_one, fromBlocks_inj]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        first
        | rw [← add_smul, htrig, one_smul]
        | rw [← add_smul, add_comm, htrig, one_smul]
        | rw [mul_comm (Real.cos θ) (Real.sin θ), neg_add_cancel]
        | rw [mul_comm (Real.cos θ) (Real.sin θ), add_neg_cancel]⟩

@[simp] theorem coe_blockRotation (θ : ℝ) :
    (blockRotation (n := n) (A := A) θ : CStarMatrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks (Real.cos θ • (1 : CStarMatrix n n A)) (-(Real.sin θ • 1))
        (Real.sin θ • 1) (Real.cos θ • 1) := (rfl)

@[simp] theorem blockRotation_zero : blockRotation (n := n) (A := A) 0 = 1 :=
  Subtype.ext <| by simp

/-- Rotation by `π / 2` is the signed block swap `[[0, -1], [1, 0]]`. -/
theorem coe_blockRotation_pi_div_two :
    (blockRotation (n := n) (A := A) (Real.pi / 2) : CStarMatrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks 0 (-1) 1 0 := by simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- Conjugating `diag(M, N)` by the `π / 2` rotation swaps the diagonal blocks to `diag(N, M)`. -/
theorem blockRotation_pi_div_two_conj (M N : CStarMatrix n n A) :
    (blockRotation (n := n) (A := A) (Real.pi / 2) : CStarMatrix (n ⊕ n) (n ⊕ n) A) *
        fromBlocks M 0 0 N *
        star (blockRotation (n := n) (A := A) (Real.pi / 2) : CStarMatrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks N 0 0 M := by
  rw [coe_blockRotation_pi_div_two]; simp

end RingRotation

section CStarRotation

variable [CStarAlgebra A]

/-- The block rotation map `θ ↦ blockRotation θ` is continuous on
`CStarMatrix (n ⊕ n) (n ⊕ n) A`. -/
theorem continuous_blockRotation : Continuous (blockRotation (n := n) (A := A)) := by
  refine Continuous.subtype_mk ?_ _
  change Continuous fun θ : ℝ => Matrix.fromBlocks
    (Real.cos θ • (1 : Matrix n n A)) (-(Real.sin θ • 1))
    (Real.sin θ • 1) (Real.cos θ • 1)
  exact Continuous.matrix_fromBlocks (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

/-- The continuous path `t ↦ blockRotation (t * θ)` joining `1` to `blockRotation θ`. -/
noncomputable def blockRotationPath (θ : ℝ) :
    Path (1 : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)) (blockRotation θ) where
  toFun t := blockRotation ((t : ℝ) * θ)
  continuous_toFun := continuous_blockRotation.comp (continuous_subtypeVal.mul continuous_const)
  source' := by simp
  target' := by simp

@[simp] theorem blockRotationPath_apply (θ : ℝ) (t : I) :
    blockRotationPath (n := n) (A := A) θ t = blockRotation ((t : ℝ) * θ) := (rfl)

/-- Every `blockRotation θ` lies in the identity path component of the unitary group. -/
theorem joined_one_blockRotation (θ : ℝ) :
    Joined (1 : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)) (blockRotation θ) :=
  ⟨blockRotationPath θ⟩

end CStarRotation

end BlockRotation

end CStarMatrix
