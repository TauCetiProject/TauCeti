/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Block sums, corners, reindexing, and rectangular norms on `CStarMatrix`

This file develops the matrix calculus on `CStarMatrix` needed to manipulate rectangular
partial isometries, corners, amplifications, permutations, and block-diagonal sums over
possibly non-unital C⋆-algebras.

## Main definitions

* `CStarMatrix.mapₐ`: entrywise amplification of a unital `⋆`-algebra homomorphism
  `A →⋆ₐ[R] B` to `CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B`.
* `CStarMatrix.fromBlocks`: `2 × 2` block matrices in `CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A`.
* `CStarMatrix.blockDiagₙₐ`, `CStarMatrix.inlₙₐ`, `CStarMatrix.inrₙₐ`: the block-diagonal sum
  and upper-left / lower-right corner embeddings as non-unital `⋆`-algebra homomorphisms.
* `CStarMatrix.single`, `CStarMatrix.singleₙₐ`: matrix units and the `(i, i)`-corner embedding
  `A →⋆ₙₐ[R] CStarMatrix n n A`.
* `CStarMatrix.reindexₗᵢ`: arbitrary finite row-and-column reindexing as a linear isometry
  equivalence.
* `CStarMatrix.permMatrix`, `CStarMatrix.permUnitary`: permutation matrices for equivalences
  `m ≃ n` and unitary permutation matrices for `Equiv.Perm n`.

## Main results

* `CStarMatrix.norm_conjTranspose`, `CStarMatrix.norm_conjTranspose_mul_self`,
  `CStarMatrix.norm_self_mul_conjTranspose`: the operator norm on rectangular `CStarMatrix` is
  invariant under conjugate transpose and satisfies the rectangular C⋆-identities
  `‖Mᴴ * M‖ = ‖M‖ ^ 2` and `‖M * Mᴴ‖ = ‖M‖ ^ 2`.
* `CStarMatrix.mul_conjTranspose_mul_self_of_isIdempotentElem`: over a star-ordered ring with
  proper star (in particular any C⋆-algebra), any rectangular matrix `v` whose `vᴴ * v` is
  idempotent satisfies the partial-isometry identity `v * vᴴ * v = v`.
* `CStarMatrix.norm_fromBlocks_zero`: `‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖` for rectangular
  matrices `M` and `N`.
* `CStarMatrix.norm_single`: `‖single i j a‖ = ‖a‖`.
* `CStarMatrix.permMatrix_mul_mul_conjTranspose`: conjugating by `permMatrix A e` implements
  `reindexₐ R A e`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), Chapter II, §4.6.
* M. Rørdam, F. Larsen, N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, LMS Student
  Texts 49, Cambridge University Press (2000), Chapter 2.
-/

public section

open scoped Matrix InnerProductSpace WithCStarModule

namespace CStarMatrix

section RectangularAlgebra

variable {k l m n R A B C : Type*}

@[simp]
theorem ofMatrix_symm_zero [Zero A] :
    ofMatrix.symm (0 : CStarMatrix m n A) = (0 : Matrix m n A) := (rfl)

@[simp]
theorem ofMatrix_symm_hMul [Fintype m] [Mul A] [AddCommMonoid A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    ofMatrix.symm (M * N) = ofMatrix.symm M * ofMatrix.symm N := (rfl)

@[simp]
theorem ofMatrix_hMul [Fintype m] [Mul A] [AddCommMonoid A]
    (M : Matrix l m A) (N : Matrix m n A) :
    ofMatrix (M * N) = ofMatrix M * ofMatrix N := (rfl)

@[simp]
theorem ofMatrix_symm_conjTranspose [Star A] (M : CStarMatrix m n A) :
    ofMatrix.symm M.conjTranspose = (ofMatrix.symm M)ᴴ := (rfl)

@[simp]
theorem ofMatrix_conjTranspose [Star A] (M : Matrix m n A) :
    ofMatrix Mᴴ = (ofMatrix M).conjTranspose := (rfl)

@[simp]
theorem ofMatrix_one [DecidableEq n] [Zero A] [One A] :
    ofMatrix (1 : Matrix n n A) = (1 : CStarMatrix n n A) := (rfl)

@[simp]
theorem ofMatrix_symm_one [DecidableEq n] [Zero A] [One A] :
    ofMatrix.symm (1 : CStarMatrix n n A) = (1 : Matrix n n A) := (rfl)

@[simp]
theorem conjTranspose_conjTranspose [InvolutiveStar A] (M : CStarMatrix m n A) :
    M.conjTranspose.conjTranspose = M := by
  ext
  simp

@[simp]
theorem conjTranspose_eq_zero [AddMonoid A] [StarAddMonoid A] {M : CStarMatrix m n A} :
    M.conjTranspose = 0 ↔ M = 0 :=
  ⟨fun h => by simpa using congrArg conjTranspose h, fun h => by simp [h]⟩

@[simp]
theorem conjTranspose_add [AddMonoid A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M + N).conjTranspose = M.conjTranspose + N.conjTranspose := by
  ext
  simp

@[simp]
theorem conjTranspose_neg [AddGroup A] [StarAddMonoid A] (M : CStarMatrix m n A) :
    (-M).conjTranspose = -M.conjTranspose := by
  ext
  simp

@[simp]
theorem conjTranspose_sub [AddGroup A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M - N).conjTranspose = M.conjTranspose - N.conjTranspose := by
  ext
  simp

@[simp]
theorem conjTranspose_smul [Star R] [Star A] [SMul R A] [StarModule R A]
    (r : R) (M : CStarMatrix m n A) :
    (r • M).conjTranspose = star r • M.conjTranspose := by
  ext
  simp

@[simp]
theorem conjTranspose_mul [Fintype m] [NonUnitalSemiring A] [StarRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).conjTranspose = N.conjTranspose * M.conjTranspose :=
  ofMatrix.symm.injective (Matrix.conjTranspose_mul (ofMatrix.symm M) (ofMatrix.symm N))

@[simp]
theorem conjTranspose_one [DecidableEq n] [NonAssocSemiring A] [StarRing A] :
    (1 : CStarMatrix n n A).conjTranspose = 1 :=
  ofMatrix.symm.injective Matrix.conjTranspose_one

protected theorem mul_assoc [Fintype l] [Fintype m] [NonUnitalSemiring A]
    (L : CStarMatrix k l A) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    L * M * N = L * (M * N) :=
  ofMatrix.symm.injective (Matrix.mul_assoc (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N))

protected theorem mul_sub [Fintype m] [NonUnitalNonAssocRing A]
    (L : CStarMatrix l m A) (M N : CStarMatrix m n A) :
    L * (M - N) = L * M - L * N :=
  ofMatrix.symm.injective (Matrix.mul_sub (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N))

protected theorem sub_mul [Fintype m] [NonUnitalNonAssocRing A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (L - M) * N = L * N - M * N :=
  ofMatrix.symm.injective (Matrix.sub_mul (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N))

@[simp]
protected theorem one_mul [Fintype m] [DecidableEq m] [NonAssocSemiring A]
    (M : CStarMatrix m n A) :
    (1 : CStarMatrix m m A) * M = M :=
  ofMatrix.symm.injective (Matrix.one_mul (ofMatrix.symm M))

@[simp]
protected theorem mul_one [Fintype n] [DecidableEq n] [NonAssocSemiring A]
    (M : CStarMatrix m n A) :
    M * (1 : CStarMatrix n n A) = M :=
  ofMatrix.symm.injective (Matrix.mul_one (ofMatrix.symm M))

/-- A rectangular matrix over a star-ordered ring with proper star vanishes iff `Mᴴ * M = 0`. -/
@[simp]
theorem conjTranspose_mul_self_eq_zero [Fintype m] [PartialOrder A]
    [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {M : CStarMatrix m n A} :
    M.conjTranspose * M = 0 ↔ M = 0 := by
  simp [← ofMatrix.symm.injective.eq_iff]

/-- A rectangular matrix over a star-ordered ring with proper star vanishes iff `M * Mᴴ = 0`. -/
@[simp]
theorem self_mul_conjTranspose_eq_zero [Fintype n] [PartialOrder A]
    [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {M : CStarMatrix m n A} :
    M * M.conjTranspose = 0 ↔ M = 0 := by
  simpa using conjTranspose_mul_self_eq_zero (M := M.conjTranspose)

/-- Over a star-ordered ring with proper star, any rectangular matrix `v` whose `vᴴ * v` is
idempotent automatically satisfies the partial-isometry identity `v * vᴴ * v = v`. -/
theorem mul_conjTranspose_mul_self_of_isIdempotentElem
    [Fintype m] [Fintype n] [PartialOrder A] [NonUnitalRing A] [StarRing A]
    [StarOrderedRing A] [IsProperStar A] {v : CStarMatrix m n A}
    (hv : IsIdempotentElem (v.conjTranspose * v)) :
    v * v.conjTranspose * v = v := by
  set p := v.conjTranspose * v
  have hp_sa : p.conjTranspose = p := by simp [p]
  rw [CStarMatrix.mul_assoc, ← sub_eq_zero, ← conjTranspose_mul_self_eq_zero]
  calc (v * p - v).conjTranspose * (v * p - v)
      = (p.conjTranspose * v.conjTranspose - v.conjTranspose) * (v * p - v) := by
          rw [conjTranspose_sub, conjTranspose_mul]
    _ = p * (v.conjTranspose * v) * p - p * (v.conjTranspose * v) -
          (v.conjTranspose * v) * p + v.conjTranspose * v := by
          simp only [hp_sa, CStarMatrix.sub_mul, CStarMatrix.mul_sub, CStarMatrix.mul_assoc]
          abel
    _ = 0 := by
          -- Rewrite `v.conjTranspose * v` back to `p` and collapse using idempotence `p * p = p`.
          change p * p * p - p * p - p * p + p = 0
          rw [hv.eq, hv.eq]
          abel

end RectangularAlgebra

section Amplification

variable {m n R A B C : Type*}

@[simp]
theorem map_conjTranspose [Star A] [Star B] (M : CStarMatrix m n A) (f : A → B)
    (hf : ∀ a, f (star a) = star (f a)) :
    (M.map f).conjTranspose = M.conjTranspose.map f := by
  ext
  simp [hf]

@[simp]
theorem map_mul_of_nonUnitalRingHom [Fintype m] {l : Type*}
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B]
    (f : F) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).map f = M.map f * N.map f := by
  ext i k
  simp [mul_apply, map_sum, map_mul]

@[simp]
theorem mapₙₐ_id [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A] :
    mapₙₐ (NonUnitalStarAlgHom.id R A) = NonUnitalStarAlgHom.id R (CStarMatrix n n A) := by
  ext M i j
  rfl

theorem mapₙₐ_comp [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    [NonUnitalNonAssocSemiring C] [Module R C] [Star C]
    (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) :
    mapₙₐ (g.comp f) = (mapₙₐ (n := n) g).comp (mapₙₐ f) := by
  ext M i j
  rfl

/-- Entrywise amplification of a unital `⋆`-algebra homomorphism to square `CStarMatrix`. -/
def mapₐ [Fintype n] [DecidableEq n] [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B] (f : A →⋆ₐ[R] B) :
    CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B where
  __ := mapₙₐ (n := n) f.toNonUnitalStarAlgHom
  map_one' := by
    ext i j
    simp [one_apply]
  commutes' r := by
    ext i j
    simp [Algebra.algebraMap_eq_smul_one, one_apply]

@[simp]
theorem mapₐ_apply [Fintype n] [DecidableEq n] [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
    (f : A →⋆ₐ[R] B) (M : CStarMatrix n n A) :
    mapₐ f M = M.map f := (rfl)

@[simp]
theorem mapₐ_toNonUnitalStarAlgHom [Fintype n] [DecidableEq n] [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
    (f : A →⋆ₐ[R] B) :
    (mapₐ (n := n) f).toNonUnitalStarAlgHom = mapₙₐ f.toNonUnitalStarAlgHom := by
  ext M i j
  simp

@[simp]
theorem mapₐ_id [Fintype n] [DecidableEq n] [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] :
    mapₐ (StarAlgHom.id R A) = StarAlgHom.id R (CStarMatrix n n A) := by
  ext M i j
  simp

theorem mapₐ_comp [Fintype n] [DecidableEq n] [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B]
    [Semiring C] [Algebra R C] [Star C]
    (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    mapₐ (g.comp f) = (mapₐ (n := n) g).comp (mapₐ f) := by
  ext M i j
  simp

end Amplification

section BlocksAndSingle

variable {l m m₁ m₂ n n₁ n₂ o₁ o₂ R A : Type*}

/-- Assemble four `CStarMatrix` blocks into a `(m₁ ⊕ m₂) × (n₁ ⊕ n₂)` matrix. -/
def fromBlocks (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) :
    CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
    (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂))

@[simp]
theorem ofMatrix_symm_fromBlocks (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) :
    ofMatrix.symm (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
        (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂) := (rfl)

@[simp]
theorem ofMatrix_fromBlocks (M₁₁ : Matrix m₁ n₁ A) (M₁₂ : Matrix m₁ n₂ A)
    (M₂₁ : Matrix m₂ n₁ A) (M₂₂ : Matrix m₂ n₂ A) :
    ofMatrix (Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (ofMatrix M₁₁) (ofMatrix M₁₂) (ofMatrix M₂₁) (ofMatrix M₂₂) := (rfl)

@[simp]
theorem fromBlocks_apply₁₁ (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) (i : m₁) (j : n₁) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (.inl i) (.inl j) = M₁₁ i j := (rfl)

@[simp]
theorem fromBlocks_apply₁₂ (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) (i : m₁) (j : n₂) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (.inl i) (.inr j) = M₁₂ i j := (rfl)

@[simp]
theorem fromBlocks_apply₂₁ (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) (i : m₂) (j : n₁) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (.inr i) (.inl j) = M₂₁ i j := (rfl)

@[simp]
theorem fromBlocks_apply₂₂ (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) (i : m₂) (j : n₂) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (.inr i) (.inr j) = M₂₂ i j := (rfl)

theorem fromBlocks_inj {M₁₁ N₁₁ : CStarMatrix m₁ n₁ A} {M₁₂ N₁₂ : CStarMatrix m₁ n₂ A}
    {M₂₁ N₂₁ : CStarMatrix m₂ n₁ A} {M₂₂ N₂₂ : CStarMatrix m₂ n₂ A} :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ ↔
      M₁₁ = N₁₁ ∧ M₁₂ = N₁₂ ∧ M₂₁ = N₂₁ ∧ M₂₂ = N₂₂ := by
  rw [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_fromBlocks, ofMatrix_symm_fromBlocks,
    Matrix.fromBlocks_inj]
  simp [ofMatrix.symm.injective.eq_iff]

@[simp]
theorem fromBlocks_zero [Zero A] :
    fromBlocks (0 : CStarMatrix m₁ n₁ A) (0 : CStarMatrix m₁ n₂ A)
      (0 : CStarMatrix m₂ n₁ A) (0 : CStarMatrix m₂ n₂ A) = 0 :=
  ofMatrix.symm.injective Matrix.fromBlocks_zero

@[simp]
theorem fromBlocks_add [Add A]
    (M₁₁ N₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ N₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ N₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ N₂₂ : CStarMatrix m₂ n₂ A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ + fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ + N₁₁) (M₁₂ + N₁₂) (M₂₁ + N₂₁) (M₂₂ + N₂₂) :=
  ofMatrix.symm.injective <| Matrix.fromBlocks_add _ _ _ _ _ _ _ _

@[simp]
theorem fromBlocks_neg [Neg A]
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) :
    -fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks (-M₁₁) (-M₁₂) (-M₂₁) (-M₂₂) :=
  ofMatrix.symm.injective <| Matrix.fromBlocks_neg _ _ _ _

@[simp]
theorem fromBlocks_sub [Sub A]
    (M₁₁ N₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ N₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ N₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ N₂₂ : CStarMatrix m₂ n₂ A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ - fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ - N₁₁) (M₁₂ - N₁₂) (M₂₁ - N₂₁) (M₂₂ - N₂₂) := by
  ext (i | i) (j | j) <;> rfl

@[simp]
theorem fromBlocks_smul [SMul R A] (r : R)
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) :
    r • fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks (r • M₁₁) (r • M₁₂) (r • M₂₁) (r • M₂₂) :=
  ofMatrix.symm.injective <| Matrix.fromBlocks_smul r _ _ _ _

@[simp]
theorem fromBlocks_conjTranspose [Star A]
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).conjTranspose =
      fromBlocks M₁₁.conjTranspose M₂₁.conjTranspose M₁₂.conjTranspose M₂₂.conjTranspose :=
  ofMatrix.symm.injective <| Matrix.fromBlocks_conjTranspose _ _ _ _

@[simp]
theorem fromBlocks_star [Star A]
    (M₁₁ : CStarMatrix n₁ n₁ A) (M₁₂ : CStarMatrix n₁ n₂ A)
    (M₂₁ : CStarMatrix n₂ n₁ A) (M₂₂ : CStarMatrix n₂ n₂ A) :
    star (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (star M₁₁) M₂₁.conjTranspose M₁₂.conjTranspose (star M₂₂) :=
  fromBlocks_conjTranspose M₁₁ M₁₂ M₂₁ M₂₂

theorem fromBlocks_multiply [Fintype n₁] [Fintype n₂] [NonUnitalNonAssocSemiring A]
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A)
    (N₁₁ : CStarMatrix n₁ o₁ A) (N₁₂ : CStarMatrix n₁ o₂ A)
    (N₂₁ : CStarMatrix n₂ o₁ A) (N₂₂ : CStarMatrix n₂ o₂ A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ * N₁₁ + M₁₂ * N₂₁) (M₁₁ * N₁₂ + M₁₂ * N₂₂)
        (M₂₁ * N₁₁ + M₂₂ * N₂₁) (M₂₁ * N₁₂ + M₂₂ * N₂₂) :=
  ofMatrix.symm.injective <| Matrix.fromBlocks_multiply _ _ _ _ _ _ _ _

@[simp]
theorem fromBlocks_one [DecidableEq n₁] [DecidableEq n₂] [Zero A] [One A] :
    fromBlocks (1 : CStarMatrix n₁ n₁ A) 0 0 (1 : CStarMatrix n₂ n₂ A) = 1 :=
  ofMatrix.symm.injective Matrix.fromBlocks_one

@[simp]
theorem fromBlocks_map {B : Type*}
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) (f : A → B) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).map f =
      fromBlocks (M₁₁.map f) (M₁₂.map f) (M₂₁.map f) (M₂₂.map f) :=
  ofMatrix.symm.injective <| Matrix.fromBlocks_map _ _ _ _ f

/-- Entrywise amplification `mapₙₐ` distributes over `fromBlocks`. -/
theorem mapₙₐ_fromBlocks [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    {B : Type*} [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (f : A →⋆ₙₐ[R] B)
    (M₁₁ : CStarMatrix n₁ n₁ A) (M₁₂ : CStarMatrix n₁ n₂ A)
    (M₂₁ : CStarMatrix n₂ n₁ A) (M₂₂ : CStarMatrix n₂ n₂ A) :
    mapₙₐ f (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (mapₙₐ f M₁₁) (M₁₂.map f) (M₂₁.map f) (mapₙₐ f M₂₂) :=
  fromBlocks_map M₁₁ M₁₂ M₂₁ M₂₂ f

@[simp]
theorem isStarProjection_fromBlocks_zero [Fintype n₁] [Fintype n₂]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix n₁ n₁ A} {q : CStarMatrix n₂ n₂ A} :
    IsStarProjection (fromBlocks p 0 0 q) ↔ IsStarProjection p ∧ IsStarProjection q := by
  simp only [isStarProjection_iff, IsIdempotentElem, IsSelfAdjoint, fromBlocks_multiply,
    fromBlocks_star, CStarMatrix.mul_zero, CStarMatrix.zero_mul, add_zero, zero_add,
    conjTranspose_zero, fromBlocks_inj, true_and]
  tauto

/-- Reindexing a block-diagonal matrix by `Equiv.sumComm` swaps the two diagonal blocks. -/
@[simp]
theorem reindexₗ_sumComm_fromBlocks [Semiring R] [AddCommMonoid A] [Module R A]
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) :
    reindexₗ R A (Equiv.sumComm m₁ m₂) (Equiv.sumComm n₁ n₂) (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks M₂₂ M₂₁ M₁₂ M₁₁ := by
  ext (i | i) (j | j) <;> rfl

/-- Reindexing nested block-diagonal sums by `Equiv.sumAssoc` reassociates the blocks. -/
@[simp]
theorem reindexₗ_sumAssoc_fromBlocks_zero {m₃ n₃ : Type*}
    [Semiring R] [AddCommMonoid A] [Module R A]
    (L : CStarMatrix m₁ n₁ A) (M : CStarMatrix m₂ n₂ A) (N : CStarMatrix m₃ n₃ A) :
    reindexₗ R A (Equiv.sumAssoc m₁ m₂ m₃) (Equiv.sumAssoc n₁ n₂ n₃)
        (fromBlocks (fromBlocks L 0 0 M) 0 0 N) =
      fromBlocks L 0 0 (fromBlocks M 0 0 N) := by
  ext (i | (i | i)) (j | (j | j)) <;> rfl

/-- Block-diagonal sum as a non-unital `⋆`-algebra homomorphism
`CStarMatrix n₁ n₁ A × CStarMatrix n₂ n₂ A →⋆ₙₐ[R] CStarMatrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) A`. -/
def blockDiagₙₐ (R A : Type*) [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n₁ n₁ A × CStarMatrix n₂ n₂ A →⋆ₙₐ[R] CStarMatrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) A where
  toFun x := fromBlocks x.1 0 0 x.2
  map_smul' r x := by simp [smul_zero]
  map_zero' := fromBlocks_zero
  map_add' x y := by simp
  map_mul' x y := by simp [fromBlocks_multiply]
  map_star' x := by simp

@[simp]
theorem blockDiagₙₐ_apply [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (x : CStarMatrix n₁ n₁ A × CStarMatrix n₂ n₂ A) :
    blockDiagₙₐ R A x = fromBlocks x.1 0 0 x.2 := (rfl)

theorem blockDiagₙₐ_injective [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (blockDiagₙₐ (n₁ := n₁) (n₂ := n₂) R A) := by
  rintro ⟨M₁, M₂⟩ ⟨N₁, N₂⟩ h
  obtain ⟨rfl, -, -, rfl⟩ := fromBlocks_inj.mp h
  rfl

/-- Upper-left corner inclusion `M ↦ fromBlocks M 0 0 0` as a non-unital `⋆`-homomorphism. -/
def inlₙₐ (R A : Type*) (n₂ : Type*) [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n₁ n₁ A →⋆ₙₐ[R] CStarMatrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) A where
  toFun M := fromBlocks M 0 0 0
  map_smul' r M := by simp [smul_zero]
  map_zero' := fromBlocks_zero
  map_add' M N := by simp
  map_mul' M N := by simp [fromBlocks_multiply]
  map_star' M := by simp

@[simp]
theorem inlₙₐ_apply [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (M : CStarMatrix n₁ n₁ A) :
    inlₙₐ R A n₂ M = fromBlocks M 0 0 0 := (rfl)

theorem inlₙₐ_injective [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (inlₙₐ (n₁ := n₁) R A n₂) :=
  fun _ _ h => (fromBlocks_inj.mp h).1

/-- Lower-right corner inclusion `N ↦ fromBlocks 0 0 0 N` as a non-unital `⋆`-homomorphism. -/
def inrₙₐ (R A : Type*) (n₁ : Type*) [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n₂ n₂ A →⋆ₙₐ[R] CStarMatrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) A where
  toFun N := fromBlocks 0 0 0 N
  map_smul' r N := by simp [smul_zero]
  map_zero' := fromBlocks_zero
  map_add' M N := by simp
  map_mul' M N := by simp [fromBlocks_multiply]
  map_star' N := by simp

@[simp]
theorem inrₙₐ_apply [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (N : CStarMatrix n₂ n₂ A) :
    inrₙₐ R A n₁ N = fromBlocks 0 0 0 N := (rfl)

theorem inrₙₐ_injective [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (inrₙₐ (n₂ := n₂) R A n₁) :=
  fun _ _ h => (fromBlocks_inj.mp h).2.2.2

/-- The matrix in `CStarMatrix m n A` with `a` at `(i, j)` and `0` elsewhere. -/
def single [DecidableEq m] [DecidableEq n] [Zero A] (i : m) (j : n) (a : A) :
    CStarMatrix m n A :=
  ofMatrix (Matrix.single i j a)

@[simp]
theorem ofMatrix_symm_single [DecidableEq m] [DecidableEq n] [Zero A] (i : m) (j : n) (a : A) :
    ofMatrix.symm (single i j a) = Matrix.single i j a := (rfl)

@[simp]
theorem ofMatrix_single [DecidableEq m] [DecidableEq n] [Zero A] (i : m) (j : n) (a : A) :
    ofMatrix (Matrix.single i j a) = single i j a := (rfl)

@[simp]
theorem single_apply_same [DecidableEq m] [DecidableEq n] [Zero A] (i : m) (j : n) (a : A) :
    single i j a i j = a :=
  Matrix.single_apply_same i j a

@[simp]
theorem single_apply_of_ne [DecidableEq m] [DecidableEq n] [Zero A]
    {i i' : m} {j j' : n} (h : ¬(i = i' ∧ j = j')) (a : A) :
    single i j a i' j' = 0 :=
  Matrix.single_apply_of_ne i j a i' j' h

@[simp]
theorem single_zero [DecidableEq m] [DecidableEq n] [Zero A] (i : m) (j : n) :
    single i j (0 : A) = 0 :=
  ofMatrix.symm.injective <| Matrix.single_zero i j

@[simp]
theorem conjTranspose_single [DecidableEq m] [DecidableEq n] [AddMonoid A] [StarAddMonoid A]
    (i : m) (j : n) (a : A) :
    (single i j a).conjTranspose = single j i (star a) :=
  ofMatrix.symm.injective <| Matrix.conjTranspose_single i j a

@[simp]
theorem single_mul_single_same [Fintype m] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    [NonUnitalNonAssocSemiring A] (i : l) (j : m) (k : n) (a b : A) :
    single i j a * single j k b = single i k (a * b) :=
  ofMatrix.symm.injective <| Matrix.single_mul_single_same a i j k b

theorem single_mul_single_of_ne [Fintype m] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    [NonUnitalNonAssocSemiring A] (i : l) {j j' : m} (k : n) (h : j ≠ j') (a b : A) :
    single i j a * single j' k b = 0 :=
  ofMatrix.symm.injective <| Matrix.single_mul_single_of_ne a i j j' h b

/-- The `(i, i)`-corner embedding `a ↦ single i i a` as a non-unital `⋆`-algebra homomorphism. -/
def singleₙₐ (R : Type*) [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) :
    A →⋆ₙₐ[R] CStarMatrix n n A where
  toFun a := single i i a
  map_smul' r a := ofMatrix.symm.injective (Matrix.smul_single r i i a).symm
  map_zero' := single_zero i i
  map_add' a b := ofMatrix.symm.injective <| Matrix.single_add i i a b
  map_mul' a b := (single_mul_single_same i i i a b).symm
  map_star' a := (conjTranspose_single i i a).symm

@[simp]
theorem singleₙₐ_apply [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) (a : A) :
    singleₙₐ R (A := A) i a = single i i a := (rfl)

theorem singleₙₐ_injective [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) :
    Function.Injective (singleₙₐ R (A := A) i) := by
  intro a b h
  simpa using congrArg (fun M => M i i) h

end BlocksAndSingle

section Permutations

variable {l m n R A : Type*}

@[simp]
theorem reindexₗ_conjTranspose [Semiring R] [AddCommMonoid A] [Module R A] [Star A]
    (eₘ : m ≃ l) {o : Type*} (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    (reindexₗ R A eₘ eₙ M).conjTranspose = reindexₗ R A eₙ eₘ M.conjTranspose := by
  ext
  rfl

theorem reindexₗ_apply_eq {o p : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    (eₘ : m ≃ o) (eₙ : n ≃ p) (M : CStarMatrix m n A) (i : o) (j : p) :
    reindexₗ R A eₘ eₙ M i j = M (eₘ.symm i) (eₙ.symm j) := (rfl)

theorem reindexₗ_mul {o p : Type*} [Fintype m] [Fintype o] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A]
    (eₗ : l ≃ p) (eₘ : m ≃ o) {q : Type*} (eₙ : n ≃ q)
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    reindexₗ R A eₗ eₙ (M * N) = reindexₗ R A eₗ eₘ M * reindexₗ R A eₘ eₙ N := by
  ext i k
  simp only [reindexₗ_apply_eq, mul_apply]
  exact Fintype.sum_equiv eₘ _ _ fun _ => by simp

/-- The permutation matrix in `CStarMatrix n m A` associated to an equivalence `e : m ≃ n`,
whose `(i, j)`-entry is `1` when `e j = i` and `0` otherwise. -/
def permMatrix (A : Type*) [DecidableEq n] [Zero A] [One A] (e : m ≃ n) :
    CStarMatrix n m A :=
  ofMatrix fun i j => if e j = i then 1 else 0

@[simp]
theorem permMatrix_apply [DecidableEq n] [Zero A] [One A] (e : m ≃ n) (i : n) (j : m) :
    permMatrix A e i j = if e j = i then 1 else 0 := (rfl)

@[simp]
theorem permMatrix_refl [DecidableEq n] [Zero A] [One A] :
    permMatrix A (Equiv.refl n) = 1 := by
  ext i j
  simp [one_apply, eq_comm]

@[simp]
theorem conjTranspose_permMatrix [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] [StarRing A] (e : m ≃ n) :
    (permMatrix A e).conjTranspose = permMatrix A e.symm := by
  ext i j
  simp only [conjTranspose_apply, permMatrix_apply]
  by_cases h : e i = j
  · subst h
    simp
  · have h' : e.symm j ≠ i := fun h' => h (by rw [← h', Equiv.apply_symm_apply])
    simp [h, h']

theorem permMatrix_mul [Fintype m] [DecidableEq n] [NonAssocSemiring A]
    (e : m ≃ n) (M : CStarMatrix m l A) :
    permMatrix A e * M = ofMatrix fun i k => M (e.symm i) k := by
  classical
  ext i k
  simp only [mul_apply, permMatrix_apply, ite_mul, one_mul, zero_mul,
    ← e.eq_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

theorem mul_permMatrix [Fintype n] [DecidableEq n] [NonAssocSemiring A]
    (M : CStarMatrix l n A) (e : m ≃ n) :
    M * permMatrix A e = ofMatrix fun i k => M i (e k) := by
  ext i k
  simp only [mul_apply, permMatrix_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rfl

@[simp]
theorem permMatrix_mul_symm [Fintype m] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] (e : m ≃ n) :
    permMatrix A e * permMatrix A e.symm = 1 := by
  rw [permMatrix_mul]
  ext i j
  -- Evaluate `ofMatrix` at `(i, j)` across semireducible `CStarMatrix`.
  change permMatrix A e.symm (e.symm i) j = (1 : CStarMatrix n n A) i j
  simp [one_apply, eq_comm]

@[simp]
theorem permMatrix_symm_mul [Fintype n] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] (e : m ≃ n) :
    permMatrix A e.symm * permMatrix A e = 1 :=
  permMatrix_mul_symm e.symm

/-- Multiplying `permMatrix A e` on the right by its conjugate transpose gives `1`. -/
theorem permMatrix_mul_conjTranspose [Fintype m] [DecidableEq n]
    [NonAssocSemiring A] [StarRing A] (e : m ≃ n) :
    permMatrix A e * (permMatrix A e).conjTranspose = 1 := by
  classical
  rw [conjTranspose_permMatrix, permMatrix_mul_symm]

/-- Multiplying `permMatrix A e` on the left by its conjugate transpose gives `1`. -/
theorem conjTranspose_permMatrix_mul [Fintype n] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] [StarRing A] (e : m ≃ n) :
    (permMatrix A e).conjTranspose * permMatrix A e = 1 := by
  rw [conjTranspose_permMatrix, permMatrix_symm_mul]

/-- Conjugating a matrix by `permMatrix A e` implements `reindexₐ R A e`. -/
theorem permMatrix_mul_mul_conjTranspose [Fintype m] [Fintype n] [DecidableEq n]
    [Semiring R] [NonAssocSemiring A] [StarRing A] [Module R A]
    (e : m ≃ n) (M : CStarMatrix m m A) :
    permMatrix A e * M * (permMatrix A e).conjTranspose = reindexₐ R A e M := by
  classical
  rw [conjTranspose_permMatrix, permMatrix_mul, mul_permMatrix]
  ext i j
  rfl

/-- The unitary permutation matrix in `unitary (CStarMatrix n n A)` attached to a permutation
`σ : Equiv.Perm n`. -/
def permUnitary (A : Type*) [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
    (σ : Equiv.Perm n) : unitary (CStarMatrix n n A) :=
  ⟨permMatrix A σ, Unitary.mem_iff.mpr
    ⟨conjTranspose_permMatrix_mul (A := A) σ, permMatrix_mul_conjTranspose (A := A) σ⟩⟩

@[simp]
theorem coe_permUnitary [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
    (σ : Equiv.Perm n) :
    (permUnitary A σ : CStarMatrix n n A) = permMatrix A σ := (rfl)

/-- Conjugating a square `CStarMatrix` by `permUnitary A σ` implements `reindexₐ R A σ`. -/
theorem permUnitary_mul_mul_star [Fintype n] [DecidableEq n] [Semiring R]
    [Semiring A] [StarRing A] [Module R A] (σ : Equiv.Perm n) (M : CStarMatrix n n A) :
    (permUnitary A σ : CStarMatrix n n A) * M * star (permUnitary A σ : CStarMatrix n n A) =
      reindexₐ R A σ M :=
  permMatrix_mul_mul_conjTranspose (R := R) σ M

end Permutations

section RectangularNorm

variable {l m m₁ m₂ n n₁ n₂ o A B : Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Multiplication of rectangular `CStarMatrix` corresponds to reversed composition of `toCLM`. -/
theorem toCLM_mul [Fintype l] [Fintype m]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    toCLM (M * N) = (toCLM N).comp (toCLM M) := by
  ext v j
  simp only [ContinuousLinearMap.comp_apply, toCLM_apply_eq_sum,
    WithCStarModule.equiv_symm_pi_apply, mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- Submultiplicativity of the operator norm for rectangular `CStarMatrix`. -/
theorem norm_mul_le [Fintype l] [Fintype m] [Fintype n]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    ‖M * N‖ ≤ ‖M‖ * ‖N‖ := by
  rw [norm_def, norm_def, norm_def, toCLM_mul, mul_comm]
  exact ContinuousLinearMap.opNorm_comp_le (toCLM N) (toCLM M)

private theorem norm_sq_le_norm_mul_conjTranspose [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) :
    ‖M‖ ^ 2 ≤ ‖M * M.conjTranspose‖ := by
  have hinner (v : C⋆ᵐᵒᵈ(A, m → A)) :
      ⟪toCLM M v, toCLM M v⟫_A = ⟪v, toCLM (M * M.conjTranspose) v⟫_A := by
    rw [toCLM_mul, ContinuousLinearMap.comp_apply]
    simp only [toCLM_apply_eq_sum, WithCStarModule.pi_inner,
      WithCStarModule.equiv_symm_pi_apply, WithCStarModule.inner_def, conjTranspose_apply,
      Finset.mul_sum, star_sum, star_mul, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have hle : ‖M‖ ≤ √‖M * M.conjTranspose‖ := by
    rw [norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A), hinner]
    have h₁ : ‖⟪v, toCLM (M * M.conjTranspose) v⟫_A‖ ≤ ‖M * M.conjTranspose‖ * ‖v‖ ^ 2 :=
      calc ‖⟪v, toCLM (M * M.conjTranspose) v⟫_A‖
          ≤ ‖v‖ * ‖toCLM (M * M.conjTranspose) v‖ := CStarModule.norm_inner_le _
        _ ≤ ‖v‖ * (‖toCLM (M * M.conjTranspose)‖ * ‖v‖) := by
            gcongr
            exact (toCLM (M * M.conjTranspose)).le_opNorm v
        _ = ‖M * M.conjTranspose‖ * ‖v‖ ^ 2 := by
            rw [← norm_def]
            ring
    calc √‖⟪v, toCLM (M * M.conjTranspose) v⟫_A‖
        ≤ √(‖M * M.conjTranspose‖ * ‖v‖ ^ 2) := Real.sqrt_le_sqrt h₁
      _ = √‖M * M.conjTranspose‖ * ‖v‖ := by
          rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have hsq := (sq_le_sq₀ (norm_nonneg M) (Real.sqrt_nonneg _)).mpr hle
  rwa [Real.sq_sqrt (norm_nonneg _)] at hsq

private theorem norm_le_norm_conjTranspose [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M‖ ≤ ‖M.conjTranspose‖ := by
  obtain h0 | hpos := eq_or_lt_of_le (norm_nonneg M)
  · rw [← h0]
    exact norm_nonneg _
  · refine le_of_mul_le_mul_left ?_ hpos
    simpa only [sq] using (norm_sq_le_norm_mul_conjTranspose M).trans (norm_mul_le M _)

/-- The operator norm on rectangular `CStarMatrix` is invariant under conjugate transpose. -/
@[simp]
theorem norm_conjTranspose [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ = ‖M‖ :=
  le_antisymm
    (by simpa only [conjTranspose_conjTranspose] using norm_le_norm_conjTranspose M.conjTranspose)
    (norm_le_norm_conjTranspose M)

/-- The rectangular C⋆-identity `‖M * Mᴴ‖ = ‖M‖ ^ 2`. -/
@[simp]
theorem norm_self_mul_conjTranspose [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M * M.conjTranspose‖ = ‖M‖ ^ 2 := by
  refine le_antisymm ?_ (norm_sq_le_norm_mul_conjTranspose M)
  calc ‖M * M.conjTranspose‖ ≤ ‖M‖ * ‖M.conjTranspose‖ := norm_mul_le M M.conjTranspose
    _ = ‖M‖ ^ 2 := by rw [norm_conjTranspose, sq]

/-- The rectangular C⋆-identity `‖Mᴴ * M‖ = ‖M‖ ^ 2`. -/
@[simp]
theorem norm_conjTranspose_mul_self [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose * M‖ = ‖M‖ ^ 2 := by
  simpa using norm_self_mul_conjTranspose M.conjTranspose

/-- Entrywise application of a `⋆`-homomorphism to a rectangular `CStarMatrix` is
norm-contractive. -/
theorem norm_map_le [Fintype m] [Fintype n]
    {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (f : F) (M : CStarMatrix m n A) :
    ‖M.map f‖ ≤ ‖M‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_conjTranspose_mul_self,
    ← norm_conjTranspose_mul_self M]
  have h : (M.map f).conjTranspose * M.map f =
      mapₙₐ (.ofClass f : A →⋆ₙₐ[ℂ] B) (M.conjTranspose * M) := by
    rw [map_conjTranspose M f (map_star f), ← map_mul_of_nonUnitalRingHom f]
    rfl
  rw [h]
  exact NonUnitalStarAlgHom.norm_apply_le (mapₙₐ (.ofClass f : A →⋆ₙₐ[ℂ] B)) (M.conjTranspose * M)

/-- Entrywise application of an injective `⋆`-homomorphism to a rectangular `CStarMatrix` is
isometric. -/
theorem norm_map_of_injective [Fintype m] [Fintype n]
    {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    {f : F} (hf : Function.Injective f) (M : CStarMatrix m n A) :
    ‖M.map f‖ = ‖M‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_conjTranspose_mul_self,
    ← norm_conjTranspose_mul_self M]
  have h : (M.map f).conjTranspose * M.map f =
      mapₙₐ (.ofClass f : A →⋆ₙₐ[ℂ] B) (M.conjTranspose * M) := by
    rw [map_conjTranspose M f (map_star f), ← map_mul_of_nonUnitalRingHom f]
    rfl
  rw [h]
  exact NonUnitalStarAlgHom.norm_map (mapₙₐ (.ofClass f : A →⋆ₙₐ[ℂ] B)) (map_injective hf)
    (M.conjTranspose * M)

@[simp]
theorem norm_reindexₐ [Fintype m] [Fintype n] (e : m ≃ n) (M : CStarMatrix m m A) :
    ‖reindexₐ ℂ A e M‖ = ‖M‖ :=
  StarAlgEquiv.norm_map (reindexₐ ℂ A e) M

@[simp]
theorem norm_reindexₗ [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    ‖reindexₗ ℂ A eₘ eₙ M‖ = ‖M‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_conjTranspose_mul_self,
    ← norm_conjTranspose_mul_self M]
  have h : (reindexₗ ℂ A eₘ eₙ M).conjTranspose * reindexₗ ℂ A eₘ eₙ M =
      reindexₐ ℂ A eₙ (M.conjTranspose * M) := by
    rw [reindexₗ_conjTranspose, ← reindexₗ_mul]
    rfl
  rw [h, norm_reindexₐ]

/-- Arbitrary finite row-and-column reindexing of `CStarMatrix` as a linear isometry equivalence. -/
noncomputable def reindexₗᵢ (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) :
    CStarMatrix m n A ≃ₗᵢ[ℂ] CStarMatrix l o A :=
  { reindexₗ ℂ A eₘ eₙ with
    norm_map' := norm_reindexₗ eₘ eₙ }

@[simp]
theorem coe_reindexₗᵢ [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) :
    ⇑(reindexₗᵢ A eₘ eₙ) = reindexₗ ℂ A eₘ eₙ := (rfl)

@[simp]
theorem reindexₗᵢ_symm [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) :
    (reindexₗᵢ A eₘ eₙ).symm = reindexₗᵢ A eₘ.symm eₙ.symm := by
  ext
  rfl

private theorem norm_fromBlocks_zero_sq [Fintype n₁] [Fintype n₂]
    (X : CStarMatrix n₁ n₁ A) (Y : CStarMatrix n₂ n₂ A) :
    ‖fromBlocks X (0 : CStarMatrix n₁ n₂ A) (0 : CStarMatrix n₂ n₁ A) Y‖ = max ‖X‖ ‖Y‖ :=
  (NonUnitalStarAlgHom.norm_map (blockDiagₙₐ ℂ A) blockDiagₙₐ_injective (X, Y)).trans rfl

/-- The operator norm of a block-diagonal `CStarMatrix` is the maximum of the norms of its
diagonal blocks. -/
@[simp]
theorem norm_fromBlocks_zero [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]
    (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₂ n₂ A) :
    ‖fromBlocks M (0 : CStarMatrix m₁ n₂ A) (0 : CStarMatrix m₂ n₁ A) N‖ = max ‖M‖ ‖N‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (le_max_iff.mpr (.inl (norm_nonneg M))),
    ← norm_conjTranspose_mul_self]
  simp only [fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply,
    CStarMatrix.mul_zero, CStarMatrix.zero_mul, add_zero, zero_add]
  rw [norm_fromBlocks_zero_sq, norm_conjTranspose_mul_self, norm_conjTranspose_mul_self]
  rcases le_total ‖M‖ ‖N‖ with h | h
  · rw [max_eq_right h, max_eq_right ((sq_le_sq₀ (norm_nonneg M) (norm_nonneg N)).mpr h)]
  · rw [max_eq_left h, max_eq_left ((sq_le_sq₀ (norm_nonneg N) (norm_nonneg M)).mpr h)]

/-- Every matrix unit `single i j a` has operator norm `‖a‖`. -/
@[simp]
theorem norm_single [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (i : m) (j : n) (a : A) :
    ‖single i j a‖ = ‖a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_conjTranspose_mul_self,
    conjTranspose_single, single_mul_single_same, sq, ← CStarRing.norm_star_mul_self]
  exact NonUnitalStarAlgHom.norm_map (singleₙₐ ℂ j) (singleₙₐ_injective j) (star a * a)

end RectangularNorm

end CStarMatrix
