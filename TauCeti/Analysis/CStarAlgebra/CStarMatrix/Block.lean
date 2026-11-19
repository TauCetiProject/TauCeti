/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
public import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.LinearAlgebra.Matrix.DotProduct
import TauCeti.Algebra.Star.PartialIsometry

/-!
# Rectangular C⋆-norm, block sums, corner inclusions, and reindexing for `CStarMatrix`

Mathlib constructs the operator norm on rectangular matrices `CStarMatrix m n A` over a non-unital
C⋆-algebra `A` and establishes the `CStarRing` structure in the square case `m = n`. Operator
K-theory works systematically with rectangular matrices between finite index sets of different
cardinalities, block-diagonal direct sums over `m ⊕ n`, corner embeddings, entrywise amplifications
of `⋆`-homomorphisms, and finite reindexings. This file develops that calculus together with all
accompanying norm and star identities.

## Main definitions

* `CStarMatrix.mapₐ`: entrywise amplification of a unital `⋆`-algebra homomorphism `A →⋆ₐ[R] B`
  to `CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B`.
* `CStarMatrix.fromBlocks`: `2 × 2` block matrices `CStarMatrix (m ⊕ n) (l ⊕ o) A`.
* `CStarMatrix.blockDiagHom`: the orthogonal block-diagonal embedding
  `CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[ℂ] CStarMatrix (m ⊕ n) (m ⊕ n) A`.
* `CStarMatrix.inlCorner`, `CStarMatrix.inrCorner`, `CStarMatrix.singleCorner`: top-left block,
  bottom-right block, and `(i, i)`-entry corner embeddings as non-unital `⋆`-algebra homomorphisms.
* `CStarMatrix.permMatrix`, `CStarMatrix.permUnitary`: rectangular equivalence matrices and square
  permutation unitaries implementing `CStarMatrix.reindexₐ` by conjugation.

## Main results

* `CStarMatrix.toCLM_mul`, `CStarMatrix.norm_mul_le`: rectangular matrix multiplication corresponds
  to operator composition in reverse order and is submultiplicative in operator norm.
* `CStarMatrix.norm_conjTranspose`, `CStarMatrix.norm_mul_conjTranspose_self`,
  `CStarMatrix.norm_conjTranspose_mul_self`: the C⋆-identities `‖M.conjTranspose‖ = ‖M‖` and
  `‖M * M.conjTranspose‖ = ‖M.conjTranspose * M‖ = ‖M‖ ^ 2` for rectangular `M : CStarMatrix m n A`.
* `CStarMatrix.mul_conjTranspose_mul_self_of_isIdempotentElem`,
  `CStarMatrix.isStarProjection_mul_conjTranspose_self_of_isIdempotentElem`: if
  `v.conjTranspose * v` is idempotent for rectangular `v : CStarMatrix m n A`, then
  `v * v.conjTranspose * v = v` and `v * v.conjTranspose` is a star projection.
* `CStarMatrix.norm_fromBlocks_zero₁₂_zero₂₁`: exact block-diagonal C⋆-norm identity
  `‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖` for arbitrary rectangular blocks `M` and `N`.
* `CStarMatrix.norm_inlCorner`, `CStarMatrix.norm_inrCorner`, `CStarMatrix.norm_singleCorner`,
  `CStarMatrix.norm_reindexₗ`, `CStarMatrix.norm_mapₙₐ`: corner inclusions, finite reindexings, and
  amplifications of injective `⋆`-homomorphisms are isometries.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), §3.4 and §4.6.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, London Mathematical
  Society Lecture Note Series 210, Cambridge University Press (1995), Chapter 4.
-/

public section

open Matrix
open scoped ComplexOrder NNReal InnerProductSpace WithCStarModule

namespace CStarMatrix

section RectangularAlgebra

variable {k l m n o R A B : Type*}

/-- Reading the zero `CStarMatrix` as an ordinary matrix gives `0`. -/
@[simp]
theorem ofMatrix_symm_zero [Zero A] :
    ofMatrix.symm (0 : CStarMatrix m n A) = 0 :=
  (rfl)

/-- Reading the identity `CStarMatrix` as an ordinary matrix gives `1`. -/
@[simp]
theorem ofMatrix_symm_one [DecidableEq n] [Zero A] [One A] :
    ofMatrix.symm (1 : CStarMatrix n n A) = 1 :=
  (rfl)

/-- Reading a difference of `CStarMatrix`es as an ordinary matrix respects subtraction. -/
@[simp]
theorem ofMatrix_symm_sub [Sub A] (M N : CStarMatrix m n A) :
    ofMatrix.symm (M - N) = ofMatrix.symm M - ofMatrix.symm N :=
  (rfl)

/-- `ofMatrix` commutes with rectangular matrix multiplication. -/
@[simp]
theorem of_mul_of [Fintype m] [Mul A] [AddCommMonoid A]
    (M : Matrix l m A) (N : Matrix m n A) :
    ofMatrix M * ofMatrix N = ofMatrix (M * N) :=
  (rfl)

/-- Reading `M.conjTranspose` as an ordinary matrix gives `(ofMatrix.symm M)ᴴ`. -/
@[simp]
theorem ofMatrix_symm_conjTranspose [Star A] (M : CStarMatrix m n A) :
    ofMatrix.symm M.conjTranspose = (ofMatrix.symm M)ᴴ :=
  (rfl)

/-- `ofMatrix` commutes with conjugate transpose. -/
@[simp]
theorem of_conjTranspose [Star A] (M : Matrix m n A) :
    (ofMatrix M).conjTranspose = ofMatrix Mᴴ :=
  (rfl)

/-- Conjugate transpose is involutive on rectangular matrices. -/
@[simp]
theorem conjTranspose_conjTranspose [InvolutiveStar A] (M : CStarMatrix m n A) :
    M.conjTranspose.conjTranspose = M := by
  ext i j
  simp

/-- Conjugate transpose preserves addition. -/
@[simp]
theorem conjTranspose_add [AddMonoid A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M + N).conjTranspose = M.conjTranspose + N.conjTranspose := by
  ext i j
  simp

/-- Conjugate transpose commutes with negation. -/
@[simp]
theorem conjTranspose_neg [AddGroup A] [StarAddMonoid A] (M : CStarMatrix m n A) :
    (-M).conjTranspose = -M.conjTranspose := by
  ext i j
  simp

/-- Conjugate transpose preserves subtraction. -/
@[simp]
theorem conjTranspose_sub [AddGroup A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M - N).conjTranspose = M.conjTranspose - N.conjTranspose := by
  ext i j
  simp

/-- Conjugate transpose is conjugate-linear with respect to scalar multiplication. -/
@[simp]
theorem conjTranspose_smul [Star R] [Star A] [SMul R A] [StarModule R A]
    (r : R) (M : CStarMatrix m n A) :
    (r • M).conjTranspose = star r • M.conjTranspose := by
  ext i j
  simp

/-- Conjugate transpose reverses rectangular matrix products. -/
@[simp]
theorem conjTranspose_mul [Fintype m] [NonUnitalNonAssocSemiring A] [StarRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).conjTranspose = N.conjTranspose * M.conjTranspose := by
  ext i j
  simp [mul_apply]

/-- Conjugate transpose of the identity matrix is the identity matrix. -/
@[simp]
theorem conjTranspose_one [DecidableEq n] [Semiring A] [StarRing A] :
    (1 : CStarMatrix n n A).conjTranspose = 1 :=
  ofMatrix.symm.injective Matrix.conjTranspose_one

/-- Rectangular matrix multiplication is associative. -/
protected theorem mul_assoc [Fintype l] [Fintype m] [NonUnitalSemiring A]
    (L : CStarMatrix k l A) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    L * M * N = L * (M * N) :=
  ofMatrix.symm.injective (Matrix.mul_assoc (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N))

/-- Left negation commutes with rectangular matrix multiplication. -/
@[simp]
protected theorem neg_mul [Fintype m] [NonUnitalRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (-M) * N = -(M * N) :=
  ofMatrix.symm.injective (Matrix.neg_mul (ofMatrix.symm M) (ofMatrix.symm N))

/-- Right negation commutes with rectangular matrix multiplication. -/
@[simp]
protected theorem mul_neg [Fintype m] [NonUnitalRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    M * (-N) = -(M * N) :=
  ofMatrix.symm.injective (Matrix.mul_neg (ofMatrix.symm M) (ofMatrix.symm N))

/-- Left multiplication distributes over subtraction for rectangular matrices. -/
protected theorem mul_sub [Fintype m] [NonUnitalRing A]
    (L : CStarMatrix l m A) (M N : CStarMatrix m n A) :
    L * (M - N) = L * M - L * N :=
  ofMatrix.symm.injective (Matrix.mul_sub (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N))

/-- Right multiplication distributes over subtraction for rectangular matrices. -/
protected theorem sub_mul [Fintype m] [NonUnitalRing A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (L - M) * N = L * N - M * N :=
  ofMatrix.symm.injective (Matrix.sub_mul (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N))

/-- Right multiplication by `1` fixes rectangular matrices. -/
@[simp]
protected theorem mul_one [Fintype n] [DecidableEq n] [Semiring A] (M : CStarMatrix m n A) :
    M * (1 : CStarMatrix n n A) = M :=
  ofMatrix.symm.injective (Matrix.mul_one (ofMatrix.symm M))

/-- Left multiplication by `1` fixes rectangular matrices. -/
@[simp]
protected theorem one_mul [Fintype m] [DecidableEq m] [Semiring A] (M : CStarMatrix m n A) :
    (1 : CStarMatrix m m A) * M = M :=
  ofMatrix.symm.injective (Matrix.one_mul (ofMatrix.symm M))

end RectangularAlgebra

section Amplification

variable {l m n R A B C : Type*}

/-- Entrywise application of a non-unital `⋆`-algebra homomorphism commutes with `conjTranspose`
on rectangular matrices. -/
theorem mapₗ_conjTranspose [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (f : A →⋆ₙₐ[R] B)
    (M : CStarMatrix m n A) :
    (M.conjTranspose).mapₗ (f : A →ₗ[R] B) = (M.mapₗ (f : A →ₗ[R] B)).conjTranspose := by
  ext i j
  simp [map_star]

/-- Entrywise application of a non-unital `⋆`-algebra homomorphism distributes over rectangular
matrix multiplication. -/
theorem mapₗ_mul [Fintype m] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (f : A →⋆ₙₐ[R] B)
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).mapₗ (f : A →ₗ[R] B) = M.mapₗ (f : A →ₗ[R] B) * N.mapₗ (f : A →ₗ[R] B) := by
  ext i j
  simp [mul_apply]

/-- `mapₙₐ` sends the identity homomorphism to the identity homomorphism. -/
@[simp]
theorem mapₙₐ_id [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A] :
    mapₙₐ (NonUnitalStarAlgHom.id R A) = NonUnitalStarAlgHom.id R (CStarMatrix n n A) := by
  ext M i j
  simp

/-- `mapₙₐ` preserves composition of non-unital `⋆`-algebra homomorphisms. -/
@[simp]
theorem mapₙₐ_comp [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    [NonUnitalNonAssocSemiring C] [Module R C] [Star C]
    (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) :
    (mapₙₐ (g.comp f) : CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix n n C) =
      (mapₙₐ g).comp (mapₙₐ f) := by
  ext M i j
  simp

/-- Amplification `mapₙₐ f` of an injective homomorphism `f` is injective. -/
theorem mapₙₐ_injective [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B] {f : A →⋆ₙₐ[R] B}
    (hf : Function.Injective f) :
    Function.Injective (mapₙₐ f : CStarMatrix n n A → CStarMatrix n n B) :=
  map_injective hf

/-- Entrywise amplification of a unital `⋆`-algebra homomorphism `A →⋆ₐ[R] B` to square matrices
`CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B`. -/
def mapₐ [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B] (f : A →⋆ₐ[R] B) :
    CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B where
  __ := mapₙₐ f.toNonUnitalStarAlgHom
  map_one' := by
    ext i j
    by_cases h : i = j <;> simp [one_apply, h]
  commutes' r := by
    ext i j
    by_cases h : i = j <;> simp [algebraMap_apply, h, AlgHomClass.commutes]

/-- Entrywise formula for `CStarMatrix.mapₐ`. -/
@[simp]
theorem mapₐ_apply [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B] (f : A →⋆ₐ[R] B) (M : CStarMatrix n n A) (i j : n) :
    mapₐ f M i j = f (M i j) :=
  (rfl)

/-- Forgetting unitality of `mapₐ f` recovers `mapₙₐ f.toNonUnitalStarAlgHom`. -/
@[simp]
theorem toNonUnitalStarAlgHom_mapₐ [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A]
    [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B] (f : A →⋆ₐ[R] B) :
    (mapₐ f : CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B).toNonUnitalStarAlgHom =
      mapₙₐ f.toNonUnitalStarAlgHom :=
  (rfl)

/-- `mapₐ` sends the identity homomorphism to the identity homomorphism. -/
@[simp]
theorem mapₐ_id [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] [Star A] :
    mapₐ (StarAlgHom.id R A) = StarAlgHom.id R (CStarMatrix n n A) := by
  ext M i j
  rfl

/-- `mapₐ` preserves composition of unital `⋆`-algebra homomorphisms. -/
@[simp]
theorem mapₐ_comp [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C]
    (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    (mapₐ (g.comp f) : CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n C) =
      (mapₐ g).comp (mapₐ f) := by
  ext M i j
  rfl

/-- Amplification `mapₐ f` of an injective unital `⋆`-homomorphism `f` is injective. -/
theorem mapₐ_injective [Fintype n] [DecidableEq n] [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B] {f : A →⋆ₐ[R] B}
    (hf : Function.Injective f) :
    Function.Injective (mapₐ f : CStarMatrix n n A → CStarMatrix n n B) :=
  map_injective hf

end Amplification

section BlocksAndReindex

variable {k l m n o p R A B : Type*}

/-- Assemble four blocks into a `(m ⊕ n) × (l ⊕ o)` `CStarMatrix`. -/
def fromBlocks (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m o A)
    (M₂₁ : CStarMatrix n l A) (M₂₂ : CStarMatrix n o A) : CStarMatrix (m ⊕ n) (l ⊕ o) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
    (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂))

/-- Reading `CStarMatrix.fromBlocks` as an ordinary matrix gives `Matrix.fromBlocks`. -/
@[simp]
theorem ofMatrix_symm_fromBlocks (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m o A)
    (M₂₁ : CStarMatrix n l A) (M₂₂ : CStarMatrix n o A) :
    ofMatrix.symm (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
        (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂) :=
  (rfl)

/-- Top-left `(Sum.inl i, Sum.inl j)` entry of `fromBlocks`. -/
@[simp]
theorem fromBlocks_apply₁₁ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m o A)
    (M₂₁ : CStarMatrix n l A) (M₂₂ : CStarMatrix n o A) (i : m) (j : l) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inl j) = M₁₁ i j :=
  (rfl)

/-- Top-right `(Sum.inl i, Sum.inr j)` entry of `fromBlocks`. -/
@[simp]
theorem fromBlocks_apply₁₂ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m o A)
    (M₂₁ : CStarMatrix n l A) (M₂₂ : CStarMatrix n o A) (i : m) (j : o) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inr j) = M₁₂ i j :=
  (rfl)

/-- Bottom-left `(Sum.inr i, Sum.inl j)` entry of `fromBlocks`. -/
@[simp]
theorem fromBlocks_apply₂₁ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m o A)
    (M₂₁ : CStarMatrix n l A) (M₂₂ : CStarMatrix n o A) (i : n) (j : l) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inl j) = M₂₁ i j :=
  (rfl)

/-- Bottom-right `(Sum.inr i, Sum.inr j)` entry of `fromBlocks`. -/
@[simp]
theorem fromBlocks_apply₂₂ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m o A)
    (M₂₁ : CStarMatrix n l A) (M₂₂ : CStarMatrix n o A) (i : n) (j : o) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inr j) = M₂₂ i j :=
  (rfl)

/-- `fromBlocks` of four zero blocks is the zero matrix. -/
@[simp]
theorem fromBlocks_zero [Zero A] :
    fromBlocks (0 : CStarMatrix m l A) (0 : CStarMatrix m o A)
      (0 : CStarMatrix n l A) (0 : CStarMatrix n o A) = 0 := by
  ext (i | i) (j | j) <;> rfl

/-- `fromBlocks 1 0 0 1` is the identity matrix. -/
@[simp]
theorem fromBlocks_one [DecidableEq m] [DecidableEq n] [Zero A] [One A] :
    fromBlocks (1 : CStarMatrix m m A) 0 0 (1 : CStarMatrix n n A) = 1 :=
  ofMatrix.symm.injective Matrix.fromBlocks_one

/-- `fromBlocks` commutes with matrix addition. -/
@[simp]
theorem fromBlocks_add [Add A]
    (M₁₁ N₁₁ : CStarMatrix m l A) (M₁₂ N₁₂ : CStarMatrix m o A)
    (M₂₁ N₂₁ : CStarMatrix n l A) (M₂₂ N₂₂ : CStarMatrix n o A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ + fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ + N₁₁) (M₁₂ + N₁₂) (M₂₁ + N₂₁) (M₂₂ + N₂₂) := by
  ext (i | i) (j | j) <;> rfl

/-- `fromBlocks` commutes with matrix negation. -/
@[simp]
theorem fromBlocks_neg [Neg A]
    (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m o A)
    (M₂₁ : CStarMatrix n l A) (M₂₂ : CStarMatrix n o A) :
    -fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks (-M₁₁) (-M₁₂) (-M₂₁) (-M₂₂) := by
  ext (i | i) (j | j) <;> rfl

/-- `fromBlocks` commutes with matrix subtraction. -/
@[simp]
theorem fromBlocks_sub [Sub A]
    (M₁₁ N₁₁ : CStarMatrix m l A) (M₁₂ N₁₂ : CStarMatrix m o A)
    (M₂₁ N₂₁ : CStarMatrix n l A) (M₂₂ N₂₂ : CStarMatrix n o A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ - fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ - N₁₁) (M₁₂ - N₁₂) (M₂₁ - N₂₁) (M₂₂ - N₂₂) := by
  ext (i | i) (j | j) <;> rfl

/-- `fromBlocks` commutes with scalar multiplication. -/
@[simp]
theorem fromBlocks_smul [SMul R A] (r : R)
    (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m o A)
    (M₂₁ : CStarMatrix n l A) (M₂₂ : CStarMatrix n o A) :
    r • fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ =
      fromBlocks (r • M₁₁) (r • M₁₂) (r • M₂₁) (r • M₂₂) := by
  ext (i | i) (j | j) <;> rfl

/-- Block-by-block multiplication formula for `CStarMatrix.fromBlocks`. -/
@[simp]
theorem fromBlocks_mul [Fintype l] [Fintype o] [NonUnitalNonAssocSemiring A]
    (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m o A)
    (M₂₁ : CStarMatrix n l A) (M₂₂ : CStarMatrix n o A)
    (N₁₁ : CStarMatrix l k A) (N₁₂ : CStarMatrix l p A)
    (N₂₁ : CStarMatrix o k A) (N₂₂ : CStarMatrix o p A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ * N₁₁ + M₁₂ * N₂₁) (M₁₁ * N₁₂ + M₁₂ * N₂₂)
        (M₂₁ * N₁₁ + M₂₂ * N₂₁) (M₂₁ * N₁₂ + M₂₂ * N₂₂) :=
  ofMatrix.symm.injective (Matrix.fromBlocks_multiply _ _ _ _ _ _ _ _)

/-- Conjugate transpose of a `2 × 2` block matrix transposes the block layout and takes
`conjTranspose` of each block. -/
@[simp]
theorem conjTranspose_fromBlocks [Star A]
    (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m o A)
    (M₂₁ : CStarMatrix n l A) (M₂₂ : CStarMatrix n o A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).conjTranspose =
      fromBlocks M₁₁.conjTranspose M₂₁.conjTranspose M₁₂.conjTranspose M₂₂.conjTranspose :=
  ofMatrix.symm.injective (Matrix.fromBlocks_conjTranspose _ _ _ _)

/-- Star of a square `2 × 2` block matrix. -/
@[simp]
theorem star_fromBlocks [Star A]
    (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix n m A) (M₂₂ : CStarMatrix n n A) :
    star (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (star M₁₁) M₂₁.conjTranspose M₁₂.conjTranspose (star M₂₂) :=
  conjTranspose_fromBlocks M₁₁ M₁₂ M₂₁ M₂₂

/-- `mapₙₐ` distributes across `fromBlocks`. -/
theorem mapₙₐ_fromBlocks [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (f : A →⋆ₙₐ[R] B)
    (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix n m A) (M₂₂ : CStarMatrix n n A) :
    mapₙₐ f (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (mapₙₐ f M₁₁) (M₁₂.mapₗ (f : A →ₗ[R] B))
        (M₂₁.mapₗ (f : A →ₗ[R] B)) (mapₙₐ f M₂₂) := by
  ext (i | i) (j | j) <;> rfl

/-- Two block matrices are equal iff all four blocks are equal. -/
theorem fromBlocks_inj {M₁₁ N₁₁ : CStarMatrix m l A} {M₁₂ N₁₂ : CStarMatrix m o A}
    {M₂₁ N₂₁ : CStarMatrix n l A} {M₂₂ N₂₂ : CStarMatrix n o A} :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ ↔
      M₁₁ = N₁₁ ∧ M₁₂ = N₁₂ ∧ M₂₁ = N₂₁ ∧ M₂₂ = N₂₂ := by
  simp only [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_fromBlocks, Matrix.fromBlocks_inj]

/-- A block-diagonal matrix `fromBlocks P 0 0 Q` is a star projection iff both `P` and `Q` are. -/
@[simp]
theorem isStarProjection_fromBlocks [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A]
    [StarAddMonoid A] {P : CStarMatrix m m A} {Q : CStarMatrix n n A} :
    IsStarProjection (fromBlocks P 0 0 Q) ↔ IsStarProjection P ∧ IsStarProjection Q := by
  simp only [isStarProjection_iff, IsIdempotentElem, isSelfAdjoint_iff, fromBlocks_mul,
    CStarMatrix.mul_zero, CStarMatrix.zero_mul, add_zero, zero_add, star_fromBlocks,
    conjTranspose_zero, fromBlocks_inj, true_and]
  tauto

/-- Orthogonal block-diagonal embedding `(P, Q) ↦ fromBlocks P 0 0 Q` as a non-unital `⋆`-algebra
homomorphism. -/
def blockDiagHom [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun PQ := fromBlocks PQ.1 0 0 PQ.2
  map_smul' r PQ := by simp
  map_zero' := by simp
  map_add' PQ RS := by simp
  map_mul' PQ RS := by simp
  map_star' PQ := by simp

/-- Evaluation formula for `CStarMatrix.blockDiagHom`. -/
@[simp]
theorem blockDiagHom_apply [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] (PQ : CStarMatrix m m A × CStarMatrix n n A) :
    blockDiagHom (R := R) PQ = fromBlocks PQ.1 0 0 PQ.2 :=
  (rfl)

/-- `CStarMatrix.blockDiagHom` is injective. -/
theorem blockDiagHom_injective [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] :
    Function.Injective (blockDiagHom (R := R) (m := m) (n := n) (A := A)) := by
  rintro ⟨P₁, Q₁⟩ ⟨P₂, Q₂⟩ h
  simp only [blockDiagHom_apply, fromBlocks_inj, true_and] at h
  exact Prod.ext h.1 h.2

/-- Top-left block corner inclusion `M ↦ fromBlocks M 0 0 0`. -/
def inlCorner (n : Type*) [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (blockDiagHom (R := R)).comp (NonUnitalStarAlgHom.inl R (CStarMatrix m m A) (CStarMatrix n n A))

/-- Evaluation formula for `CStarMatrix.inlCorner`. -/
@[simp]
theorem inlCorner_apply [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] (M : CStarMatrix m m A) :
    inlCorner (R := R) n M = fromBlocks M 0 0 0 :=
  (rfl)

/-- `CStarMatrix.inlCorner` is injective. -/
theorem inlCorner_injective [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] :
    Function.Injective (inlCorner (R := R) (m := m) n (A := A)) := fun _ _ h ↦
  (fromBlocks_inj.mp h).1

/-- Bottom-right block corner inclusion `N ↦ fromBlocks 0 0 0 N`. -/
def inrCorner (m : Type*) [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (blockDiagHom (R := R)).comp (NonUnitalStarAlgHom.inr R (CStarMatrix m m A) (CStarMatrix n n A))

/-- Evaluation formula for `CStarMatrix.inrCorner`. -/
@[simp]
theorem inrCorner_apply [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] (N : CStarMatrix n n A) :
    inrCorner (R := R) m N = fromBlocks 0 0 0 N :=
  (rfl)

/-- `CStarMatrix.inrCorner` is injective. -/
theorem inrCorner_injective [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] :
    Function.Injective (inrCorner (R := R) m (n := n) (A := A)) := fun _ _ h ↦
  (fromBlocks_inj.mp h).2.2.2

/-- Top-left and bottom-right corner inclusions are mutually orthogonal. -/
theorem inlCorner_mul_inrCorner [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    inlCorner (R := R) n M * inrCorner (R := R) m N = 0 := by
  simp

/-- Bottom-right and top-left corner inclusions are mutually orthogonal. -/
theorem inrCorner_mul_inlCorner [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    inrCorner (R := R) m N * inlCorner (R := R) n M = 0 := by
  simp

/-- Single diagonal-entry `(i, i)` corner inclusion `A →⋆ₙₐ[R] CStarMatrix n n A`. -/
def singleCorner [Fintype n] [DecidableEq n] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [StarAddMonoid A] (i : n) :
    A →⋆ₙₐ[R] CStarMatrix n n A where
  toFun a := ofMatrix (Matrix.single i i a)
  map_smul' r a := by ext j k; simp [Matrix.single]
  map_zero' := by ext j k; simp
  map_add' a b := by ext j k; simp [Matrix.single_add]
  map_mul' a b := by
    refine ofMatrix.symm.injective ?_
    simp [Matrix.single_mul_single_same]
  map_star' a := by
    rw [star_eq_conjTranspose]
    exact ofMatrix.symm.injective (by simp)

/-- Entrywise formula for `CStarMatrix.singleCorner`. -/
@[simp]
theorem singleCorner_apply [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) (a : A) (j k : n) :
    singleCorner (R := R) i a j k = Matrix.single i i a j k :=
  (rfl)

/-- The `(i, i)` entry of `singleCorner i a` is `a`. -/
theorem singleCorner_apply_same [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) (a : A) :
    singleCorner (R := R) i a i i = a := by
  simp

/-- `CStarMatrix.singleCorner` is injective. -/
theorem singleCorner_injective [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) :
    Function.Injective (singleCorner (R := R) (A := A) i) := fun a b h ↦ by
  simpa only [singleCorner_apply_same] using congr_fun₂ h i i

/-- `singleCorner i a` is a star projection iff `a` is a star projection. -/
@[simp]
theorem isStarProjection_singleCorner [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) {a : A} :
    IsStarProjection (singleCorner (R := R) i a) ↔ IsStarProjection a := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map (singleCorner (R := R) i)⟩
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem]
    exact singleCorner_injective (R := R) i (by rw [map_mul, h.isIdempotentElem.eq])
  · rw [isSelfAdjoint_iff]
    exact singleCorner_injective (R := R) i (by rw [map_star, h.isSelfAdjoint.star_eq])

/-- Reindexing along identity equivalences on both sides is the identity map. -/
@[simp]
theorem reindexₗ_refl_refl [Semiring R] [AddCommMonoid A] [Module R A] (M : CStarMatrix m n A) :
    reindexₗ R A (Equiv.refl m) (Equiv.refl n) M = M :=
  (rfl)

/-- On square matrices with equal row and column equivalences, `reindexₗ` agrees with
`reindexₐ`. -/
theorem reindexₗ_eq_reindexₐ [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] [Star A] (e : m ≃ n) (M : CStarMatrix m m A) :
    reindexₗ R A e e M = reindexₐ R A e M := by
  ext i j
  simp

/-- Rectangular reindexing commutes with `conjTranspose`. -/
@[simp]
theorem conjTranspose_reindexₗ [Semiring R] [AddCommMonoid A] [Module R A] [Star A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    (reindexₗ R A eₘ eₙ M).conjTranspose = reindexₗ R A eₙ eₘ M.conjTranspose :=
  (rfl)

/-- Rectangular reindexing is compatible with rectangular matrix multiplication. -/
@[simp]
theorem reindexₗ_mul [Fintype m] [Fintype o] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] (e₁ : l ≃ k) (e₂ : m ≃ o) (e₃ : n ≃ p)
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    reindexₗ R A e₁ e₂ M * reindexₗ R A e₂ e₃ N = reindexₗ R A e₁ e₃ (M * N) := by
  ext i j
  simp only [mul_apply, reindexₗ_apply]
  exact Fintype.sum_equiv e₂.symm _ _ fun _ ↦ rfl

/-- Reindexing a `2 × 2` block-diagonal matrix along `Equiv.sumComm` swaps its diagonal blocks. -/
@[simp]
theorem reindexₐ_sumComm_fromBlocks [Fintype m] [Fintype n] [Semiring R]
    [AddCommMonoid A] [Mul A] [Module R A] [Star A]
    (P : CStarMatrix m m A) (Q : CStarMatrix n n A) :
    reindexₐ R A (Equiv.sumComm m n) (fromBlocks P 0 0 Q) = fromBlocks Q 0 0 P := by
  ext (i | i) (j | j) <;> rfl

/-- Reindexing nested `3 × 3` block-diagonal matrices along `Equiv.sumAssoc` reassociates them. -/
@[simp]
theorem reindexₐ_sumAssoc_fromBlocks [Fintype l] [Fintype m] [Fintype n] [Semiring R]
    [AddCommMonoid A] [Mul A] [Module R A] [Star A]
    (P : CStarMatrix l l A) (Q : CStarMatrix m m A) (S : CStarMatrix n n A) :
    reindexₐ R A (Equiv.sumAssoc l m n) (fromBlocks (fromBlocks P 0 0 Q) 0 0 S) =
      fromBlocks P 0 0 (fromBlocks Q 0 0 S) := by
  ext (i | (i | i)) (j | (j | j)) <;> rfl

section PermutationUnitary

variable (A)

/-- Rectangular permutation matrix in `CStarMatrix n m A` associated to an equivalence `e : m ≃ n`,
with `(i, j)`-entry `1` when `e.symm i = j` (equivalently `e j = i`) and `0` otherwise. -/
def permMatrix [DecidableEq m] [Semiring A] (e : m ≃ n) : CStarMatrix n m A :=
  reindexₗ ℕ A e (Equiv.refl m) (1 : CStarMatrix m m A)

variable {A}

/-- Entrywise formula for `CStarMatrix.permMatrix` in terms of `e.symm`. -/
@[simp]
theorem permMatrix_apply [DecidableEq m] [Semiring A] (e : m ≃ n) (i : n) (j : m) :
    permMatrix A e i j = if e.symm i = j then 1 else 0 :=
  (rfl)

/-- Entrywise formula for `CStarMatrix.permMatrix` in terms of `e`. -/
theorem permMatrix_apply_eq_ite [DecidableEq m] [DecidableEq n] [Semiring A]
    (e : m ≃ n) (i : n) (j : m) :
    permMatrix A e i j = if e j = i then 1 else 0 := by
  rw [permMatrix_apply]
  exact if_congr (e.symm_apply_eq.trans eq_comm) rfl rfl

/-- `(permMatrix A e).conjTranspose * permMatrix A e` is the `m × m` identity matrix. -/
@[simp]
theorem conjTranspose_permMatrix_mul_self [Fintype n] [DecidableEq m]
    [Semiring A] [StarRing A] (e : m ≃ n) :
    (permMatrix A e).conjTranspose * permMatrix A e = (1 : CStarMatrix m m A) := by
  let _ : Fintype m := Fintype.ofEquiv n e.symm
  rw [permMatrix, conjTranspose_reindexₗ, reindexₗ_mul, conjTranspose_one, CStarMatrix.mul_one,
    reindexₗ_refl_refl]

/-- `permMatrix A e * (permMatrix A e).conjTranspose` is the `n × n` identity matrix. -/
@[simp]
theorem permMatrix_mul_conjTranspose_self [Fintype m] [DecidableEq m] [DecidableEq n]
    [Semiring A] [StarRing A] (e : m ≃ n) :
    permMatrix A e * (permMatrix A e).conjTranspose = (1 : CStarMatrix n n A) := by
  let _ : Fintype n := Fintype.ofEquiv m e
  rw [permMatrix, conjTranspose_reindexₗ, reindexₗ_mul, conjTranspose_one, CStarMatrix.mul_one,
    reindexₗ_eq_reindexₐ]
  exact map_one (reindexₐ ℕ A e)

/-- Conjugating a square matrix `M : CStarMatrix m m A` by `permMatrix A e` produces
`reindexₐ ℕ A e M`. -/
@[simp]
theorem permMatrix_mul_mul_conjTranspose [Fintype m] [Fintype n] [DecidableEq m]
    [Semiring A] [StarRing A] (e : m ≃ n) (M : CStarMatrix m m A) :
    permMatrix A e * M * (permMatrix A e).conjTranspose = reindexₐ ℕ A e M := by
  nth_rw 1 [← reindexₗ_refl_refl (R := ℕ) M]
  rw [permMatrix, conjTranspose_reindexₗ, reindexₗ_mul, reindexₗ_mul,
    CStarMatrix.one_mul, conjTranspose_one, CStarMatrix.mul_one, reindexₗ_eq_reindexₐ]

/-- Square permutation unitary in `unitary (CStarMatrix n n A)` implementing `e : Equiv.Perm n`. -/
def permUnitary (A : Type*) [Fintype n] [DecidableEq n] [Ring A] [StarRing A] (e : Equiv.Perm n) :
    unitary (CStarMatrix n n A) :=
  ⟨permMatrix A e, conjTranspose_permMatrix_mul_self e, permMatrix_mul_conjTranspose_self e⟩

/-- Coercing `permUnitary A e` to a matrix recovers `permMatrix A e`. -/
@[simp]
theorem coe_permUnitary [Fintype n] [DecidableEq n] [Ring A] [StarRing A] (e : Equiv.Perm n) :
    (permUnitary A e : CStarMatrix n n A) = permMatrix A e :=
  (rfl)

/-- Conjugation by a square permutation matrix `permMatrix A e` using `star` equals
`reindexₐ ℕ A e`. -/
@[simp]
theorem permMatrix_mul_mul_star [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
    (e : Equiv.Perm n) (M : CStarMatrix n n A) :
    permMatrix A e * M * star (permMatrix A e) = reindexₐ ℕ A e M :=
  permMatrix_mul_mul_conjTranspose e M

/-- Conjugation by `permUnitary A e` equals `reindexₐ ℕ A e`. -/
theorem permUnitary_conj [Fintype n] [DecidableEq n] [Ring A] [StarRing A] (e : Equiv.Perm n)
    (M : CStarMatrix n n A) :
    (permUnitary A e : CStarMatrix n n A) * M * star (permUnitary A e : CStarMatrix n n A) =
      reindexₐ ℕ A e M :=
  permMatrix_mul_mul_conjTranspose e M

end PermutationUnitary

end BlocksAndReindex

section RectangularProperStar

variable {l m n A : Type*} [NonUnitalCStarAlgebra A]

/-- Rectangular matrix multiplication corresponds to composition of `toCLM` operators in reverse
order: `toCLM (M * N) = (toCLM N).comp (toCLM M)`. -/
@[simp]
theorem toCLM_mul [Fintype l] [Fintype m] (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    toCLM (M * N) = (toCLM N).comp (toCLM M) := by
  ext v k
  simp only [ContinuousLinearMap.comp_apply, toCLM_apply_eq_sum,
    WithCStarModule.equiv_symm_pi_apply, mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- For a rectangular `CStarMatrix`, `M.conjTranspose * M = 0` iff `M = 0`. -/
@[simp]
theorem conjTranspose_mul_self_eq_zero [Fintype m] {M : CStarMatrix m n A} :
    M.conjTranspose * M = 0 ↔ M = 0 := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  rw [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_mul, ofMatrix_symm_conjTranspose,
    ← ofMatrix.symm.injective.eq_iff (a := M)]
  exact Matrix.conjTranspose_mul_self_eq_zero

/-- For a rectangular `CStarMatrix`, `M * M.conjTranspose = 0` iff `M = 0`. -/
@[simp]
theorem self_mul_conjTranspose_eq_zero [Fintype n] {M : CStarMatrix m n A} :
    M * M.conjTranspose = 0 ↔ M = 0 := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  rw [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_mul, ofMatrix_symm_conjTranspose,
    ← ofMatrix.symm.injective.eq_iff (a := M)]
  exact Matrix.self_mul_conjTranspose_eq_zero

/-- Square `CStarMatrix`es over a C⋆-algebra have a proper star. -/
instance instIsProperStar [Fintype n] : IsProperStar (CStarMatrix n n A) where
  eq_zero_of_star_mul_self_eq_zero := by simp [star_eq_conjTranspose]

/-- **Rectangular partial-isometry identity**: if `v.conjTranspose * v` is idempotent for
`v : CStarMatrix m n A`, then `v * v.conjTranspose * v = v`. -/
theorem mul_conjTranspose_mul_self_of_isIdempotentElem [Fintype m] [Fintype n]
    {v : CStarMatrix m n A} (hv : IsIdempotentElem (v.conjTranspose * v)) :
    v * v.conjTranspose * v = v := by
  let V : CStarMatrix (m ⊕ n) (m ⊕ n) A := fromBlocks 0 v 0 0
  have hV_idem : IsIdempotentElem (star V * V) := by
    simp [V, IsIdempotentElem, hv.eq]
  have hV_pi : V * star V * V = V :=
    (TauCeti.IsPartialIsometry.of_isIdempotentElem_star_mul_self hV_idem).mul_star_mul_self
  simpa [V, fromBlocks_inj] using hV_pi

/-- Dual rectangular partial-isometry identity: if `v.conjTranspose * v` is idempotent, then
`v.conjTranspose * v * v.conjTranspose = v.conjTranspose`. -/
theorem conjTranspose_mul_self_mul_conjTranspose_of_isIdempotentElem [Fintype m] [Fintype n]
    {v : CStarMatrix m n A} (hv : IsIdempotentElem (v.conjTranspose * v)) :
    v.conjTranspose * v * v.conjTranspose = v.conjTranspose := by
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose, CStarMatrix.mul_assoc] using
    congrArg conjTranspose (mul_conjTranspose_mul_self_of_isIdempotentElem hv)

/-- If `v.conjTranspose * v` is idempotent for rectangular `v : CStarMatrix m n A`, then
`v * v.conjTranspose` is a star projection. -/
theorem isStarProjection_mul_conjTranspose_self_of_isIdempotentElem [Fintype m] [Fintype n]
    {v : CStarMatrix m n A} (hv : IsIdempotentElem (v.conjTranspose * v)) :
    IsStarProjection (v * v.conjTranspose) where
  isIdempotentElem := by
    rw [IsIdempotentElem, ← CStarMatrix.mul_assoc (v * v.conjTranspose) v v.conjTranspose,
      mul_conjTranspose_mul_self_of_isIdempotentElem hv]
  isSelfAdjoint := by
    rw [isSelfAdjoint_iff, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

end RectangularProperStar

section RectangularNorm

variable {l m n o m₁ m₂ n₁ n₂ A B : Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Operator norm submultiplicativity `‖M * N‖ ≤ ‖M‖ * ‖N‖` for rectangular `CStarMatrix`es. -/
protected theorem norm_mul_le [Fintype l] [Fintype m] [Fintype n]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    ‖M * N‖ ≤ ‖M‖ * ‖N‖ := by
  rw [norm_def, norm_def, norm_def, toCLM_mul, mul_comm]
  exact ContinuousLinearMap.opNorm_comp_le (toCLM N) (toCLM M)

/-- Lower C⋆-estimate `‖M‖ ^ 2 ≤ ‖M * M.conjTranspose‖` for a rectangular `CStarMatrix`. -/
theorem norm_sq_le_norm_mul_conjTranspose_self [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) :
    ‖M‖ ^ 2 ≤ ‖M * M.conjTranspose‖ := by
  have hmain : ‖M‖ ≤ √‖M * M.conjTranspose‖ := by
    rw [norm_def, ContinuousLinearMap.opNorm_le_iff (Real.sqrt_nonneg _)]
    intro v
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A), ← inner_toCLM_conjTranspose_right]
    have h₁ : ‖⟪v, (toCLM M.conjTranspose) ((toCLM M) v)⟫_A‖ ≤
        ‖M * M.conjTranspose‖ * ‖v‖ ^ 2 :=
      calc ‖⟪v, (toCLM M.conjTranspose) ((toCLM M) v)⟫_A‖
          ≤ ‖v‖ * ‖(toCLM M.conjTranspose) (toCLM M v)‖ :=
            CStarModule.norm_inner_le (C⋆ᵐᵒᵈ(A, m → A))
        _ ≤ ‖v‖ * (‖(toCLM M.conjTranspose).comp (toCLM M)‖ * ‖v‖) := by
            gcongr
            rw [← ContinuousLinearMap.comp_apply]
            exact ContinuousLinearMap.le_opNorm _ v
        _ = ‖M * M.conjTranspose‖ * ‖v‖ ^ 2 := by
            rw [← toCLM_mul, ← norm_def]
            ring
    have h₂ : ‖v‖ = √(‖v‖ ^ 2) := by simp
    rw [h₂, ← Real.sqrt_mul (norm_nonneg _)]
    exact Real.sqrt_le_sqrt h₁
  have hsq := mul_self_le_mul_self (norm_nonneg M) hmain
  rwa [← sq, Real.mul_self_sqrt (norm_nonneg _)] at hsq

private theorem norm_conjTranspose_le [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ ≤ ‖M‖ := by
  have hnn : 0 ≤ ‖M.conjTranspose‖ := by rw [norm_def]; exact ContinuousLinearMap.opNorm_nonneg _
  obtain h0 | hpos := hnn.eq_or_lt
  · rw [← h0, norm_def]
    exact ContinuousLinearMap.opNorm_nonneg _
  · refine le_of_mul_le_mul_left ?_ hpos
    calc ‖M.conjTranspose‖ * ‖M.conjTranspose‖
        = ‖M.conjTranspose‖ ^ 2 := (sq _).symm
      _ ≤ ‖M.conjTranspose * M.conjTranspose.conjTranspose‖ :=
          norm_sq_le_norm_mul_conjTranspose_self M.conjTranspose
      _ = ‖M.conjTranspose * M‖ := by rw [conjTranspose_conjTranspose]
      _ ≤ ‖M.conjTranspose‖ * ‖M‖ := CStarMatrix.norm_mul_le M.conjTranspose M

/-- `conjTranspose` preserves the operator norm of a rectangular `CStarMatrix`. -/
@[simp]
theorem norm_conjTranspose [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ = ‖M‖ :=
  le_antisymm (norm_conjTranspose_le M)
    (by simpa only [conjTranspose_conjTranspose] using norm_conjTranspose_le M.conjTranspose)

/-- Rectangular C⋆-identity `‖M * M.conjTranspose‖ = ‖M‖ ^ 2`. -/
@[simp]
theorem norm_mul_conjTranspose_self [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M * M.conjTranspose‖ = ‖M‖ ^ 2 := by
  refine le_antisymm ?_ (norm_sq_le_norm_mul_conjTranspose_self M)
  calc ‖M * M.conjTranspose‖ ≤ ‖M‖ * ‖M.conjTranspose‖ := CStarMatrix.norm_mul_le M M.conjTranspose
    _ = ‖M‖ ^ 2 := by rw [norm_conjTranspose, sq]

/-- Rectangular C⋆-identity `‖M.conjTranspose * M‖ = ‖M‖ ^ 2`. -/
@[simp]
theorem norm_conjTranspose_mul_self [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose * M‖ = ‖M‖ ^ 2 := by
  simpa only [conjTranspose_conjTranspose, norm_conjTranspose] using
    norm_mul_conjTranspose_self M.conjTranspose

/-- Any rectangular partial isometry `v : CStarMatrix m n A`
(`IsIdempotentElem (v.conjTranspose * v)`) is a contraction: `‖v‖ ≤ 1`. -/
theorem norm_le_one_of_isIdempotentElem_conjTranspose_mul_self [Fintype m] [Fintype n]
    {v : CStarMatrix m n A} (hv : IsIdempotentElem (v.conjTranspose * v)) :
    ‖v‖ ≤ 1 := by
  have hp : IsStarProjection (v.conjTranspose * v) :=
    ⟨hv, by rw [isSelfAdjoint_iff, star_eq_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose]⟩
  have hsq : ‖v‖ ^ 2 ≤ 1 ^ 2 := by
    rw [← norm_conjTranspose_mul_self, one_pow]
    exact hp.norm_le
  exact (sq_le_sq₀ (norm_nonneg v) zero_le_one).mp hsq

/-- Amplification `mapₙₐ f` of an injective `⋆`-homomorphism `f : A →⋆ₙₐ[ℂ] B` is isometric. -/
theorem norm_mapₙₐ [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Fintype n]
    {f : A →⋆ₙₐ[ℂ] B} (hf : Function.Injective f) (M : CStarMatrix n n A) :
    ‖mapₙₐ f M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map (mapₙₐ f) (mapₙₐ_injective hf) M

/-- Amplification `mapₐ f` of an injective unital `⋆`-homomorphism `f : A →⋆ₐ[ℂ] B` is isometric. -/
theorem norm_mapₐ {C D : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Fintype n] [DecidableEq n]
    {f : C →⋆ₐ[ℂ] D} (hf : Function.Injective f) (M : CStarMatrix n n C) :
    ‖mapₐ f M‖ = ‖M‖ :=
  norm_mapₙₐ hf M

/-- Exact C⋆-norm identity for a block-diagonal matrix with arbitrary rectangular blocks:
`‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖`. -/
@[simp]
theorem norm_fromBlocks_zero₁₂_zero₂₁ [Fintype m₁] [Fintype n₁] [Fintype m₂] [Fintype n₂]
    (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₂ n₂ A) :
    ‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖ := by
  -- Square case: `blockDiagHom` is an injective `NonUnitalStarAlgHom`, hence an isometry.
  have hsq_case : ∀ (P : CStarMatrix m₁ m₁ A) (Q : CStarMatrix m₂ m₂ A),
      ‖fromBlocks P 0 0 Q‖ = max ‖P‖ ‖Q‖ := fun P Q ↦ by
    rw [← blockDiagHom_apply (R := ℂ) (P, Q),
      NonUnitalStarAlgHom.norm_map (blockDiagHom (R := ℂ)) (blockDiagHom_injective (R := ℂ)) (P, Q),
      Prod.norm_mk]
  have h_eq : ‖fromBlocks M 0 0 N‖ ^ 2 = (max ‖M‖ ‖N‖) ^ 2 := by
    calc ‖fromBlocks M 0 0 N‖ ^ 2
        = ‖fromBlocks M 0 0 N * (fromBlocks M 0 0 N).conjTranspose‖ :=
          (norm_mul_conjTranspose_self _).symm
      _ = ‖fromBlocks (M * M.conjTranspose) 0 0 (N * N.conjTranspose)‖ := by
          simp
      _ = max ‖M * M.conjTranspose‖ ‖N * N.conjTranspose‖ := hsq_case _ _
      _ = max (‖M‖ ^ 2) (‖N‖ ^ 2) := by
          rw [norm_mul_conjTranspose_self, norm_mul_conjTranspose_self]
      _ = (max ‖M‖ ‖N‖) ^ 2 := by
          rcases le_total ‖M‖ ‖N‖ with hMN | hNM
          · rw [max_eq_right hMN, max_eq_right (pow_le_pow_left₀ (norm_nonneg M) hMN 2)]
          · rw [max_eq_left hNM, max_eq_left (pow_le_pow_left₀ (norm_nonneg N) hNM 2)]
  exact (sq_eq_sq₀ (norm_nonneg _) (le_max_of_le_left (norm_nonneg M))).mp h_eq

/-- Top-left block corner inclusion preserves operator norm: `‖inlCorner n M‖ = ‖M‖`. -/
theorem norm_inlCorner [Fintype m] [Fintype n] (M : CStarMatrix m m A) :
    ‖inlCorner (R := ℂ) n M‖ = ‖M‖ := by
  rw [inlCorner_apply, norm_fromBlocks_zero₁₂_zero₂₁, norm_zero, max_eq_left (norm_nonneg M)]

/-- Bottom-right block corner inclusion preserves operator norm: `‖inrCorner m N‖ = ‖N‖`. -/
theorem norm_inrCorner [Fintype m] [Fintype n] (N : CStarMatrix n n A) :
    ‖inrCorner (R := ℂ) m N‖ = ‖N‖ := by
  rw [inrCorner_apply, norm_fromBlocks_zero₁₂_zero₂₁, norm_zero, max_eq_right (norm_nonneg N)]

/-- Diagonal-entry corner inclusion preserves norm: `‖singleCorner i a‖ = ‖a‖`. -/
@[simp]
theorem norm_singleCorner [Fintype n] [DecidableEq n] (i : n) (a : A) :
    ‖singleCorner (R := ℂ) i a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (singleCorner (R := ℂ) i) (singleCorner_injective i) a

/-- Square reindexing `reindexₐ` preserves operator norm. -/
@[simp]
theorem norm_reindexₐ [Fintype m] [Fintype n] (e : m ≃ n) (M : CStarMatrix m m A) :
    ‖reindexₐ ℂ A e M‖ = ‖M‖ :=
  StarAlgEquiv.norm_map (reindexₐ ℂ A e) M

/-- Arbitrary rectangular reindexing `reindexₗ` preserves operator norm. -/
@[simp]
theorem norm_reindexₗ [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    ‖reindexₗ ℂ A eₘ eₙ M‖ = ‖M‖ := by
  have hsq : ‖reindexₗ ℂ A eₘ eₙ M‖ ^ 2 = ‖M‖ ^ 2 := by
    calc ‖reindexₗ ℂ A eₘ eₙ M‖ ^ 2
        = ‖reindexₗ ℂ A eₘ eₙ M * (reindexₗ ℂ A eₘ eₙ M).conjTranspose‖ :=
          (norm_mul_conjTranspose_self _).symm
      _ = ‖reindexₐ ℂ A eₘ (M * M.conjTranspose)‖ := by
          rw [conjTranspose_reindexₗ, reindexₗ_mul, reindexₗ_eq_reindexₐ]
      _ = ‖M * M.conjTranspose‖ := norm_reindexₐ eₘ (M * M.conjTranspose)
      _ = ‖M‖ ^ 2 := norm_mul_conjTranspose_self M
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end RectangularNorm

end CStarMatrix
