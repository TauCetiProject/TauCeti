/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block

/-!
# Block calculus, amplification, and operator norms for rectangular `CStarMatrix`

Mathlib defines `CStarMatrix m n A` for matrices of arbitrary finite dimensions over a C⋆-algebra
`A`, equipping `CStarMatrix n n A` with a C⋆-algebra structure and `CStarMatrix m n A` with the
Hilbert C⋆-module operator norm via `CStarMatrix.toCLM`. This file develops rectangular and
block-matrix algebra and norm identities on `CStarMatrix`:

* Rectangular `conjTranspose`, multiplication, proper-star laws (`M.conjTranspose * M = 0 ↔ M = 0`),
  entrywise homomorphisms (`mapₐ`), and rectangular `reindexₗ` identities.
* Four-block matrices `CStarMatrix.fromBlocks`, vertical stacks `CStarMatrix.colBlocks`,
  block-diagonal direct sums `CStarMatrix.blockDiag`, corner embeddings (`inlStarAlgHom`,
  `inrStarAlgHom`, `singleStarAlgHom`), and finite amplification `CStarMatrix.amplify`.
* Operator-norm identities: submultiplicativity `‖M * N‖ ≤ ‖M‖ * ‖N‖`, isometric conjugate
  transposition `‖M.conjTranspose‖ = ‖M‖`, the rectangular C⋆-identities
  `‖M * M.conjTranspose‖ = ‖M‖ ^ 2` and `‖M.conjTranspose * M‖ = ‖M‖ ^ 2`, and exact norm formulas
  for reindexing, block-diagonal sums (`‖blockDiag M N‖ = max ‖M‖ ‖N‖`), matrix units, and
  amplifications.

## Main declarations

* `CStarMatrix.fromBlocks`, `CStarMatrix.colBlocks`, `CStarMatrix.blockDiag`, `CStarMatrix.amplify`.
* `CStarMatrix.blockDiagStarAlgHom`, `CStarMatrix.inlStarAlgHom`, `CStarMatrix.inrStarAlgHom`,
  `CStarMatrix.singleStarAlgHom`, `CStarMatrix.amplifyStarAlgHom`,
  `CStarMatrix.amplifyUnitalStarAlgHom`.
* `CStarMatrix.norm_conjTranspose`, `CStarMatrix.norm_self_mul_conjTranspose`,
  `CStarMatrix.norm_conjTranspose_mul_self`, `CStarMatrix.norm_blockDiag`,
  `CStarMatrix.norm_reindexₗ`, `CStarMatrix.norm_amplify`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §4.6 and §5.1.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 4.
-/

public section

open scoped Matrix ComplexOrder InnerProductSpace WithCStarModule

namespace CStarMatrix

section RectangularAlgebra

variable {k l m n o R A B : Type*}

@[simp] theorem of_one [DecidableEq n] [Zero A] [One A] : ofMatrix (1 : Matrix n n A) = 1 := (rfl)

@[simp] theorem of_mul_of [Fintype m] [Mul A] [AddCommMonoid A]
    (f : Matrix l m A) (g : Matrix m n A) :
    ofMatrix f * ofMatrix g = ofMatrix (f * g) := (rfl)

@[simp] theorem ofMatrix_symm_conjTranspose [Star A] (M : CStarMatrix m n A) :
    ofMatrix.symm M.conjTranspose = (ofMatrix.symm M)ᴴ := (rfl)

@[simp] theorem conjTranspose_of [Star A] (f : Matrix m n A) :
    (ofMatrix f).conjTranspose = ofMatrix fᴴ := (rfl)

/-- Rectangular matrix multiplication on `CStarMatrix` is associative. -/
protected theorem mul_assoc [Fintype l] [Fintype m] [NonUnitalSemiring A]
    (L : CStarMatrix k l A) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    L * M * N = L * (M * N) :=
  ofMatrix.symm.injective (Matrix.mul_assoc (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N))

/-- Scalars pull out of both factors in a rectangular `CStarMatrix` product. -/
protected theorem smul_mul_smul [Fintype m] [Monoid R] [AddCommMonoid A] [Mul A]
    [DistribMulAction R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (a b : R) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (a • M) * (b • N) = (a * b) • (M * N) := by
  rw [CStarMatrix.smul_mul, CStarMatrix.mul_smul, smul_smul]

@[simp] protected theorem one_mul [Fintype m] [DecidableEq m] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : (1 : CStarMatrix m m A) * M = M :=
  ofMatrix.symm.injective (Matrix.one_mul (ofMatrix.symm M))

@[simp] protected theorem mul_one [Fintype n] [DecidableEq n] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : M * (1 : CStarMatrix n n A) = M :=
  ofMatrix.symm.injective (Matrix.mul_one (ofMatrix.symm M))

protected theorem mul_sub [Fintype n] [NonUnitalNonAssocRing A]
    (L : CStarMatrix m n A) (M N : CStarMatrix n o A) : L * (M - N) = L * M - L * N :=
  ofMatrix.symm.injective (Matrix.mul_sub (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N))

protected theorem sub_mul [Fintype m] [NonUnitalNonAssocRing A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) : (L - M) * N = L * N - M * N :=
  ofMatrix.symm.injective (Matrix.sub_mul (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N))

@[simp] protected theorem neg_mul [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : (-M) * N = -(M * N) :=
  ofMatrix.symm.injective (Matrix.neg_mul (ofMatrix.symm M) (ofMatrix.symm N))

@[simp] protected theorem mul_neg [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : M * (-N) = -(M * N) :=
  ofMatrix.symm.injective (Matrix.mul_neg (ofMatrix.symm M) (ofMatrix.symm N))

@[simp] theorem conjTranspose_conjTranspose [InvolutiveStar A] (M : CStarMatrix m n A) :
    M.conjTranspose.conjTranspose = M := by ext; simp

theorem conjTranspose_injective [InvolutiveStar A] :
    Function.Injective (conjTranspose : CStarMatrix m n A → CStarMatrix n m A) :=
  Function.LeftInverse.injective conjTranspose_conjTranspose

@[simp] theorem conjTranspose_inj [InvolutiveStar A] {M N : CStarMatrix m n A} :
    M.conjTranspose = N.conjTranspose ↔ M = N :=
  conjTranspose_injective.eq_iff

@[simp] theorem conjTranspose_add [AddMonoid A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M + N).conjTranspose = M.conjTranspose + N.conjTranspose := by ext; simp

@[simp] theorem conjTranspose_sub [AddGroup A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M - N).conjTranspose = M.conjTranspose - N.conjTranspose := by ext; simp

@[simp] theorem conjTranspose_neg [AddGroup A] [StarAddMonoid A] (M : CStarMatrix m n A) :
    (-M).conjTranspose = -M.conjTranspose := by ext; simp

@[simp] theorem conjTranspose_smul [Star R] [Star A] [SMul R A] [StarModule R A]
    (r : R) (M : CStarMatrix m n A) :
    (r • M).conjTranspose = star r • M.conjTranspose := by ext; simp

@[simp] theorem conjTranspose_one [DecidableEq n] [Semiring A] [StarRing A] :
    (1 : CStarMatrix n n A).conjTranspose = 1 :=
  ofMatrix.symm.injective Matrix.conjTranspose_one

/-- Conjugate transposition reverses rectangular matrix products. -/
@[simp] theorem conjTranspose_mul [Fintype m] [NonUnitalNonAssocSemiring A] [StarRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).conjTranspose = N.conjTranspose * M.conjTranspose :=
  ofMatrix.symm.injective (Matrix.conjTranspose_mul (ofMatrix.symm M) (ofMatrix.symm N))

/-- Over a star-ordered ring with proper star, `M.conjTranspose * M = 0` iff `M = 0`. -/
@[simp] theorem conjTranspose_mul_self_eq_zero [Fintype m] [NonUnitalSemiring A] [StarRing A]
    [PartialOrder A] [StarOrderedRing A] [IsProperStar A] {M : CStarMatrix m n A} :
    M.conjTranspose * M = 0 ↔ M = 0 := by
  refine ⟨fun h => ext fun i j => ?_, fun h => by simp [h]⟩
  have hjj : ∑ k, star (M k j) * M k j = 0 := by
    simpa [mul_apply] using congr_fun (congr_fun h j) j
  exact star_mul_self_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun k _ => star_mul_self_nonneg (M k j)).mp hjj i
      (Finset.mem_univ i))

/-- Over a star-ordered ring with proper star, `M * M.conjTranspose = 0` iff `M = 0`. -/
@[simp] theorem self_mul_conjTranspose_eq_zero [Fintype n] [NonUnitalSemiring A] [StarRing A]
    [PartialOrder A] [StarOrderedRing A] [IsProperStar A] {M : CStarMatrix m n A} :
    M * M.conjTranspose = 0 ↔ M = 0 := by
  rw [← conjTranspose_inj (M := M) (N := 0), conjTranspose_zero,
    ← conjTranspose_mul_self_eq_zero (M := M.conjTranspose), conjTranspose_conjTranspose]

end RectangularAlgebra

section MapAndReindex

variable {k l m n o p R A B F : Type*}

@[simp] theorem map_zero [Zero A] [Zero B] {f : A → B} (hf : f 0 = 0) :
    (0 : CStarMatrix m n A).map f = 0 := by ext; simp [hf]

theorem map_add [AddZeroClass A] [AddZeroClass B] [FunLike F A B] [AddMonoidHomClass F A B]
    (φ : F) (M N : CStarMatrix m n A) : (M + N).map φ = M.map φ + N.map φ := by ext; simp

/-- Mapping entries by a non-unital ring homomorphism commutes with rectangular multiplication. -/
theorem map_mul [Fintype m] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [FunLike F A B] [NonUnitalRingHomClass F A B]
    (φ : F) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).map φ = M.map φ * N.map φ := by ext; simp [mul_apply, map_sum]

/-- Mapping entries by a `⋆`-homomorphism commutes with `conjTranspose`. -/
theorem map_conjTranspose [Star A] [Star B] [FunLike F A B] [StarHomClass F A B]
    (φ : F) (M : CStarMatrix m n A) :
    M.conjTranspose.map φ = (M.map φ).conjTranspose := by ext; simp [map_star]

theorem mapₙₐ_eq_map [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    (φ : A →⋆ₙₐ[R] B) (M : CStarMatrix n n A) : mapₙₐ φ M = M.map φ := (rfl)

/-- Applying a unital `⋆`-algebra homomorphism entrywise gives a unital `⋆`-algebra homomorphism
between square matrix algebras. -/
def mapₐ [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B] (φ : A →⋆ₐ[R] B) :
    CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B :=
  { mapₙₐ φ.toNonUnitalStarAlgHom with
    map_one' := by ext i j; by_cases h : i = j <;> simp [mapₙₐ_apply, mapₗ_apply, one_apply, h]
    commutes' r := by
      ext i j; by_cases h : i = j <;>
        simp [mapₙₐ_apply, mapₗ_apply, algebraMap_apply, h, AlgHomClass.commutes] }

@[simp] theorem mapₐ_apply [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A]
    [Star A] [Semiring B] [Algebra R B] [Star B] (φ : A →⋆ₐ[R] B) (M : CStarMatrix n n A) :
    mapₐ φ M = M.map φ := (rfl)

@[simp] theorem reindexₗ_conjTranspose [Semiring R] [AddCommMonoid A] [Module R A] [Star A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    (reindexₗ R A eₘ eₙ M).conjTranspose = reindexₗ R A eₙ eₘ M.conjTranspose := by ext; rfl

/-- `reindexₗ` is multiplicative across matching intermediate equivalences. -/
@[simp] theorem reindexₗ_mul [Fintype m] [Fintype o] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] (eₗ : l ≃ k) (eₘ : m ≃ o) (eₙ : n ≃ p)
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    reindexₗ R A eₗ eₘ M * reindexₗ R A eₘ eₙ N = reindexₗ R A eₗ eₙ (M * N) := by
  ext i j
  simp only [mul_apply, reindexₗ_apply]
  exact Fintype.sum_equiv eₘ.symm _ _ fun _ => rfl

@[simp] theorem reindexₗ_refl [Semiring R] [AddCommMonoid A] [Module R A] (M : CStarMatrix m n A) :
    reindexₗ R A (Equiv.refl m) (Equiv.refl n) M = M := by ext; rfl

theorem reindexₗ_trans [Semiring R] [AddCommMonoid A] [Module R A]
    (e₁ : m ≃ l) (e₂ : l ≃ k) (f₁ : n ≃ o) (f₂ : o ≃ p) (M : CStarMatrix m n A) :
    reindexₗ R A (e₁.trans e₂) (f₁.trans f₂) M =
      reindexₗ R A e₂ f₂ (reindexₗ R A e₁ f₁ M) := by ext; rfl

@[simp] theorem reindexₐ_refl [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    [Star A] : reindexₐ R A (Equiv.refl n) = StarAlgEquiv.refl R (CStarMatrix n n A) := by ext; rfl

theorem reindexₐ_trans [Fintype l] [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A]
    [Mul A] [Module R A] [Star A] (e₁ : l ≃ m) (e₂ : m ≃ n) :
    reindexₐ R A (e₁.trans e₂) = (reindexₐ R A e₁).trans (reindexₐ R A e₂) := by ext; rfl

end MapAndReindex

section Blocks

variable {k l m n o p m₁ m₂ m₃ n₁ n₂ n₃ R A B : Type*}

/-- Build a four-block `CStarMatrix` from blocks of sizes `m × l`, `m × n`, `o × l`, and
`o × n`. -/
def fromBlocks (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) : CStarMatrix (m ⊕ o) (l ⊕ n) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
    (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂))

@[simp] theorem ofMatrix_symm_fromBlocks (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    ofMatrix.symm (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
        (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂) := (rfl)

@[simp] theorem of_fromBlocks (M₁₁ : Matrix m l A) (M₁₂ : Matrix m n A)
    (M₂₁ : Matrix o l A) (M₂₂ : Matrix o n A) :
    ofMatrix (Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (ofMatrix M₁₁) (ofMatrix M₁₂) (ofMatrix M₂₁) (ofMatrix M₂₂) := (rfl)

@[simp] theorem fromBlocks_apply₁₁ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) (i : m) (j : l) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inl j) = M₁₁ i j := (rfl)

@[simp] theorem fromBlocks_apply₁₂ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) (i : m) (j : n) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inr j) = M₁₂ i j := (rfl)

@[simp] theorem fromBlocks_apply₂₁ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) (i : o) (j : l) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inl j) = M₂₁ i j := (rfl)

@[simp] theorem fromBlocks_apply₂₂ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) (i : o) (j : n) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inr j) = M₂₂ i j := (rfl)

@[simp] theorem fromBlocks_inj {M₁₁ N₁₁ : CStarMatrix m l A} {M₁₂ N₁₂ : CStarMatrix m n A}
    {M₂₁ N₂₁ : CStarMatrix o l A} {M₂₂ N₂₂ : CStarMatrix o n A} :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ ↔
      M₁₁ = N₁₁ ∧ M₁₂ = N₁₂ ∧ M₂₁ = N₂₁ ∧ M₂₂ = N₂₂ := by
  rw [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_fromBlocks, ofMatrix_symm_fromBlocks,
    Matrix.fromBlocks_inj]
  simp [ofMatrix.symm.injective.eq_iff]

@[simp] theorem fromBlocks_zero [Zero A] :
    fromBlocks (0 : CStarMatrix m l A) (0 : CStarMatrix m n A)
      (0 : CStarMatrix o l A) (0 : CStarMatrix o n A) = 0 :=
  ofMatrix.symm.injective Matrix.fromBlocks_zero

@[simp] theorem fromBlocks_one [DecidableEq l] [DecidableEq m] [Zero A] [One A] :
    fromBlocks (1 : CStarMatrix l l A) 0 0 (1 : CStarMatrix m m A) = 1 :=
  ofMatrix.symm.injective Matrix.fromBlocks_one

@[simp] theorem fromBlocks_add [Add A]
    (M₁₁ N₁₁ : CStarMatrix m l A) (M₁₂ N₁₂ : CStarMatrix m n A)
    (M₂₁ N₂₁ : CStarMatrix o l A) (M₂₂ N₂₂ : CStarMatrix o n A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ + fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ + N₁₁) (M₁₂ + N₁₂) (M₂₁ + N₂₁) (M₂₂ + N₂₂) :=
  ofMatrix.symm.injective (Matrix.fromBlocks_add _ _ _ _ _ _ _ _)

@[simp] theorem fromBlocks_neg [Neg A]
    (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    -fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks (-M₁₁) (-M₁₂) (-M₂₁) (-M₂₂) :=
  ofMatrix.symm.injective (Matrix.fromBlocks_neg _ _ _ _)

@[simp] theorem fromBlocks_sub [AddGroup A]
    (M₁₁ N₁₁ : CStarMatrix m l A) (M₁₂ N₁₂ : CStarMatrix m n A)
    (M₂₁ N₂₁ : CStarMatrix o l A) (M₂₂ N₂₂ : CStarMatrix o n A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ - fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ - N₁₁) (M₁₂ - N₁₂) (M₂₁ - N₂₁) (M₂₂ - N₂₂) := by
  ext (_ | _) (_ | _) <;> rfl

@[simp] theorem fromBlocks_smul [SMul R A] (r : R)
    (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    r • fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks (r • M₁₁) (r • M₁₂) (r • M₂₁) (r • M₂₂) :=
  ofMatrix.symm.injective (Matrix.fromBlocks_smul r _ _ _ _)

/-- Block-by-block multiplication of `CStarMatrix.fromBlocks`. -/
theorem fromBlocks_mul [Fintype l] [Fintype n] [NonUnitalNonAssocSemiring A]
    (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A)
    (N₁₁ : CStarMatrix l k A) (N₁₂ : CStarMatrix l p A)
    (N₂₁ : CStarMatrix n k A) (N₂₂ : CStarMatrix n p A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ * N₁₁ + M₁₂ * N₂₁) (M₁₁ * N₁₂ + M₁₂ * N₂₂)
        (M₂₁ * N₁₁ + M₂₂ * N₂₁) (M₂₁ * N₁₂ + M₂₂ * N₂₂) :=
  ofMatrix.symm.injective (Matrix.fromBlocks_multiply _ _ _ _ _ _ _ _)

/-- Conjugate transpose of a four-block `CStarMatrix`. -/
@[simp] theorem fromBlocks_conjTranspose [Star A]
    (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).conjTranspose =
      fromBlocks M₁₁.conjTranspose M₂₁.conjTranspose M₁₂.conjTranspose M₂₂.conjTranspose :=
  ofMatrix.symm.injective (Matrix.fromBlocks_conjTranspose _ _ _ _)

/-- `star` of a square four-block `CStarMatrix`. -/
theorem star_fromBlocks [Star A]
    (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix n m A) (M₂₂ : CStarMatrix n n A) :
    star (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (star M₁₁) M₂₁.conjTranspose M₁₂.conjTranspose (star M₂₂) :=
  fromBlocks_conjTranspose M₁₁ M₁₂ M₂₁ M₂₂

@[simp] theorem map_fromBlocks (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) (f : A → B) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).map f =
      fromBlocks (M₁₁.map f) (M₁₂.map f) (M₂₁.map f) (M₂₂.map f) :=
  ofMatrix.symm.injective (Matrix.fromBlocks_map _ _ _ _ f)

/-- Stack two matrices of sizes `m × l` and `o × l` vertically into a `(m ⊕ o) × l`
`CStarMatrix`. -/
def colBlocks (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A) : CStarMatrix (m ⊕ o) l A :=
  ofMatrix (Sum.elim (ofMatrix.symm M₁) (ofMatrix.symm M₂))

@[simp] theorem colBlocks_apply_inl (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A)
    (i : m) (j : l) : colBlocks M₁ M₂ (Sum.inl i) j = M₁ i j := (rfl)

@[simp] theorem colBlocks_apply_inr (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A)
    (i : o) (j : l) : colBlocks M₁ M₂ (Sum.inr i) j = M₂ i j := (rfl)

@[simp] theorem colBlocks_inj {M₁ N₁ : CStarMatrix m l A} {M₂ N₂ : CStarMatrix o l A} :
    colBlocks M₁ M₂ = colBlocks N₁ N₂ ↔ M₁ = N₁ ∧ M₂ = N₂ := by
  refine ⟨fun h => ⟨ext fun i j => ?_, ext fun i j => ?_⟩, fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ rfl⟩
  · simpa using congr_fun (congr_fun h (Sum.inl i)) j
  · simpa using congr_fun (congr_fun h (Sum.inr i)) j

@[simp] theorem colBlocks_zero [Zero A] :
    colBlocks (0 : CStarMatrix m l A) (0 : CStarMatrix o l A) = 0 := by ext (_ | _) _ <;> rfl

/-- Inner product of two vertical block stacks as a sum of `l × n` products. -/
@[simp] theorem conjTranspose_colBlocks_mul [Fintype m] [Fintype o] [NonUnitalNonAssocSemiring A]
    [Star A] (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A)
    (N₁ : CStarMatrix m n A) (N₂ : CStarMatrix o n A) :
    (colBlocks M₁ M₂).conjTranspose * colBlocks N₁ N₂ =
      M₁.conjTranspose * N₁ + M₂.conjTranspose * N₂ := by
  ext; simp [mul_apply, Fintype.sum_sum_type]

/-- Outer product of two vertical block stacks as a four-block `CStarMatrix`. -/
@[simp] theorem colBlocks_mul_conjTranspose [Fintype l] [NonUnitalNonAssocSemiring A] [Star A]
    (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A)
    (N₁ : CStarMatrix k l A) (N₂ : CStarMatrix p l A) :
    colBlocks M₁ M₂ * (colBlocks N₁ N₂).conjTranspose =
      fromBlocks (M₁ * N₁.conjTranspose) (M₁ * N₂.conjTranspose)
        (M₂ * N₁.conjTranspose) (M₂ * N₂.conjTranspose) := by
  ext (_ | _) (_ | _) <;> simp [mul_apply]

/-- Action of a four-block `CStarMatrix` on a vertical block stack. -/
@[simp] theorem fromBlocks_mul_colBlocks [Fintype l] [Fintype n] [NonUnitalNonAssocSemiring A]
    (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A)
    (N₁ : CStarMatrix l k A) (N₂ : CStarMatrix n k A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * colBlocks N₁ N₂ =
      colBlocks (M₁₁ * N₁ + M₁₂ * N₂) (M₂₁ * N₁ + M₂₂ * N₂) := by
  ext (_ | _) _ <;> simp [mul_apply, Fintype.sum_sum_type]

/-- The block-diagonal direct sum `M ⊕ N` of two rectangular `CStarMatrix` values. -/
def blockDiag [Zero A] (M : CStarMatrix m l A) (N : CStarMatrix o n A) :
    CStarMatrix (m ⊕ o) (l ⊕ n) A :=
  fromBlocks M 0 0 N

theorem blockDiag_def [Zero A] (M : CStarMatrix m l A) (N : CStarMatrix o n A) :
    blockDiag M N = fromBlocks M 0 0 N := (rfl)

@[simp] theorem blockDiag_apply_inl_inl [Zero A] (M : CStarMatrix m l A) (N : CStarMatrix o n A)
    (i : m) (j : l) : blockDiag M N (Sum.inl i) (Sum.inl j) = M i j := (rfl)

@[simp] theorem blockDiag_apply_inl_inr [Zero A] (M : CStarMatrix m l A) (N : CStarMatrix o n A)
    (i : m) (j : n) : blockDiag M N (Sum.inl i) (Sum.inr j) = 0 := (rfl)

@[simp] theorem blockDiag_apply_inr_inl [Zero A] (M : CStarMatrix m l A) (N : CStarMatrix o n A)
    (i : o) (j : l) : blockDiag M N (Sum.inr i) (Sum.inl j) = 0 := (rfl)

@[simp] theorem blockDiag_apply_inr_inr [Zero A] (M : CStarMatrix m l A) (N : CStarMatrix o n A)
    (i : o) (j : n) : blockDiag M N (Sum.inr i) (Sum.inr j) = N i j := (rfl)

@[simp] theorem blockDiag_inj [Zero A] {M₁ M₂ : CStarMatrix m l A} {N₁ N₂ : CStarMatrix o n A} :
    blockDiag M₁ N₁ = blockDiag M₂ N₂ ↔ M₁ = M₂ ∧ N₁ = N₂ := by simp [blockDiag_def]

@[simp] theorem blockDiag_zero [Zero A] :
    blockDiag (0 : CStarMatrix m l A) (0 : CStarMatrix o n A) = 0 := fromBlocks_zero

@[simp] theorem blockDiag_one [DecidableEq l] [DecidableEq m] [Zero A] [One A] :
    blockDiag (1 : CStarMatrix l l A) (1 : CStarMatrix m m A) = 1 := fromBlocks_one

@[simp] theorem blockDiag_add [AddZeroClass A]
    (M₁ M₂ : CStarMatrix m l A) (N₁ N₂ : CStarMatrix o n A) :
    blockDiag M₁ N₁ + blockDiag M₂ N₂ = blockDiag (M₁ + M₂) (N₁ + N₂) := by simp [blockDiag_def]

@[simp] theorem blockDiag_neg [SubtractionMonoid A]
    (M : CStarMatrix m l A) (N : CStarMatrix o n A) :
    -blockDiag M N = blockDiag (-M) (-N) := by ext (_ | _) (_ | _) <;> simp

@[simp] theorem blockDiag_sub [AddGroup A]
    (M₁ M₂ : CStarMatrix m l A) (N₁ N₂ : CStarMatrix o n A) :
    blockDiag M₁ N₁ - blockDiag M₂ N₂ = blockDiag (M₁ - M₂) (N₁ - N₂) := by simp [blockDiag_def]

@[simp] theorem blockDiag_smul [Zero A] [SMulZeroClass R A] (r : R)
    (M : CStarMatrix m l A) (N : CStarMatrix o n A) :
    r • blockDiag M N = blockDiag (r • M) (r • N) := by ext (_ | _) (_ | _) <;> simp

@[simp] theorem blockDiag_mul [Fintype l] [Fintype n] [NonUnitalNonAssocSemiring A]
    (M₁ : CStarMatrix m l A) (N₁ : CStarMatrix o n A)
    (M₂ : CStarMatrix l k A) (N₂ : CStarMatrix n p A) :
    blockDiag M₁ N₁ * blockDiag M₂ N₂ = blockDiag (M₁ * M₂) (N₁ * N₂) := by
  simp [blockDiag_def, fromBlocks_mul]

@[simp] theorem blockDiag_conjTranspose [AddMonoid A] [StarAddMonoid A]
    (M : CStarMatrix m l A) (N : CStarMatrix o n A) :
    (blockDiag M N).conjTranspose = blockDiag M.conjTranspose N.conjTranspose := by
  simp [blockDiag_def]

@[simp] theorem star_blockDiag [AddMonoid A] [StarAddMonoid A]
    (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    star (blockDiag M N) = blockDiag (star M) (star N) :=
  blockDiag_conjTranspose M N

@[simp] theorem map_blockDiag [Zero A] [Zero B] (M : CStarMatrix m l A) (N : CStarMatrix o n A)
    {f : A → B} (hf : f 0 = 0) :
    (blockDiag M N).map f = blockDiag (M.map f) (N.map f) := by simp [blockDiag_def, map_zero hf]

/-- A block-diagonal square matrix is idempotent iff both blocks are idempotent. -/
@[simp] theorem isIdempotentElem_blockDiag_iff [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A]
    {P : CStarMatrix m m A} {Q : CStarMatrix n n A} :
    IsIdempotentElem (blockDiag P Q) ↔ IsIdempotentElem P ∧ IsIdempotentElem Q := by
  simp [IsIdempotentElem]

/-- A block-diagonal square matrix is self-adjoint iff both blocks are self-adjoint. -/
@[simp] theorem isSelfAdjoint_blockDiag_iff [AddMonoid A] [StarAddMonoid A]
    {P : CStarMatrix m m A} {Q : CStarMatrix n n A} :
    IsSelfAdjoint (blockDiag P Q) ↔ IsSelfAdjoint P ∧ IsSelfAdjoint Q := by simp [IsSelfAdjoint]

/-- A block-diagonal square matrix is a star projection iff both blocks are star projections. -/
@[simp] theorem isStarProjection_blockDiag_iff [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A]
    [StarAddMonoid A] {P : CStarMatrix m m A} {Q : CStarMatrix n n A} :
    IsStarProjection (blockDiag P Q) ↔ IsStarProjection P ∧ IsStarProjection Q := by
  simp [isStarProjection_iff, and_and_and_comm]

@[simp] theorem reindexₗ_sumAssoc_blockDiag [Semiring R] [AddCommMonoid A] [Module R A]
    (M₁ : CStarMatrix m₁ n₁ A) (M₂ : CStarMatrix m₂ n₂ A) (M₃ : CStarMatrix m₃ n₃ A) :
    reindexₗ R A (Equiv.sumAssoc m₁ m₂ m₃) (Equiv.sumAssoc n₁ n₂ n₃)
        (blockDiag (blockDiag M₁ M₂) M₃) =
      blockDiag M₁ (blockDiag M₂ M₃) := by ext (_ | _ | _) (_ | _ | _) <;> rfl

@[simp] theorem reindexₐ_sumAssoc_blockDiag [Fintype l] [Fintype m] [Fintype n] [Semiring R]
    [AddCommMonoid A] [Mul A] [Module R A] [Star A]
    (M₁ : CStarMatrix l l A) (M₂ : CStarMatrix m m A) (M₃ : CStarMatrix n n A) :
    reindexₐ R A (Equiv.sumAssoc l m n) (blockDiag (blockDiag M₁ M₂) M₃) =
      blockDiag M₁ (blockDiag M₂ M₃) := by ext (_ | _ | _) (_ | _ | _) <;> rfl

@[simp] theorem reindexₗ_sumComm_blockDiag [Semiring R] [AddCommMonoid A] [Module R A]
    (M₁ : CStarMatrix m₁ n₁ A) (M₂ : CStarMatrix m₂ n₂ A) :
    reindexₗ R A (Equiv.sumComm m₁ m₂) (Equiv.sumComm n₁ n₂) (blockDiag M₁ M₂) =
      blockDiag M₂ M₁ := by ext (_ | _) (_ | _) <;> rfl

@[simp] theorem reindexₐ_sumComm_blockDiag [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A]
    [Mul A] [Module R A] [Star A] (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    reindexₐ R A (Equiv.sumComm m n) (blockDiag M N) = blockDiag N M := by
  ext (_ | _) (_ | _) <;> rfl

/-- `blockDiag` bundled as an injective non-unital `⋆`-algebra homomorphism from the product of
two square matrix algebras into the `(m ⊕ n) × (m ⊕ n)` matrix algebra. -/
def blockDiagStarAlgHom (R : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun P := blockDiag P.1 P.2
  map_smul' r P := (blockDiag_smul r P.1 P.2).symm
  map_zero' := blockDiag_zero
  map_add' P Q := (blockDiag_add P.1 Q.1 P.2 Q.2).symm
  map_mul' P Q := (blockDiag_mul P.1 P.2 Q.1 Q.2).symm
  map_star' P := (star_blockDiag P.1 P.2).symm

@[simp] theorem blockDiagStarAlgHom_apply [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (P : CStarMatrix m m A × CStarMatrix n n A) :
    blockDiagStarAlgHom R P = blockDiag P.1 P.2 := (rfl)

theorem blockDiagStarAlgHom_injective [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (blockDiagStarAlgHom R :
      CStarMatrix m m A × CStarMatrix n n A → CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  fun _ _ h => Prod.ext (blockDiag_inj.mp h).1 (blockDiag_inj.mp h).2

/-- Upper-left corner inclusion `M ↦ M ⊕ 0` as a non-unital `⋆`-algebra homomorphism. -/
def inlStarAlgHom (R n : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun M := blockDiag M 0
  map_smul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp
  map_mul' _ _ := by simp
  map_star' _ := by simp

@[simp] theorem inlStarAlgHom_apply [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (M : CStarMatrix m m A) :
    inlStarAlgHom R n M = blockDiag M 0 := (rfl)

/-- Lower-right corner inclusion `N ↦ 0 ⊕ N` as a non-unital `⋆`-algebra homomorphism. -/
def inrStarAlgHom (R m : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun N := blockDiag 0 N
  map_smul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp
  map_mul' _ _ := by simp
  map_star' _ := by simp

@[simp] theorem inrStarAlgHom_apply [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (N : CStarMatrix n n A) :
    inrStarAlgHom R m N = blockDiag 0 N := (rfl)

/-- Diagonal `(i, i)`-corner embedding `a ↦ single i i a` of `A` into `CStarMatrix n n A`. -/
def singleStarAlgHom (R : Type*) [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) :
    A →⋆ₙₐ[R] CStarMatrix n n A where
  toFun a := ofMatrix (Matrix.single i i a)
  map_smul' _ _ := by ext; simp [Matrix.single_apply]
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [Matrix.single_apply, ite_add_zero]
  map_mul' _ _ := ofMatrix.symm.injective (by simp)
  map_star' _ := by
    ext x y
    rw [star_apply]
    simp only [ofMatrix_apply, Matrix.single_apply, and_comm]
    split_ifs <;> simp

@[simp] theorem singleStarAlgHom_apply [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) (a : A) :
    singleStarAlgHom R i a = ofMatrix (Matrix.single i i a) := (rfl)

theorem singleStarAlgHom_injective [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) :
    Function.Injective (singleStarAlgHom R i : A → CStarMatrix n n A) := fun _ _ h => by
  simpa using congr_fun (congr_fun (congrArg ofMatrix.symm h) i) i

end Blocks

section Amplify

variable {k l m n R A : Type*}

/-- Finite block-diagonal amplification `1_k ⊗ M` of a rectangular `M : CStarMatrix m n A`,
placing a copy of `M` in each `(i, i)` block for `i : k` and `0` off the `k`-diagonal. -/
def amplify (k : Type*) [DecidableEq k] [Zero A] (M : CStarMatrix m n A) :
    CStarMatrix (k × m) (k × n) A :=
  ofMatrix fun i j => if i.1 = j.1 then M i.2 j.2 else 0

@[simp] theorem amplify_apply [DecidableEq k] [Zero A] (M : CStarMatrix m n A)
    (i : k × m) (j : k × n) :
    amplify k M i j = if i.1 = j.1 then M i.2 j.2 else 0 := (rfl)

@[simp] theorem amplify_zero [DecidableEq k] [Zero A] :
    amplify k (0 : CStarMatrix m n A) = 0 := by ext; simp

@[simp] theorem amplify_one [DecidableEq k] [DecidableEq n] [Zero A] [One A] :
    amplify k (1 : CStarMatrix n n A) = 1 := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [one_apply, Prod.ext_iff, ite_and]

@[simp] theorem amplify_add [DecidableEq k] [AddZeroClass A] (M N : CStarMatrix m n A) :
    amplify k (M + N) = amplify k M + amplify k N := by
  ext i j; by_cases h : i.1 = j.1 <;> simp [h]

@[simp] theorem amplify_neg [DecidableEq k] [SubtractionMonoid A] (M : CStarMatrix m n A) :
    amplify k (-M) = -amplify k M := by ext i j; by_cases h : i.1 = j.1 <;> simp [h]

@[simp] theorem amplify_sub [DecidableEq k] [AddGroup A] (M N : CStarMatrix m n A) :
    amplify k (M - N) = amplify k M - amplify k N := by
  ext i j; by_cases h : i.1 = j.1 <;> simp [h]

@[simp] theorem amplify_smul [DecidableEq k] [Zero A] [SMulZeroClass R A]
    (r : R) (M : CStarMatrix m n A) :
    amplify k (r • M) = r • amplify k M := by ext i j; by_cases h : i.1 = j.1 <;> simp [h]

@[simp] theorem amplify_mul [Fintype k] [DecidableEq k] [Fintype m] [NonUnitalNonAssocSemiring A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    amplify k (M * N) = amplify k M * amplify k N := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [amplify_apply, mul_apply, Fintype.sum_prod_type]
  by_cases hij : i₁ = j₁
  · subst hij
    simp only [↓reduceIte]
    rw [Finset.sum_eq_single i₁ (fun x _ hx => by simp [hx.symm]) (by simp)]
    simp
  · simp only [hij, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    by_cases hix : i₁ = x
    · subst hix; simp [hij]
    · simp [hix]

@[simp] theorem amplify_conjTranspose [DecidableEq k] [AddMonoid A] [StarAddMonoid A]
    (M : CStarMatrix m n A) :
    (amplify k M).conjTranspose = amplify k M.conjTranspose := by
  ext ⟨i₁, _⟩ ⟨j₁, _⟩; by_cases h : i₁ = j₁ <;> simp [h, eq_comm]

@[simp] theorem star_amplify [DecidableEq k] [AddMonoid A] [StarAddMonoid A]
    (M : CStarMatrix n n A) : star (amplify k M) = amplify k (star M) :=
  amplify_conjTranspose M

theorem amplify_injective [DecidableEq k] [Nonempty k] [Zero A] :
    Function.Injective (amplify k : CStarMatrix m n A → CStarMatrix (k × m) (k × n) A) := by
  obtain ⟨x⟩ := ‹Nonempty k›
  exact fun _ _ h => ext fun i j => by simpa using congr_fun (congr_fun h (x, i)) (x, j)

/-- Finite block-diagonal amplification bundled as a non-unital `⋆`-algebra homomorphism. -/
def amplifyStarAlgHom (R k : Type*) [Fintype k] [DecidableEq k] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (k × n) (k × n) A where
  toFun := amplify k
  map_smul' := amplify_smul
  map_zero' := amplify_zero
  map_add' := amplify_add
  map_mul' := amplify_mul
  map_star' M := (star_amplify M).symm

@[simp] theorem amplifyStarAlgHom_apply [Fintype k] [DecidableEq k] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (M : CStarMatrix n n A) :
    amplifyStarAlgHom R k M = amplify k M := (rfl)

/-- Unital finite block-diagonal amplification bundled as a `⋆`-algebra homomorphism. -/
def amplifyUnitalStarAlgHom (R k : Type*) [Fintype k] [DecidableEq k] [Fintype n] [DecidableEq n]
    [CommSemiring R] [Semiring A] [Algebra R A] [StarAddMonoid A] :
    CStarMatrix n n A →⋆ₐ[R] CStarMatrix (k × n) (k × n) A :=
  { amplifyStarAlgHom R k with
    map_one' := amplify_one
    commutes' r := by ext ⟨_, _⟩ ⟨_, _⟩; simp [algebraMap_apply, Prod.ext_iff, ite_and] }

@[simp] theorem amplifyUnitalStarAlgHom_apply [Fintype k] [DecidableEq k] [Fintype n]
    [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] [StarAddMonoid A]
    (M : CStarMatrix n n A) : amplifyUnitalStarAlgHom R k M = amplify k M := (rfl)

end Amplify

section Norms

variable {k l m n o A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- `toCLM` reverses rectangular matrix multiplication into operator composition. -/
theorem toCLM_mul [Fintype l] [Fintype m] (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    toCLM (M * N) = (toCLM N).comp (toCLM M) := by
  ext v j
  simp only [ContinuousLinearMap.comp_apply, toCLM_apply_eq_sum,
    WithCStarModule.equiv_symm_pi_apply, mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- Rectangular submultiplicativity of the `CStarMatrix` operator norm. -/
theorem norm_mul_le [Fintype l] [Fintype m] [Fintype n]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : ‖M * N‖ ≤ ‖M‖ * ‖N‖ := by
  rw [norm_def, norm_def, norm_def, toCLM_mul, mul_comm]
  exact ContinuousLinearMap.opNorm_comp_le (toCLM N) (toCLM M)

private theorem norm_conjTranspose_le [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ ≤ ‖M‖ := by
  refine norm_le_of_forall_inner_le (C := ‖M‖₊) fun v w => ?_
  have hinner : ⟪w, toCLM M.conjTranspose v⟫_A = ⟪toCLM M w, v⟫_A :=
    inner_toCLM_conjTranspose_right (M := M)
  calc ‖⟪w, toCLM M.conjTranspose v⟫_A‖
      = ‖⟪toCLM M w, v⟫_A‖ := by rw [hinner]
    _ ≤ (‖toCLM M‖ * ‖w‖) * ‖v‖ :=
        (CStarModule.norm_inner_le _).trans (by gcongr; exact (toCLM M).le_opNorm w)
    _ = (‖M‖₊ : ℝ) * ‖v‖ * ‖w‖ := by simp only [coe_nnNorm, norm_def]; ring

/-- Conjugate transposition on rectangular `CStarMatrix` is isometric. -/
@[simp] theorem norm_conjTranspose [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ = ‖M‖ :=
  le_antisymm (norm_conjTranspose_le M) (by simpa using norm_conjTranspose_le M.conjTranspose)

/-- Rectangular C⋆-identity `‖M * M.conjTranspose‖ = ‖M‖ ^ 2`. -/
@[simp] theorem norm_self_mul_conjTranspose [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M * M.conjTranspose‖ = ‖M‖ ^ 2 := by
  refine le_antisymm (by simpa [sq] using norm_mul_le M M.conjTranspose) ?_
  have hsqrt : ‖M‖ ≤ √‖M * M.conjTranspose‖ := by
    rw [norm_def, ContinuousLinearMap.opNorm_le_iff (by positivity)]
    intro v
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A), ← inner_toCLM_conjTranspose_right]
    have hcomp : toCLM M.conjTranspose (toCLM M v) = toCLM (M * M.conjTranspose) v := by
      rw [toCLM_mul, ContinuousLinearMap.comp_apply]
    have h1 : ‖⟪v, toCLM M.conjTranspose (toCLM M v)⟫_A‖ ≤ ‖M * M.conjTranspose‖ * ‖v‖ ^ 2 := by
      rw [hcomp]
      refine (CStarModule.norm_inner_le _).trans ?_
      calc ‖v‖ * ‖toCLM (M * M.conjTranspose) v‖
          ≤ ‖v‖ * (‖toCLM (M * M.conjTranspose)‖ * ‖v‖) := by
            gcongr; exact (toCLM (M * M.conjTranspose)).le_opNorm v
        _ = ‖M * M.conjTranspose‖ * ‖v‖ ^ 2 := by rw [← norm_def]; ring
    rw [show ‖v‖ = √(‖v‖ ^ 2) by simp, ← Real.sqrt_mul (norm_nonneg _)]
    exact Real.sqrt_le_sqrt h1
  have hsq := mul_self_le_mul_self (norm_nonneg M) hsqrt
  rwa [Real.mul_self_sqrt (norm_nonneg _), ← sq] at hsq

/-- Rectangular C⋆-identity `‖M.conjTranspose * M‖ = ‖M‖ ^ 2`. -/
@[simp] theorem norm_conjTranspose_mul_self [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose * M‖ = ‖M‖ ^ 2 := by simpa using norm_self_mul_conjTranspose M.conjTranspose

@[simp] theorem norm_reindexₐ [Fintype m] [Fintype n] (e : m ≃ n) (M : CStarMatrix m m A) :
    ‖reindexₐ ℂ A e M‖ = ‖M‖ :=
  StarAlgEquiv.norm_map (reindexₐ ℂ A e) M

/-- `reindexₗ` along arbitrary row and column equivalences is isometric. -/
@[simp] theorem norm_reindexₗ [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) : ‖reindexₗ ℂ A eₘ eₙ M‖ = ‖M‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  calc ‖reindexₗ ℂ A eₘ eₙ M‖ ^ 2
      = ‖(reindexₗ ℂ A eₘ eₙ M).conjTranspose * reindexₗ ℂ A eₘ eₙ M‖ :=
        (norm_conjTranspose_mul_self _).symm
    _ = ‖reindexₐ ℂ A eₙ (M.conjTranspose * M)‖ := by rw [reindexₗ_conjTranspose, reindexₗ_mul]; rfl
    _ = ‖M‖ ^ 2 := by rw [norm_reindexₐ, norm_conjTranspose_mul_self]

/-- The operator norm of a block-diagonal `CStarMatrix` is the maximum of the norms of its blocks.
-/
@[simp] theorem norm_blockDiag [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (M : CStarMatrix m l A) (N : CStarMatrix o n A) : ‖blockDiag M N‖ = max ‖M‖ ‖N‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (le_max_of_le_left (norm_nonneg M))).mp ?_
  have hsq : ‖blockDiag (M.conjTranspose * M) (N.conjTranspose * N)‖ =
      max ‖M.conjTranspose * M‖ ‖N.conjTranspose * N‖ := by
    simpa [Prod.norm_def] using
      NonUnitalStarAlgHom.norm_map (blockDiagStarAlgHom ℂ (m := l) (n := n) (A := A))
        blockDiagStarAlgHom_injective (M.conjTranspose * M, N.conjTranspose * N)
  rw [← norm_conjTranspose_mul_self, blockDiag_conjTranspose, blockDiag_mul, hsq,
    norm_conjTranspose_mul_self, norm_conjTranspose_mul_self]
  rcases le_total ‖M‖ ‖N‖ with h | h
  · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ (norm_nonneg M) h 2)]
  · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ (norm_nonneg N) h 2)]

theorem norm_blockDiag_zero_right [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (M : CStarMatrix m l A) : ‖blockDiag M (0 : CStarMatrix o n A)‖ = ‖M‖ := by simp

theorem norm_blockDiag_zero_left [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (N : CStarMatrix o n A) : ‖blockDiag (0 : CStarMatrix m l A) N‖ = ‖N‖ := by simp

/-- A matrix with a single entry `a` at `(i, j)` has operator norm `‖a‖`. -/
@[simp] theorem norm_single [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (i : m) (j : n) (a : A) : ‖ofMatrix (Matrix.single i j a)‖ = ‖a‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  have hmul : (ofMatrix (Matrix.single i j a)).conjTranspose * ofMatrix (Matrix.single i j a) =
      singleStarAlgHom ℂ j (star a * a) :=
    ofMatrix.symm.injective (by simp [Matrix.conjTranspose_single])
  rw [← norm_conjTranspose_mul_self, hmul,
    NonUnitalStarAlgHom.norm_map (singleStarAlgHom ℂ (A := A) j) (singleStarAlgHom_injective j) _,
    CStarRing.norm_star_mul_self, sq]

/-- Finite block-diagonal amplification over a nonempty index type `k` is isometric. -/
@[simp] theorem norm_amplify [Fintype k] [DecidableEq k] [Nonempty k] [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) : ‖amplify k M‖ = ‖M‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  have hinj : Function.Injective
      (amplifyStarAlgHom ℂ k : CStarMatrix n n A → CStarMatrix (k × n) (k × n) A) :=
    amplify_injective
  rw [← norm_conjTranspose_mul_self, amplify_conjTranspose, ← amplify_mul,
    ← amplifyStarAlgHom_apply (R := ℂ),
    NonUnitalStarAlgHom.norm_map (amplifyStarAlgHom ℂ k) hinj _, norm_conjTranspose_mul_self]

theorem norm_amplify_le [Fintype k] [DecidableEq k] [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) : ‖amplify k M‖ ≤ ‖M‖ := by
  rcases isEmpty_or_nonempty k with hk | hk
  · rw [show amplify k M = 0 from ext fun ⟨i, _⟩ _ => isEmptyElim i, norm_zero]
    exact norm_nonneg M
  · exact (norm_amplify M).le

end Norms

section Continuity

variable {l m n o A : Type*} [NonUnitalCStarAlgebra A]

/-- A four-block `CStarMatrix` family is continuous when each of its four blocks is continuous. -/
theorem continuous_fromBlocks {X : Type*} [TopologicalSpace X]
    {f₁₁ : X → CStarMatrix m l A} {f₁₂ : X → CStarMatrix m n A}
    {f₂₁ : X → CStarMatrix o l A} {f₂₂ : X → CStarMatrix o n A}
    (hf₁₁ : Continuous f₁₁) (hf₁₂ : Continuous f₁₂)
    (hf₂₁ : Continuous f₂₁) (hf₂₂ : Continuous f₂₂) :
    Continuous fun x => fromBlocks (f₁₁ x) (f₁₂ x) (f₂₁ x) (f₂₂ x) := by
  refine ofMatrixL.continuous.comp (continuous_pi fun i => continuous_pi fun j => ?_)
  rcases i with i | i <;> rcases j with j | j
  · exact (continuous_apply j).comp
      ((continuous_apply i).comp (ofMatrixL.symm.continuous.comp hf₁₁))
  · exact (continuous_apply j).comp
      ((continuous_apply i).comp (ofMatrixL.symm.continuous.comp hf₁₂))
  · exact (continuous_apply j).comp
      ((continuous_apply i).comp (ofMatrixL.symm.continuous.comp hf₂₁))
  · exact (continuous_apply j).comp
      ((continuous_apply i).comp (ofMatrixL.symm.continuous.comp hf₂₂))

end Continuity

end CStarMatrix
