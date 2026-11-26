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

/-!
# Block sums, corner inclusions, reindexing, and rectangular C⋆-norms for `CStarMatrix`

Mathlib constructs the operator norm on rectangular matrices `CStarMatrix m n A` over a non-unital
C⋆-algebra `A` and establishes the `CStarRing` structure in the square case `m = n`. Operator
K-theory works systematically with `2 × 2` block matrices over `m ⊕ n`, corner embeddings, finite
reindexings, and rectangular partial isometries between finite index sets of different
cardinalities. This file develops that block and reindexing calculus together with the rectangular
and block-diagonal operator-norm identities.

## Main definitions

* `CStarMatrix.fromBlocks`: `2 × 2` block matrices `CStarMatrix (m ⊕ n) (l ⊕ o) A`.
* `CStarMatrix.blockDiagHom`: the orthogonal block-diagonal embedding
  `CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A`.
* `CStarMatrix.inlCorner`, `CStarMatrix.inrCorner`, `CStarMatrix.singleCorner`: top-left block,
  bottom-right block, and `(i, i)`-entry corner embeddings as non-unital `⋆`-algebra homomorphisms.

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
  `CStarMatrix.norm_reindexₗ`: corner inclusions and finite reindexings are isometries.

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

section BlocksAndReindex

variable {k l m n o p R A B : Type*}

section FromBlocks

variable (M₁₁ N₁₁ : CStarMatrix m l A) (M₁₂ N₁₂ : CStarMatrix m o A)
  (M₂₁ N₂₁ : CStarMatrix n l A) (M₂₂ N₂₂ : CStarMatrix n o A)

/-- Assemble four blocks into a `(m ⊕ n) × (l ⊕ o)` `CStarMatrix`. -/
def fromBlocks : CStarMatrix (m ⊕ n) (l ⊕ o) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
    (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂))

/-- Reading `CStarMatrix.fromBlocks` as an ordinary matrix gives `Matrix.fromBlocks`. -/
@[simp]
theorem ofMatrix_symm_fromBlocks :
    ofMatrix.symm (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
        (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂) := (rfl)

/-- Top-left `(Sum.inl i, Sum.inl j)` entry of `fromBlocks`. -/
@[simp]
theorem fromBlocks_apply₁₁ (i : m) (j : l) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inl j) = M₁₁ i j := (rfl)

/-- Top-right `(Sum.inl i, Sum.inr j)` entry of `fromBlocks`. -/
@[simp]
theorem fromBlocks_apply₁₂ (i : m) (j : o) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inr j) = M₁₂ i j := (rfl)

/-- Bottom-left `(Sum.inr i, Sum.inl j)` entry of `fromBlocks`. -/
@[simp]
theorem fromBlocks_apply₂₁ (i : n) (j : l) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inl j) = M₂₁ i j := (rfl)

/-- Bottom-right `(Sum.inr i, Sum.inr j)` entry of `fromBlocks`. -/
@[simp]
theorem fromBlocks_apply₂₂ (i : n) (j : o) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inr j) = M₂₂ i j := (rfl)

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
theorem fromBlocks_add [Add A] :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ + fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ + N₁₁) (M₁₂ + N₁₂) (M₂₁ + N₂₁) (M₂₂ + N₂₂) := by
  ext (i | i) (j | j) <;> rfl

/-- `fromBlocks` commutes with matrix negation. -/
@[simp]
theorem fromBlocks_neg [Neg A] :
    -fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks (-M₁₁) (-M₁₂) (-M₂₁) (-M₂₂) := by
  ext (i | i) (j | j) <;> rfl

/-- `fromBlocks` commutes with matrix subtraction. -/
@[simp]
theorem fromBlocks_sub [Sub A] :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ - fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ - N₁₁) (M₁₂ - N₁₂) (M₂₁ - N₂₁) (M₂₂ - N₂₂) := by
  ext (i | i) (j | j) <;> rfl

/-- `fromBlocks` commutes with scalar multiplication. -/
@[simp]
theorem fromBlocks_smul [SMul R A] (r : R) :
    r • fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ =
      fromBlocks (r • M₁₁) (r • M₁₂) (r • M₂₁) (r • M₂₂) := by
  ext (i | i) (j | j) <;> rfl

/-- Block-by-block multiplication formula for `CStarMatrix.fromBlocks`. -/
@[simp]
theorem fromBlocks_mul [Fintype l] [Fintype o] [NonUnitalNonAssocSemiring A]
    (P₁₁ : CStarMatrix l k A) (P₁₂ : CStarMatrix l p A)
    (P₂₁ : CStarMatrix o k A) (P₂₂ : CStarMatrix o p A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromBlocks P₁₁ P₁₂ P₂₁ P₂₂ =
      fromBlocks (M₁₁ * P₁₁ + M₁₂ * P₂₁) (M₁₁ * P₁₂ + M₁₂ * P₂₂)
        (M₂₁ * P₁₁ + M₂₂ * P₂₁) (M₂₁ * P₁₂ + M₂₂ * P₂₂) :=
  ofMatrix.symm.injective (Matrix.fromBlocks_multiply _ _ _ _ _ _ _ _)

/-- Conjugate transpose of a `2 × 2` block matrix transposes the block layout and takes
`conjTranspose` of each block. -/
@[simp]
theorem conjTranspose_fromBlocks [Star A] :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).conjTranspose =
      fromBlocks M₁₁.conjTranspose M₂₁.conjTranspose M₁₂.conjTranspose M₂₂.conjTranspose :=
  ofMatrix.symm.injective (Matrix.fromBlocks_conjTranspose _ _ _ _)

/-- Two block matrices are equal iff all four blocks are equal. -/
theorem fromBlocks_inj {M₁₁ N₁₁ : CStarMatrix m l A} {M₁₂ N₁₂ : CStarMatrix m o A}
    {M₂₁ N₂₁ : CStarMatrix n l A} {M₂₂ N₂₂ : CStarMatrix n o A} :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ ↔
      M₁₁ = N₁₁ ∧ M₁₂ = N₁₂ ∧ M₂₁ = N₂₁ ∧ M₂₂ = N₂₂ := by
  simp only [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_fromBlocks, Matrix.fromBlocks_inj]

end FromBlocks

/-- Star of a square `2 × 2` block matrix. -/
@[simp]
theorem star_fromBlocks [Star A] (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
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

/-- A block-diagonal matrix `fromBlocks P 0 0 Q` is a star projection iff both `P` and `Q` are. -/
@[simp]
theorem isStarProjection_fromBlocks_zero₁₂_zero₂₁ [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {P : CStarMatrix m m A} {Q : CStarMatrix n n A} :
    IsStarProjection (fromBlocks P 0 0 Q) ↔ IsStarProjection P ∧ IsStarProjection Q := by
  simp only [isStarProjection_iff, IsIdempotentElem, isSelfAdjoint_iff, fromBlocks_mul,
    CStarMatrix.mul_zero, CStarMatrix.zero_mul, add_zero, zero_add, star_fromBlocks,
    conjTranspose_zero, fromBlocks_inj, true_and]
  tauto

section Corners

variable [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]

section SumCorners

variable [Fintype m]

/-- Orthogonal block-diagonal embedding `(P, Q) ↦ fromBlocks P 0 0 Q` as a non-unital `⋆`-algebra
homomorphism. -/
def blockDiagHom :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun PQ := fromBlocks PQ.1 0 0 PQ.2
  map_smul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp
  map_mul' _ _ := by simp
  map_star' _ := by simp

/-- Evaluation formula for `CStarMatrix.blockDiagHom`. -/
@[simp]
theorem blockDiagHom_apply (PQ : CStarMatrix m m A × CStarMatrix n n A) :
    blockDiagHom (R := R) PQ = fromBlocks PQ.1 0 0 PQ.2 := (rfl)

/-- `CStarMatrix.blockDiagHom` is injective. -/
theorem blockDiagHom_injective :
    Function.Injective (blockDiagHom (R := R) (m := m) (n := n) (A := A)) := by
  rintro ⟨P₁, Q₁⟩ ⟨P₂, Q₂⟩ h
  simp only [blockDiagHom_apply, fromBlocks_inj, true_and] at h
  exact Prod.ext h.1 h.2

/-- Top-left block corner inclusion `M ↦ fromBlocks M 0 0 0`. -/
def inlCorner (n : Type*) [Fintype n] :
    CStarMatrix m m A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (blockDiagHom (R := R)).comp (NonUnitalStarAlgHom.inl R (CStarMatrix m m A) (CStarMatrix n n A))

/-- Evaluation formula for `CStarMatrix.inlCorner`. -/
@[simp]
theorem inlCorner_apply (M : CStarMatrix m m A) :
    inlCorner (R := R) n M = fromBlocks M 0 0 0 := (rfl)

/-- `CStarMatrix.inlCorner` is injective. -/
theorem inlCorner_injective :
    Function.Injective (inlCorner (R := R) (m := m) n (A := A)) := fun _ _ h ↦
  (fromBlocks_inj.mp h).1

/-- Bottom-right block corner inclusion `N ↦ fromBlocks 0 0 0 N`. -/
def inrCorner (m : Type*) [Fintype m] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (blockDiagHom (R := R)).comp (NonUnitalStarAlgHom.inr R (CStarMatrix m m A) (CStarMatrix n n A))

/-- Evaluation formula for `CStarMatrix.inrCorner`. -/
@[simp]
theorem inrCorner_apply (N : CStarMatrix n n A) :
    inrCorner (R := R) m N = fromBlocks 0 0 0 N := (rfl)

/-- `CStarMatrix.inrCorner` is injective. -/
theorem inrCorner_injective :
    Function.Injective (inrCorner (R := R) m (n := n) (A := A)) := fun _ _ h ↦
  (fromBlocks_inj.mp h).2.2.2

/-- Top-left and bottom-right corner inclusions are mutually orthogonal. -/
theorem inlCorner_mul_inrCorner (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    inlCorner (R := R) n M * inrCorner (R := R) m N = 0 := by simp

/-- Bottom-right and top-left corner inclusions are mutually orthogonal. -/
theorem inrCorner_mul_inlCorner (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    inrCorner (R := R) m N * inlCorner (R := R) n M = 0 := by simp

end SumCorners

section SingleCorner

variable [DecidableEq n]

/-- Single diagonal-entry `(i, i)` corner inclusion `A →⋆ₙₐ[R] CStarMatrix n n A`. -/
def singleCorner (i : n) : A →⋆ₙₐ[R] CStarMatrix n n A where
  toFun a := ofMatrix (Matrix.single i i a)
  map_smul' r a := by ext j k; simp [Matrix.single]
  map_zero' := by ext j k; simp
  map_add' a b := by ext j k; simp [Matrix.single_add]
  map_mul' a b := ofMatrix.symm.injective (by simp [Matrix.single_mul_single_same])
  map_star' a := by
    rw [star_eq_conjTranspose]
    exact ofMatrix.symm.injective (by simp)

/-- Entrywise formula for `CStarMatrix.singleCorner`. -/
@[simp]
theorem singleCorner_apply (i : n) (a : A) (j k : n) :
    singleCorner (R := R) i a j k = Matrix.single i i a j k := (rfl)

/-- The `(i, i)` entry of `singleCorner i a` is `a`. -/
theorem singleCorner_apply_same (i : n) (a : A) :
    singleCorner (R := R) i a i i = a := by simp

/-- `CStarMatrix.singleCorner` is injective. -/
theorem singleCorner_injective (i : n) :
    Function.Injective (singleCorner (R := R) (A := A) i) := fun a b h ↦ by
  simpa only [singleCorner_apply_same] using congr_fun₂ h i i

/-- `singleCorner i a` is a star projection iff `a` is a star projection. -/
@[simp]
theorem isStarProjection_singleCorner (i : n) {a : A} :
    IsStarProjection (singleCorner (R := R) i a) ↔ IsStarProjection a := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.map (singleCorner (R := R) i)⟩
  · exact singleCorner_injective (R := R) i (by rw [map_mul, h.isIdempotentElem.eq])
  · exact singleCorner_injective (R := R) i (by rw [map_star, h.isSelfAdjoint.star_eq])

end SingleCorner

end Corners

/-- Reindexing along identity equivalences on both sides is the identity map. -/
@[simp]
theorem reindexₗ_refl_refl [Semiring R] [AddCommMonoid A] [Module R A] (M : CStarMatrix m n A) :
    reindexₗ R A (Equiv.refl m) (Equiv.refl n) M = M := (rfl)

/-- On square matrices with equal row and column equivalences, `reindexₗ` agrees with
`reindexₐ`. -/
theorem reindexₗ_eq_reindexₐ [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] [Star A] (e : m ≃ n) (M : CStarMatrix m m A) :
    reindexₗ R A e e M = reindexₐ R A e M := (rfl)

/-- Rectangular reindexing commutes with `conjTranspose`. -/
@[simp]
theorem conjTranspose_reindexₗ [Semiring R] [AddCommMonoid A] [Module R A] [Star A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    (reindexₗ R A eₘ eₙ M).conjTranspose = reindexₗ R A eₙ eₘ M.conjTranspose := (rfl)

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

end BlocksAndReindex

section RectangularProperStar

variable {m n A : Type*} [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [IsProperStar A]

/-- For a rectangular `CStarMatrix`, `M.conjTranspose * M = 0` iff `M = 0`. -/
@[simp]
theorem conjTranspose_mul_self_eq_zero [Fintype m] {M : CStarMatrix m n A} :
    M.conjTranspose * M = 0 ↔ M = 0 := by
  rw [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_mul, ofMatrix_symm_conjTranspose,
    ← ofMatrix.symm.injective.eq_iff (a := M)]
  exact Matrix.conjTranspose_mul_self_eq_zero

/-- For a rectangular `CStarMatrix`, `M * M.conjTranspose = 0` iff `M = 0`. -/
@[simp]
theorem self_mul_conjTranspose_eq_zero [Fintype n] {M : CStarMatrix m n A} :
    M * M.conjTranspose = 0 ↔ M = 0 := by
  rw [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_mul, ofMatrix_symm_conjTranspose,
    ← ofMatrix.symm.injective.eq_iff (a := M)]
  exact Matrix.self_mul_conjTranspose_eq_zero

/-- Square `CStarMatrix`es over a star-ordered ring with proper star have a proper star. -/
instance instIsProperStar [Fintype n] : IsProperStar (CStarMatrix n n A) where
  eq_zero_of_star_mul_self_eq_zero := by simp [star_eq_conjTranspose]

/-- **Rectangular partial-isometry identity**: if `v.conjTranspose * v` is idempotent for
`v : CStarMatrix m n A`, then `v * v.conjTranspose * v = v`. -/
theorem mul_conjTranspose_mul_self_of_isIdempotentElem [Fintype m] [Fintype n]
    {v : CStarMatrix m n A} (hv : IsIdempotentElem (v.conjTranspose * v)) :
    v * v.conjTranspose * v = v := by
  simpa only [← mul_assoc_rectangular] using mul_eq_self_of_conjTranspose_mul_eq v hv rfl

/-- Dual rectangular partial-isometry identity: if `v.conjTranspose * v` is idempotent, then
`v.conjTranspose * v * v.conjTranspose = v.conjTranspose`. -/
theorem conjTranspose_mul_self_mul_conjTranspose_of_isIdempotentElem [Fintype m] [Fintype n]
    {v : CStarMatrix m n A} (hv : IsIdempotentElem (v.conjTranspose * v)) :
    v.conjTranspose * v * v.conjTranspose = v.conjTranspose := by
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc_rectangular] using
    congrArg conjTranspose (mul_conjTranspose_mul_self_of_isIdempotentElem hv)

/-- If `v.conjTranspose * v` is idempotent for rectangular `v : CStarMatrix m n A`, then
`v * v.conjTranspose` is a star projection. -/
theorem isStarProjection_mul_conjTranspose_self_of_isIdempotentElem [Fintype m] [Fintype n]
    {v : CStarMatrix m n A} (hv : IsIdempotentElem (v.conjTranspose * v)) :
    IsStarProjection (v * v.conjTranspose) where
  isIdempotentElem := by
    rw [IsIdempotentElem, ← mul_assoc_rectangular (v * v.conjTranspose) v v.conjTranspose,
      mul_conjTranspose_mul_self_of_isIdempotentElem hv]
  isSelfAdjoint := by
    rw [isSelfAdjoint_iff, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

end RectangularProperStar

/-- Rectangular matrix multiplication corresponds to composition of `toCLM` operators in reverse
order: `toCLM (M * N) = (toCLM N).comp (toCLM M)`. -/
@[simp]
theorem toCLM_mul {l m n A : Type*} [NonUnitalCStarAlgebra A] [Fintype l] [Fintype m]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    toCLM (M * N) = (toCLM N).comp (toCLM M) := by
  ext v k
  simp only [ContinuousLinearMap.comp_apply, toCLM_apply_eq_sum,
    WithCStarModule.equiv_symm_pi_apply, mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

section RectangularNorm

variable {l m n o m₁ m₂ n₁ n₂ A : Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Operator norm submultiplicativity `‖M * N‖ ≤ ‖M‖ * ‖N‖` for rectangular `CStarMatrix`es. -/
protected theorem norm_mul_le [Fintype l] [Fintype m] [Fintype n]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    ‖M * N‖ ≤ ‖M‖ * ‖N‖ := by
  rw [norm_def, norm_def, norm_def, toCLM_mul, mul_comm]
  exact ContinuousLinearMap.opNorm_comp_le (toCLM N) (toCLM M)

/-- Lower C⋆-estimate `‖M‖ ^ 2 ≤ ‖M * M.conjTranspose‖` for a rectangular `CStarMatrix`. -/
theorem norm_sq_le_norm_mul_conjTranspose_self [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
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
            gcongr; rw [← ContinuousLinearMap.comp_apply]; exact ContinuousLinearMap.le_opNorm _ v
        _ = ‖M * M.conjTranspose‖ * ‖v‖ ^ 2 := by rw [← toCLM_mul, ← norm_def]; ring
    have hv_sq : ‖v‖ = √(‖v‖ ^ 2) := by simp
    rw [hv_sq, ← Real.sqrt_mul (norm_nonneg _)]
    exact Real.sqrt_le_sqrt h₁
  have hsq := mul_self_le_mul_self (norm_nonneg M) hmain
  rwa [← sq, Real.mul_self_sqrt (norm_nonneg _)] at hsq

private theorem norm_conjTranspose_le [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ ≤ ‖M‖ := by
  have hnn : 0 ≤ ‖M.conjTranspose‖ := by rw [norm_def]; exact ContinuousLinearMap.opNorm_nonneg _
  obtain h0 | hpos := hnn.eq_or_lt
  · rw [← h0, norm_def]; exact ContinuousLinearMap.opNorm_nonneg _
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
    rw [← norm_conjTranspose_mul_self, one_pow]; exact hp.norm_le
  exact (sq_le_sq₀ (norm_nonneg v) zero_le_one).mp hsq

/-- Exact C⋆-norm identity for a block-diagonal matrix with arbitrary rectangular blocks:
`‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖`. -/
@[simp]
theorem norm_fromBlocks_zero₁₂_zero₂₁ [Fintype m₁] [Fintype n₁] [Fintype m₂] [Fintype n₂]
    (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₂ n₂ A) :
    ‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖ := by
  have hsq_case : ∀ (P : CStarMatrix m₁ m₁ A) (Q : CStarMatrix m₂ m₂ A),
      ‖fromBlocks P 0 0 Q‖ = max ‖P‖ ‖Q‖ := fun P Q ↦ by
    rw [← blockDiagHom_apply (R := ℂ) (P, Q),
      NonUnitalStarAlgHom.norm_map (blockDiagHom (R := ℂ)) (blockDiagHom_injective (R := ℂ)) (P, Q),
      Prod.norm_mk]
  have h_eq : ‖fromBlocks M 0 0 N‖ ^ 2 = (max ‖M‖ ‖N‖) ^ 2 := by
    calc ‖fromBlocks M 0 0 N‖ ^ 2
        = ‖fromBlocks M 0 0 N * (fromBlocks M 0 0 N).conjTranspose‖ :=
          (norm_mul_conjTranspose_self _).symm
      _ = ‖fromBlocks (M * M.conjTranspose) 0 0 (N * N.conjTranspose)‖ := by simp
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
