/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Data.Matrix.Block
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Block matrices, corners, amplification, and rectangular norms for C⋆-matrices

This file develops the finite matrix calculus on `CStarMatrix m n A` over a (possibly non-unital)
complex C⋆-algebra `A`:

* Rectangular multiplication and conjugate-transpose identities (`mul_assoc`, `conjTranspose_mul`,
  `conjTranspose_conjTranspose`, `one_mul`, `mul_one`, and compatibility with entrywise maps).
* Rectangular C⋆-norm identities (`norm_mul_le`, `norm_conjTranspose`,
  `norm_mul_conjTranspose_self`, `norm_conjTranspose_mul_self`, and vanishing of `Mᴴ * M` iff
  `M = 0`).
* Unital matrix amplification `mapₐ` and functoriality of `mapₙₐ`.
* Block matrices `fromBlocks`, diagonal block sums `blockDiagHom`, and corner inclusions
  `cornerInl`, `cornerInr`, with their norm, star, projection, and unitary characterizations:
  `‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖` and `‖cornerInl M‖ = ‖M‖`.
* Reindexing norm invariance for rectangular matrices, associativity and commutativity of block
  direct sums under `reindexₐ`, and implementation of reindexing by permutation matrices
  `reindexMatrix` and permutation unitaries `permUnitary` when `A` is unital.

## Main definitions

* `CStarMatrix.mapₐ`: unital ⋆-algebra homomorphism amplification to `CStarMatrix n n A`.
* `CStarMatrix.fromBlocks`: block matrix constructor on `CStarMatrix`.
* `CStarMatrix.blockDiagHom`: injective non-unital ⋆-algebra homomorphism sending `(M, N)` to
  `fromBlocks M 0 0 N`.
* `CStarMatrix.cornerInl`, `CStarMatrix.cornerInr`: the upper-left and lower-right corner
  inclusions `M ↦ fromBlocks M 0 0 0` and `N ↦ fromBlocks 0 0 0 N`.
* `CStarMatrix.reindexMatrix`, `CStarMatrix.permUnitary`: permutation matrices and permutation
  unitaries implementing `reindexₐ` by conjugation over a unital coefficient ring.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Chapter III, §4.6.
-/

public section

open scoped Matrix CStarAlgebra CStarModule

namespace CStarMatrix

section RectangularAlgebra

variable {l m n o R A B : Type*}

/-- Reading a rectangular C⋆-matrix as an ordinary matrix respects conjugate transpose. -/
@[simp]
theorem ofMatrix_symm_conjTranspose [Star A] (M : CStarMatrix m n A) :
    ofMatrix.symm M.conjTranspose = (ofMatrix.symm M)ᴴ := (rfl)

/-- Wrapping an ordinary matrix respects conjugate transpose. -/
@[simp]
theorem ofMatrix_conjTranspose [Star A] (M : Matrix m n A) :
    (ofMatrix M).conjTranspose = ofMatrix Mᴴ := (rfl)

/-- Wrapping ordinary matrices respects rectangular multiplication. -/
@[simp]
theorem ofMatrix_mul [Fintype m] [Mul A] [AddCommMonoid A]
    (M : Matrix l m A) (N : Matrix m n A) :
    ofMatrix M * ofMatrix N = ofMatrix (M * N) := (rfl)

/-- Reading rectangular C⋆-matrices as ordinary matrices respects multiplication. -/
theorem ofMatrix_symm_hMul [Fintype m] [Mul A] [AddCommMonoid A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    ofMatrix.symm (M * N) = ofMatrix.symm M * ofMatrix.symm N := (rfl)

@[simp]
theorem ofMatrix_symm_zero [Zero A] :
    ofMatrix.symm (0 : CStarMatrix m n A) = 0 := (rfl)

@[simp]
theorem ofMatrix_symm_sub [Sub A] (M N : CStarMatrix m n A) :
    ofMatrix.symm (M - N) = ofMatrix.symm M - ofMatrix.symm N := (rfl)

@[simp]
theorem ofMatrix_symm_one [DecidableEq n] [Zero A] [One A] :
    ofMatrix.symm (1 : CStarMatrix n n A) = 1 := (rfl)

protected theorem sub_mul [Fintype m] [NonUnitalNonAssocRing A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (L - M) * N = L * N - M * N := by
  apply ofMatrix.symm.injective
  exact Matrix.sub_mul (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N)

protected theorem mul_sub [Fintype m] [NonUnitalNonAssocRing A]
    (L : CStarMatrix l m A) (M N : CStarMatrix m n A) :
    L * (M - N) = L * M - L * N := by
  apply ofMatrix.symm.injective
  exact Matrix.mul_sub (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N)

protected theorem neg_mul [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (-M) * N = -(M * N) := by
  apply ofMatrix.symm.injective
  exact Matrix.neg_mul (ofMatrix.symm M) (ofMatrix.symm N)

protected theorem mul_neg [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    M * (-N) = -(M * N) := by
  apply ofMatrix.symm.injective
  exact Matrix.mul_neg (ofMatrix.symm M) (ofMatrix.symm N)

@[simp]
theorem conjTranspose_conjTranspose [InvolutiveStar A] (M : CStarMatrix m n A) :
    M.conjTranspose.conjTranspose = M := by
  ext i j
  simp

@[simp]
theorem conjTranspose_add [AddMonoid A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M + N).conjTranspose = M.conjTranspose + N.conjTranspose := by
  ext i j
  simp

@[simp]
theorem conjTranspose_sub [AddGroup A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M - N).conjTranspose = M.conjTranspose - N.conjTranspose := by
  ext i j
  simp

@[simp]
theorem conjTranspose_neg [AddGroup A] [StarAddMonoid A] (M : CStarMatrix m n A) :
    (-M).conjTranspose = -M.conjTranspose := by
  ext i j
  simp

@[simp]
theorem conjTranspose_smul [Star R] [Star A] [SMul R A] [StarModule R A]
    (r : R) (M : CStarMatrix m n A) :
    (r • M).conjTranspose = star r • M.conjTranspose := by
  ext i j
  simp

@[simp]
theorem conjTranspose_one [DecidableEq n] [Semiring A] [StarRing A] :
    (1 : CStarMatrix n n A).conjTranspose = 1 := by
  ext i j
  by_cases h : i = j <;> simp [one_apply, h, eq_comm]

@[simp]
theorem conjTranspose_mul [Fintype m] [NonUnitalNonAssocSemiring A] [StarRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).conjTranspose = N.conjTranspose * M.conjTranspose := by
  apply ofMatrix.symm.injective
  exact Matrix.conjTranspose_mul (ofMatrix.symm M) (ofMatrix.symm N)

theorem conjTranspose_map {F : Type*} [Star A] [Star B] [FunLike F A B] [StarHomClass F A B]
    (f : F) (M : CStarMatrix m n A) :
    (M.map f).conjTranspose = M.conjTranspose.map f := by
  ext i j
  simp [map_star]

theorem mul_assoc [Fintype m] [Fintype n] [NonUnitalSemiring A]
    (L : CStarMatrix l m A) (M : CStarMatrix m n A) (N : CStarMatrix n o A) :
    L * M * N = L * (M * N) := by
  apply ofMatrix.symm.injective
  exact Matrix.mul_assoc (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N)

@[simp]
protected theorem one_mul [Fintype m] [DecidableEq m] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : (1 : CStarMatrix m m A) * M = M := by
  apply ofMatrix.symm.injective
  exact Matrix.one_mul (ofMatrix.symm M)

@[simp]
protected theorem mul_one [Fintype n] [DecidableEq n] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : M * (1 : CStarMatrix n n A) = M := by
  apply ofMatrix.symm.injective
  exact Matrix.mul_one (ofMatrix.symm M)

theorem map_mul {F : Type*} [Fintype m] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [FunLike F A B] [NonUnitalRingHomClass F A B]
    (f : F) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).map f = M.map f * N.map f := by
  ext i k
  simp [mul_apply, map_sum]

@[simp]
protected theorem map_zero {F : Type*} [Zero A] [Zero B] [FunLike F A B] [ZeroHomClass F A B]
    (f : F) : (0 : CStarMatrix m n A).map f = 0 := by
  ext i j
  simp [map_zero]

theorem map_add {F : Type*} [Add A] [Add B] [FunLike F A B] [AddHomClass F A B]
    (f : F) (M N : CStarMatrix m n A) :
    (M + N).map f = M.map f + N.map f := by
  ext i j
  simp

theorem map_sub {F : Type*} [AddGroup A] [AddGroup B] [FunLike F A B] [AddMonoidHomClass F A B]
    (f : F) (M N : CStarMatrix m n A) :
    (M - N).map f = M.map f - N.map f := by
  ext i j
  simp

/-- A rectangular matrix over a star-ordered ring with proper star vanishes iff `Mᴴ * M = 0`. -/
@[simp]
theorem conjTranspose_mul_self_eq_zero [Fintype m] [PartialOrder A] [NonUnitalRing A] [StarRing A]
    [StarOrderedRing A] [IsProperStar A] {M : CStarMatrix m n A} :
    M.conjTranspose * M = 0 ↔ M = 0 := by
  rw [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_hMul, ofMatrix_symm_conjTranspose,
    ofMatrix_symm_zero, Matrix.conjTranspose_mul_self_eq_zero, ← ofMatrix_symm_zero,
    ofMatrix.symm.injective.eq_iff]

/-- A rectangular matrix over a star-ordered ring with proper star vanishes iff `M * Mᴴ = 0`. -/
@[simp]
theorem self_mul_conjTranspose_eq_zero [Fintype n] [PartialOrder A] [NonUnitalRing A] [StarRing A]
    [StarOrderedRing A] [IsProperStar A] {M : CStarMatrix m n A} :
    M * M.conjTranspose = 0 ↔ M = 0 := by
  rw [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_hMul, ofMatrix_symm_conjTranspose,
    ofMatrix_symm_zero, Matrix.self_mul_conjTranspose_eq_zero, ← ofMatrix_symm_zero,
    ofMatrix.symm.injective.eq_iff]

end RectangularAlgebra

section Amplification

variable {n R A B C : Type*} [Fintype n] [Semiring R]

/-- Functoriality of `mapₙₐ` on the identity homomorphism. -/
@[simp]
theorem mapₙₐ_id [NonUnitalNonAssocSemiring A] [Module R A] [Star A] :
    mapₙₐ (n := n) (NonUnitalStarAlgHom.id R A) =
      NonUnitalStarAlgHom.id R (CStarMatrix n n A) := by
  ext M i j
  simp

/-- Functoriality of `mapₙₐ` on composition of non-unital ⋆-algebra homomorphisms. -/
@[simp]
theorem mapₙₐ_comp [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    [NonUnitalNonAssocSemiring C] [Module R C] [Star C]
    (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) :
    mapₙₐ (n := n) (g.comp f) = (mapₙₐ (n := n) g).comp (mapₙₐ (n := n) f) := by
  ext M i j
  simp

/-- Applying a unital ⋆-algebra homomorphism to every entry of a square C⋆-matrix is a unital
⋆-algebra homomorphism. -/
def mapₐ [DecidableEq n] {R : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B] (f : A →⋆ₐ[R] B) :
    CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B where
  __ := mapₙₐ f.toNonUnitalStarAlgHom
  map_one' := by
    ext i j
    by_cases h : i = j <;> simp [mapₙₐ_apply, one_apply, h]
  commutes' r := by
    ext i j
    by_cases h : i = j <;> simp [mapₙₐ_apply, algebraMap_apply, h, AlgHomClass.commutes]

@[simp]
theorem mapₐ_apply [DecidableEq n] {R : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B]
    (f : A →⋆ₐ[R] B) (M : CStarMatrix n n A) (i j : n) :
    mapₐ f M i j = f (M i j) := (rfl)

@[simp]
theorem toNonUnitalStarAlgHom_mapₐ [DecidableEq n] {R : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B] (f : A →⋆ₐ[R] B) :
    (mapₐ (n := n) f).toNonUnitalStarAlgHom = mapₙₐ f.toNonUnitalStarAlgHom := (rfl)

theorem mapₐ_eq_mapₙₐ [DecidableEq n] {R : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B] (f : A →⋆ₐ[R] B) (M : CStarMatrix n n A) :
    mapₐ f M = mapₙₐ f.toNonUnitalStarAlgHom M := (rfl)

@[simp]
theorem mapₐ_id [DecidableEq n] {R : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] :
    mapₐ (n := n) (StarAlgHom.id R A) = StarAlgHom.id R (CStarMatrix n n A) := by
  ext M i j
  simp

@[simp]
theorem mapₐ_comp [DecidableEq n] {R : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B]
    [Semiring C] [Algebra R C] [Star C]
    (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    mapₐ (n := n) (g.comp f) = (mapₐ (n := n) g).comp (mapₐ (n := n) f) := by
  ext M i j
  simp

theorem mapₙₐ_injective [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    {f : A →⋆ₙₐ[R] B} (hf : Function.Injective f) :
    Function.Injective (mapₙₐ (n := n) f) :=
  map_injective hf

theorem mapₐ_injective [DecidableEq n] {R : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B]
    {f : A →⋆ₐ[R] B} (hf : Function.Injective f) :
    Function.Injective (mapₐ (n := n) f) :=
  map_injective hf

end Amplification

section RectangularNorm

variable {l m n A : Type*}

/-- Matrix multiplication corresponds to reversed composition of `toCLM`, because `toCLM` acts on
row vectors on the right. -/
theorem toCLM_mul [Fintype l] [Fintype m] [NonUnitalCStarAlgebra A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    toCLM (M * N) = (toCLM N).comp (toCLM M) := by
  ext v k
  simp only [toCLM_apply_eq_sum, ContinuousLinearMap.comp_apply,
    WithCStarModule.equiv_symm_pi_apply, mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [_root_.mul_assoc]

private theorem toCLM_conjTranspose [Fintype n] [NonUnitalCStarAlgebra A]
    (M : CStarMatrix m n A) :
    toCLM M.conjTranspose = toCLM Mᴴ := (rfl)

variable [Fintype l] [Fintype m] [Fintype n]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Rectangular matrix multiplication in `CStarMatrix` is submultiplicative for the operator
norm. -/
theorem norm_mul_le (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    ‖M * N‖ ≤ ‖M‖ * ‖N‖ := by
  rw [norm_def, norm_def, norm_def, toCLM_mul, mul_comm]
  exact ContinuousLinearMap.opNorm_comp_le (toCLM N) (toCLM M)

private theorem norm_conjTranspose_le (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ ≤ ‖M‖ := by
  have h : ‖M.conjTranspose‖ ≤ (‖M‖₊ : ℝ) := by
    refine norm_le_of_forall_inner_le fun v w => ?_
    rw [toCLM_conjTranspose, inner_toCLM_conjTranspose_right]
    calc ‖Inner.inner A (toCLM M w) v‖
        ≤ ‖toCLM M w‖ * ‖v‖ := CStarModule.norm_inner_le _
      _ ≤ (‖toCLM M‖ * ‖w‖) * ‖v‖ := by gcongr; exact (toCLM M).le_opNorm w
      _ = (‖M‖₊ : ℝ) * ‖v‖ * ‖w‖ := by rw [coe_nnNorm, norm_def]; ring
  simpa only [coe_nnNorm] using h

/-- Taking the conjugate transpose of a rectangular C⋆-matrix preserves the operator norm. -/
@[simp]
theorem norm_conjTranspose (M : CStarMatrix m n A) : ‖M.conjTranspose‖ = ‖M‖ :=
  le_antisymm (norm_conjTranspose_le M) <| by
    simpa only [conjTranspose_conjTranspose] using norm_conjTranspose_le M.conjTranspose

private theorem norm_sq_le_norm_mul_conjTranspose (M : CStarMatrix m n A) :
    ‖M‖ ^ 2 ≤ ‖M * M.conjTranspose‖ := by
  rw [norm_def]
  have h : ‖toCLM M‖ ≤ √‖M * M.conjTranspose‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hsq : ‖toCLM M v‖ ^ 2 ≤ ‖M * M.conjTranspose‖ * ‖v‖ ^ 2 := by
      rw [CStarModule.norm_sq_eq A, ← inner_toCLM_conjTranspose_right, ← toCLM_conjTranspose]
      calc ‖Inner.inner A v (toCLM M.conjTranspose (toCLM M v))‖
          ≤ ‖v‖ * ‖toCLM M.conjTranspose (toCLM M v)‖ := CStarModule.norm_inner_le _
        _ = ‖v‖ * ‖toCLM (M * M.conjTranspose) v‖ := by
            rw [toCLM_mul, ContinuousLinearMap.comp_apply]
        _ ≤ ‖v‖ * (‖toCLM (M * M.conjTranspose)‖ * ‖v‖) := by
            gcongr
            exact (toCLM (M * M.conjTranspose)).le_opNorm v
        _ = ‖M * M.conjTranspose‖ * ‖v‖ ^ 2 := by rw [norm_def]; ring
    calc ‖toCLM M v‖ = √(‖toCLM M v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √(‖M * M.conjTranspose‖ * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = √‖M * M.conjTranspose‖ * ‖v‖ := by
          rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact (pow_le_pow_left₀ (toCLM M).opNorm_nonneg h 2).trans_eq (Real.sq_sqrt (norm_nonneg _))

/-- The rectangular C⋆-identity `‖M * Mᴴ‖ = ‖M‖ * ‖M‖`. -/
@[simp]
theorem norm_mul_conjTranspose_self (M : CStarMatrix m n A) :
    ‖M * M.conjTranspose‖ = ‖M‖ * ‖M‖ := by
  refine le_antisymm ?_ ?_
  · simpa only [norm_conjTranspose] using norm_mul_le M M.conjTranspose
  · simpa only [sq] using norm_sq_le_norm_mul_conjTranspose M

/-- The rectangular C⋆-identity `‖Mᴴ * M‖ = ‖M‖ * ‖M‖`. -/
@[simp]
theorem norm_conjTranspose_mul_self (M : CStarMatrix m n A) :
    ‖M.conjTranspose * M‖ = ‖M‖ * ‖M‖ := by
  simpa only [conjTranspose_conjTranspose, norm_conjTranspose] using
    norm_mul_conjTranspose_self M.conjTranspose

end RectangularNorm

section FromBlocks

variable {l m n o p q R A B : Type*}

/-- Form a block matrix in `CStarMatrix` from its four blocks. -/
def fromBlocks (M₁₁ : CStarMatrix m p A) (M₁₂ : CStarMatrix m q A)
    (M₂₁ : CStarMatrix n p A) (M₂₂ : CStarMatrix n q A) :
    CStarMatrix (m ⊕ n) (p ⊕ q) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
    (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂))

@[simp]
theorem ofMatrix_symm_fromBlocks (M₁₁ : CStarMatrix m p A) (M₁₂ : CStarMatrix m q A)
    (M₂₁ : CStarMatrix n p A) (M₂₂ : CStarMatrix n q A) :
    ofMatrix.symm (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
        (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂) := (rfl)

@[simp]
theorem fromBlocks_apply₁₁ (M₁₁ : CStarMatrix m p A) (M₁₂ : CStarMatrix m q A)
    (M₂₁ : CStarMatrix n p A) (M₂₂ : CStarMatrix n q A) (i : m) (j : p) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inl j) = M₁₁ i j := (rfl)

@[simp]
theorem fromBlocks_apply₁₂ (M₁₁ : CStarMatrix m p A) (M₁₂ : CStarMatrix m q A)
    (M₂₁ : CStarMatrix n p A) (M₂₂ : CStarMatrix n q A) (i : m) (j : q) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inr j) = M₁₂ i j := (rfl)

@[simp]
theorem fromBlocks_apply₂₁ (M₁₁ : CStarMatrix m p A) (M₁₂ : CStarMatrix m q A)
    (M₂₁ : CStarMatrix n p A) (M₂₂ : CStarMatrix n q A) (i : n) (j : p) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inl j) = M₂₁ i j := (rfl)

@[simp]
theorem fromBlocks_apply₂₂ (M₁₁ : CStarMatrix m p A) (M₁₂ : CStarMatrix m q A)
    (M₂₁ : CStarMatrix n p A) (M₂₂ : CStarMatrix n q A) (i : n) (j : q) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inr j) = M₂₂ i j := (rfl)

@[simp]
theorem fromBlocks_inj {M₁₁ N₁₁ : CStarMatrix m p A} {M₁₂ N₁₂ : CStarMatrix m q A}
    {M₂₁ N₂₁ : CStarMatrix n p A} {M₂₂ N₂₂ : CStarMatrix n q A} :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ ↔
      M₁₁ = N₁₁ ∧ M₁₂ = N₁₂ ∧ M₂₁ = N₂₁ ∧ M₂₂ = N₂₂ := by
  constructor
  · intro h
    refine ⟨ext fun i j => ?_, ext fun i j => ?_, ext fun i j => ?_, ext fun i j => ?_⟩
    · exact congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
    · exact congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
    · exact congrFun (congrFun h (Sum.inr i)) (Sum.inl j)
    · exact congrFun (congrFun h (Sum.inr i)) (Sum.inr j)
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

@[simp]
theorem fromBlocks_zero [Zero A] :
    fromBlocks (0 : CStarMatrix m p A) 0 0 (0 : CStarMatrix n q A) = 0 := by
  ext (i | i) (j | j) <;> rfl

@[simp]
theorem fromBlocks_one [DecidableEq m] [DecidableEq n] [Zero A] [One A] :
    fromBlocks (1 : CStarMatrix m m A) 0 0 (1 : CStarMatrix n n A) = 1 := by
  apply ofMatrix.symm.injective
  exact Matrix.fromBlocks_one

@[simp]
theorem fromBlocks_add [Add A] (M₁₁ N₁₁ : CStarMatrix m p A)
    (M₁₂ N₁₂ : CStarMatrix m q A) (M₂₁ N₂₁ : CStarMatrix n p A)
    (M₂₂ N₂₂ : CStarMatrix n q A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ + fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ + N₁₁) (M₁₂ + N₁₂) (M₂₁ + N₂₁) (M₂₂ + N₂₂) := by
  ext (i | i) (j | j) <;> rfl

@[simp]
theorem fromBlocks_sub [Sub A] (M₁₁ N₁₁ : CStarMatrix m p A)
    (M₁₂ N₁₂ : CStarMatrix m q A) (M₂₁ N₂₁ : CStarMatrix n p A)
    (M₂₂ N₂₂ : CStarMatrix n q A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ - fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ - N₁₁) (M₁₂ - N₁₂) (M₂₁ - N₂₁) (M₂₂ - N₂₂) := by
  ext (i | i) (j | j) <;> rfl

@[simp]
theorem fromBlocks_neg [Neg A] (M₁₁ : CStarMatrix m p A) (M₁₂ : CStarMatrix m q A)
    (M₂₁ : CStarMatrix n p A) (M₂₂ : CStarMatrix n q A) :
    -fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ =
      fromBlocks (-M₁₁) (-M₁₂) (-M₂₁) (-M₂₂) := by
  ext (i | i) (j | j) <;> rfl

@[simp]
theorem fromBlocks_smul [SMul R A] (r : R) (M₁₁ : CStarMatrix m p A)
    (M₁₂ : CStarMatrix m q A) (M₂₁ : CStarMatrix n p A) (M₂₂ : CStarMatrix n q A) :
    r • fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ =
      fromBlocks (r • M₁₁) (r • M₁₂) (r • M₂₁) (r • M₂₂) := by
  ext (i | i) (j | j) <;> rfl

@[simp]
theorem fromBlocks_conjTranspose [Star A] (M₁₁ : CStarMatrix m p A)
    (M₁₂ : CStarMatrix m q A) (M₂₁ : CStarMatrix n p A) (M₂₂ : CStarMatrix n q A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).conjTranspose =
      fromBlocks M₁₁.conjTranspose M₂₁.conjTranspose
        M₁₂.conjTranspose M₂₂.conjTranspose := by
  ext (i | i) (j | j) <;> rfl

@[simp]
theorem fromBlocks_star [Star A] (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix n m A) (M₂₂ : CStarMatrix n n A) :
    star (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (star M₁₁) M₂₁.conjTranspose M₁₂.conjTranspose (star M₂₂) :=
  fromBlocks_conjTranspose M₁₁ M₁₂ M₂₁ M₂₂

@[simp]
theorem fromBlocks_multiply [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring A]
    (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A)
    (N₁₁ : CStarMatrix l p A) (N₁₂ : CStarMatrix l q A)
    (N₂₁ : CStarMatrix m p A) (N₂₂ : CStarMatrix m q A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ * N₁₁ + M₁₂ * N₂₁) (M₁₁ * N₁₂ + M₁₂ * N₂₂)
        (M₂₁ * N₁₁ + M₂₂ * N₂₁) (M₂₁ * N₁₂ + M₂₂ * N₂₂) := by
  apply ofMatrix.symm.injective
  exact Matrix.fromBlocks_multiply (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
    (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂) (ofMatrix.symm N₁₁) (ofMatrix.symm N₁₂)
    (ofMatrix.symm N₂₁) (ofMatrix.symm N₂₂)

@[simp]
theorem fromBlocks_map (f : A → B) (M₁₁ : CStarMatrix m p A) (M₁₂ : CStarMatrix m q A)
    (M₂₁ : CStarMatrix n p A) (M₂₂ : CStarMatrix n q A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).map f =
      fromBlocks (M₁₁.map f) (M₁₂.map f) (M₂₁.map f) (M₂₂.map f) := by
  ext (i | i) (j | j) <;> rfl

/-- A block-diagonal matrix is a star projection iff both diagonal blocks are star projections. -/
@[simp]
theorem isStarProjection_fromBlocks_diag [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {P : CStarMatrix m m A} {Q : CStarMatrix n n A} :
    IsStarProjection (fromBlocks P 0 0 Q) ↔ IsStarProjection P ∧ IsStarProjection Q := by
  simp only [isStarProjection_iff', fromBlocks_multiply, fromBlocks_star, conjTranspose_zero,
    CStarMatrix.mul_zero, CStarMatrix.zero_mul, add_zero, zero_add, fromBlocks_inj, true_and]
  tauto

/-- A block-diagonal square matrix is unitary iff both diagonal blocks are unitary. -/
@[simp]
theorem fromBlocks_diag_mem_unitary [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Semiring A] [StarRing A] {U : CStarMatrix m m A} {V : CStarMatrix n n A} :
    fromBlocks U 0 0 V ∈ unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) ↔
      U ∈ unitary (CStarMatrix m m A) ∧ V ∈ unitary (CStarMatrix n n A) := by
  simp only [Unitary.mem_iff, fromBlocks_star, conjTranspose_zero, fromBlocks_multiply,
    CStarMatrix.mul_zero, CStarMatrix.zero_mul, add_zero, zero_add, ← fromBlocks_one,
    fromBlocks_inj, true_and]
  tauto

end FromBlocks

section Corners

variable {m n R A : Type*} [Fintype m] [Fintype n]

/-- The block-diagonal embedding `CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[R]
CStarMatrix (m ⊕ n) (m ⊕ n) A` sending `(M, N)` to `fromBlocks M 0 0 N`. -/
def blockDiagHom (R : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [StarAddMonoid A] :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun x := fromBlocks x.1 0 0 x.2
  map_smul' r x := by simp [fromBlocks_smul]
  map_zero' := by simp
  map_add' x y := by simp
  map_mul' x y := by simp
  map_star' x := by simp

@[simp]
theorem blockDiagHom_apply [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [StarAddMonoid A] (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    blockDiagHom R (M, N) = fromBlocks M 0 0 N := (rfl)

theorem blockDiagHom_injective [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [StarAddMonoid A] :
    Function.Injective (blockDiagHom (m := m) (n := n) (A := A) R) := by
  rintro ⟨M₁, N₁⟩ ⟨M₂, N₂⟩ h
  simp only [blockDiagHom_apply, fromBlocks_inj, true_and] at h
  exact Prod.ext h.1 h.2

/-- The upper-left corner inclusion `M ↦ fromBlocks M 0 0 0`. -/
def cornerInl (R : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [StarAddMonoid A] :
    CStarMatrix m m A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun M := fromBlocks M 0 0 0
  map_smul' r M := by simp [fromBlocks_smul]
  map_zero' := by simp
  map_add' M N := by simp
  map_mul' M N := by simp
  map_star' M := by simp

/-- The lower-right corner inclusion `N ↦ fromBlocks 0 0 0 N`. -/
def cornerInr (R : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [StarAddMonoid A] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun N := fromBlocks 0 0 0 N
  map_smul' r N := by simp [fromBlocks_smul]
  map_zero' := by simp
  map_add' M N := by simp
  map_mul' M N := by simp
  map_star' N := by simp

@[simp]
theorem cornerInl_apply [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [StarAddMonoid A] (M : CStarMatrix m m A) :
    cornerInl (n := n) R M = fromBlocks M 0 0 0 := (rfl)

@[simp]
theorem cornerInr_apply [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [StarAddMonoid A] (N : CStarMatrix n n A) :
    cornerInr (m := m) R N = fromBlocks 0 0 0 N := (rfl)

theorem cornerInl_injective [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [StarAddMonoid A] :
    Function.Injective (cornerInl (m := m) (n := n) (A := A) R) := by
  intro M₁ M₂ h
  simpa using h

theorem cornerInr_injective [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [StarAddMonoid A] :
    Function.Injective (cornerInr (m := m) (n := n) (A := A) R) := by
  intro N₁ N₂ h
  simpa using h

theorem cornerInl_mul_cornerInr [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [StarAddMonoid A] (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    cornerInl (n := n) R M * cornerInr (m := m) R N = 0 := by
  simp

theorem cornerInr_mul_cornerInl [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [StarAddMonoid A] (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    cornerInr (m := m) R N * cornerInl (n := n) R M = 0 := by
  simp

theorem cornerInl_add_cornerInr [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [StarAddMonoid A] (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    cornerInl (n := n) R M + cornerInr (m := m) R N = fromBlocks M 0 0 N := by
  simp

/-- The operator norm of a block-diagonal C⋆-matrix is the maximum of the norms of its diagonal
blocks. -/
@[simp]
theorem norm_fromBlocks_diag [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    ‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖ := by
  simpa [Prod.norm_def] using
    NonUnitalStarAlgHom.norm_map (blockDiagHom (m := m) (n := n) (A := A) ℂ)
      blockDiagHom_injective (M, N)

/-- The upper-left corner inclusion is isometric. -/
theorem norm_cornerInl [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (M : CStarMatrix m m A) : ‖cornerInl (n := n) ℂ M‖ = ‖M‖ := by
  simp [norm_nonneg]

/-- The lower-right corner inclusion is isometric. -/
theorem norm_cornerInr [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (N : CStarMatrix n n A) : ‖cornerInr (m := m) ℂ N‖ = ‖N‖ := by
  simp [norm_nonneg]

end Corners

section Reindex

variable {l m n k R A : Type*}

/-- Block-diagonal sums are associative under `reindexₐ (Equiv.sumAssoc m n k)`. -/
theorem reindexₐ_sumAssoc_fromBlocks [Fintype m] [Fintype n] [Fintype k]
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    (M : CStarMatrix m m A) (N : CStarMatrix n n A) (P : CStarMatrix k k A) :
    reindexₐ R A (Equiv.sumAssoc m n k) (fromBlocks (fromBlocks M 0 0 N) 0 0 P) =
      fromBlocks M 0 0 (fromBlocks N 0 0 P) := by
  ext (i | (i | i)) (j | (j | j)) <;> rfl

/-- Block-diagonal sums are commutative under `reindexₐ (Equiv.sumComm m n)`. -/
theorem reindexₐ_sumComm_fromBlocks [Fintype m] [Fintype n]
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    reindexₐ R A (Equiv.sumComm m n) (fromBlocks M 0 0 N) = fromBlocks N 0 0 M := by
  ext (i | i) (j | j) <;> rfl

/-- Rectangular reindexing preserves the C⋆-matrix operator norm. -/
@[simp]
theorem norm_reindexₗ [Fintype m] [Fintype n] [Fintype l] [Fintype k]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (eₘ : m ≃ l) (eₙ : n ≃ k) (M : CStarMatrix m n A) :
    ‖reindexₗ ℂ A eₘ eₙ M‖ = ‖M‖ := by
  have hsq :
      ‖reindexₗ ℂ A eₘ eₙ M‖ * ‖reindexₗ ℂ A eₘ eₙ M‖ = ‖M‖ * ‖M‖ := by
    rw [← norm_mul_conjTranspose_self, ← norm_mul_conjTranspose_self]
    have hmul : reindexₗ ℂ A eₘ eₙ M * (reindexₗ ℂ A eₘ eₙ M).conjTranspose =
        reindexₐ ℂ A eₘ (M * M.conjTranspose) := by
      ext i j
      simp only [mul_apply, conjTranspose_apply, reindexₗ_apply, reindexₐ_apply]
      exact Fintype.sum_equiv eₙ.symm _ _ fun _ => rfl
    rw [hmul, StarAlgEquiv.norm_map]
  nlinarith [norm_nonneg (reindexₗ ℂ A eₘ eₙ M), norm_nonneg M]

/-- The permutation matrix in `CStarMatrix n m A` associated to an equivalence `e : m ≃ n`,
with `(e j, j)` entry equal to `1` and all other entries `0`. -/
def reindexMatrix (A : Type*) [Zero A] [One A] [DecidableEq n] (e : m ≃ n) :
    CStarMatrix n m A :=
  ofMatrix fun i j => if i = e j then 1 else 0

@[simp]
theorem reindexMatrix_apply [Zero A] [One A] [DecidableEq n] (e : m ≃ n) (i : n) (j : m) :
    reindexMatrix A e i j = if i = e j then 1 else 0 := (rfl)

@[simp]
theorem conjTranspose_reindexMatrix [DecidableEq m] [DecidableEq n]
    [Semiring A] [StarRing A] (e : m ≃ n) :
    (reindexMatrix A e).conjTranspose = reindexMatrix A e.symm := by
  ext i j
  simp only [conjTranspose_apply, reindexMatrix_apply]
  by_cases h : i = e.symm j
  · subst h
    simp
  · have h' : j ≠ e i := fun hj => h (by simp [hj])
    simp [h, h']

@[simp]
theorem reindexMatrix_mul_conjTranspose [Fintype m] [DecidableEq n]
    [Semiring A] [StarRing A] (e : m ≃ n) :
    reindexMatrix A e * (reindexMatrix A e).conjTranspose = 1 := by
  classical
  ext i j
  simp only [mul_apply, conjTranspose_reindexMatrix, reindexMatrix_apply, one_apply]
  rw [Finset.sum_eq_single (e.symm i)]
  · by_cases h : i = j <;> simp [h]
  · intro k _ hk
    have hik : i ≠ e k := fun h => hk (by simp [h])
    simp [hik]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem conjTranspose_mul_reindexMatrix [Fintype n] [DecidableEq m] [DecidableEq n]
    [Semiring A] [StarRing A] (e : m ≃ n) :
    (reindexMatrix A e).conjTranspose * reindexMatrix A e = 1 := by
  simpa only [conjTranspose_reindexMatrix, conjTranspose_conjTranspose, Equiv.symm_symm] using
    reindexMatrix_mul_conjTranspose (A := A) e.symm

/-- Conjugation by `reindexMatrix A e` equals `reindexₐ R A e`. -/
theorem reindexMatrix_mul_mul_conjTranspose [Fintype m] [Fintype n] [DecidableEq n]
    [Semiring R] [Semiring A] [Module R A] [StarRing A]
    (e : m ≃ n) (M : CStarMatrix m m A) :
    reindexMatrix A e * M * (reindexMatrix A e).conjTranspose = reindexₐ R A e M := by
  classical
  ext i j
  simp only [mul_apply, conjTranspose_reindexMatrix, reindexMatrix_apply, reindexₐ_apply]
  rw [Finset.sum_eq_single (e.symm j)]
  · simp only [ite_true, mul_one]
    rw [Finset.sum_eq_single (e.symm i)]
    · simp only [Equiv.apply_symm_apply, ite_true, one_mul]
      rfl
    · intro k _ hk
      have hik : i ≠ e k := fun h => hk (by simp [h])
      simp [hik]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A permutation of a finite index set yields a permutation unitary in `CStarMatrix n n A`. -/
def permUnitary (A : Type*) [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
    (e : Equiv.Perm n) : unitary (CStarMatrix n n A) :=
  ⟨reindexMatrix A e, conjTranspose_mul_reindexMatrix e, reindexMatrix_mul_conjTranspose e⟩

@[simp]
theorem coe_permUnitary [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
    (e : Equiv.Perm n) :
    (permUnitary A e : CStarMatrix n n A) = reindexMatrix A e := (rfl)

/-- Conjugation by `permUnitary A e` implements `reindexₐ R A e`. -/
theorem permUnitary_mul_mul_star [Fintype n] [DecidableEq n]
    [Semiring R] [Semiring A] [Module R A] [StarRing A]
    (e : Equiv.Perm n) (M : CStarMatrix n n A) :
    (permUnitary A e : CStarMatrix n n A) * M * star (permUnitary A e : CStarMatrix n n A) =
      reindexₐ R A e M :=
  reindexMatrix_mul_mul_conjTranspose (R := R) e M

end Reindex

end CStarMatrix
