/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Star.Basic
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Rectangular algebra, operator norms, and quadratic-form positivity on `CStarMatrix`

For a non-unital C⋆-algebra `A` and finite types `m`, `n`, Mathlib defines `CStarMatrix m n A`
with the Hilbert C⋆-module operator norm and makes `CStarMatrix n n A` a C⋆-algebra ordered by the
spectral order.

This file develops the core rectangular algebra, entrywise amplification, finite row-and-column
reindexing, rectangular C⋆-norm identities, and quadratic-form positivity criterion on
`CStarMatrix`:

* Rectangular `ofMatrix` / `conjTranspose` / multiplication lemmas, together with automatic
  partial-isometry identities when `vᴴ * v` is idempotent
  (`CStarMatrix.mul_conjTranspose_mul_self_of_isIdempotentElem`).
* Entrywise amplification (`CStarMatrix.mapₐ`, `CStarMatrix.norm_map_le`,
  `CStarMatrix.norm_map_of_injective`) and finite row-and-column reindexing isometries
  (`CStarMatrix.reindexₗᵢ`).
* Rectangular operator-norm C⋆-identities (`CStarMatrix.norm_conjTranspose`,
  `CStarMatrix.norm_self_mul_conjTranspose`, `CStarMatrix.norm_conjTranspose_mul_self`).
* Positivity in `CStarMatrix n n A` via finite quadratic forms:
  `0 ≤ M ↔ ∀ x : n → A, 0 ≤ ∑ i, ∑ j, star (x i) * M i j * x j`
  (`CStarMatrix.nonneg_iff_forall_sum_nonneg`), with no prior self-adjointness assumption by
  complex polarization (`CStarMatrix.isSelfAdjoint_of_forall_isSelfAdjoint_sum`).

## Main declarations

* `CStarMatrix.mapₐ`: entrywise amplification of a unital `⋆`-algebra homomorphism
  `A →⋆ₐ[R] B` to `CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B`.
* `CStarMatrix.reindexₗᵢ`: arbitrary finite row-and-column reindexing of `CStarMatrix` as a
  linear isometry equivalence.
* `CStarMatrix.instNonUnitalContinuousFunctionalCalculusReal`: the real continuous functional
  calculus of `CStarMatrix n n A`, which instance search does not find on its own.
* `CStarMatrix.ofMatrix_symm_mul`, `CStarMatrix.ofMatrix_symm_star`: reading a C⋆-matrix as an
  ordinary matrix respects rectangular multiplication and sends `star` to the conjugate transpose.
* `CStarMatrix.sum_apply`, `CStarMatrix.toOneByOne_apply`: entries of finite sums and of
  `1 × 1` C⋆-matrices.
* `CStarMatrix.transposeₗ`: the transpose of C⋆-matrices, as a linear map.
* `CStarMatrix.map_zero_linearMap`, `CStarMatrix.map_add_linearMap`,
  `CStarMatrix.map_smul_linearMap`: applying `0`, `f + g`, or `c • f` to every entry.
* `CStarMatrix.mul_conjTranspose_mul_self_of_isIdempotentElem`: over a star-ordered ring with
  proper star, any rectangular matrix `v` with idempotent `vᴴ * v` satisfies `v * vᴴ * v = v`.
* `CStarMatrix.norm_conjTranspose`, `CStarMatrix.norm_self_mul_conjTranspose`,
  `CStarMatrix.norm_conjTranspose_mul_self`: `‖Mᴴ‖ = ‖M‖`, `‖M * Mᴴ‖ = ‖M‖ ^ 2`, and
  `‖Mᴴ * M‖ = ‖M‖ ^ 2`.
* `CStarMatrix.isSelfAdjoint_of_forall_isSelfAdjoint_sum`: a matrix all of whose quadratic forms
  are self-adjoint is self-adjoint.
* `CStarMatrix.nonneg_iff_forall_sum_nonneg`: the quadratic-form criterion for positivity.
* `CStarMatrix.diag_nonneg_of_nonneg`: the diagonal entries of a positive matrix are positive.
* `CStarMatrix.submatrix_nonneg` and `CStarMatrix.extend_nonneg`: reindexing a positive matrix
  along any map of indices, or extending it by zero along an injective one, gives a positive
  matrix.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Lemma 4.1.
* M. Rørdam, F. Larsen, N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, LMS Student
  Texts 49, Cambridge University Press (2000), Chapter 2.
-/

public section

open Matrix
open scoped InnerProductSpace WithCStarModule

namespace CStarMatrix

section Algebraic

variable {k l m n o p R A B C : Type*}

/-- Scalars commute past matrix multiplication on the left, as for `Matrix`. -/
instance instIsScalarTowerSelf [Fintype n] [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] [IsScalarTower R A A] :
    IsScalarTower R (CStarMatrix n n A) (CStarMatrix n n A) :=
  ⟨fun r M N => smul_mul r M N⟩

/-- Scalars commute past matrix multiplication on the right, as for `Matrix`. -/
instance instSMulCommClassSelf [Fintype n] [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] [SMulCommClass R A A] :
    SMulCommClass R (CStarMatrix n n A) (CStarMatrix n n A) :=
  ⟨fun r M N => (mul_smul M r N).symm⟩

@[simp]
theorem ofMatrix_symm_zero [Zero A] :
    ofMatrix.symm (0 : CStarMatrix m n A) = (0 : Matrix m n A) := (rfl)

@[simp]
theorem ofMatrix_one [DecidableEq n] [Zero A] [One A] :
    ofMatrix (1 : Matrix n n A) = (1 : CStarMatrix n n A) := (rfl)

@[simp]
theorem ofMatrix_symm_one [DecidableEq n] [Zero A] [One A] :
    ofMatrix.symm (1 : CStarMatrix n n A) = (1 : Matrix n n A) := (rfl)

@[simp]
theorem ofMatrix_symm_add [Add A] (M N : CStarMatrix m n A) :
    ofMatrix.symm (M + N) = ofMatrix.symm M + ofMatrix.symm N := (rfl)

@[simp]
theorem ofMatrix_symm_neg [Neg A] (M : CStarMatrix m n A) :
    ofMatrix.symm (-M) = -ofMatrix.symm M := (rfl)

@[simp]
theorem ofMatrix_symm_sub [Sub A] (M N : CStarMatrix m n A) :
    ofMatrix.symm (M - N) = ofMatrix.symm M - ofMatrix.symm N := (rfl)

@[simp]
theorem ofMatrix_symm_smul [SMul R A] (r : R) (M : CStarMatrix m n A) :
    ofMatrix.symm (r • M) = r • ofMatrix.symm M := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix respects rectangular multiplication. -/
@[simp]
lemma ofMatrix_symm_mul [Fintype m] [Mul A] [AddCommMonoid A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    ofMatrix.symm (M * N) = ofMatrix.symm M * ofMatrix.symm N := (rfl)

@[simp]
theorem ofMatrix_mul [Fintype m] [Mul A] [AddCommMonoid A]
    (M : Matrix l m A) (N : Matrix m n A) :
    ofMatrix (M * N) = ofMatrix M * ofMatrix N := (rfl)

@[simp]
theorem ofMatrix_symm_conjTranspose [Star A] (M : CStarMatrix m n A) :
    ofMatrix.symm M.conjTranspose = (ofMatrix.symm M)ᴴ := (rfl)

@[simp]
theorem ofMatrix_conjTranspose [Star A] (M : Matrix m n A) :
    ofMatrix Mᴴ = (ofMatrix M).conjTranspose := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix sends `star` to the conjugate transpose. -/
@[simp]
lemma ofMatrix_symm_star [Star A] (M : CStarMatrix n n A) :
    ofMatrix.symm (star M) = (ofMatrix.symm M)ᴴ := (rfl)

@[simp]
theorem ofMatrix_symm_map (M : CStarMatrix m n A) (f : A → B) :
    ofMatrix.symm (M.map f) = (ofMatrix.symm M).map f := (rfl)

@[simp]
theorem ofMatrix_symm_reindexₗ [Semiring R] [AddCommMonoid A] [Module R A]
    (eₘ : m ≃ o) (eₙ : n ≃ p) (M : CStarMatrix m n A) :
    ofMatrix.symm (reindexₗ R A eₘ eₙ M) = Matrix.reindex eₘ eₙ (ofMatrix.symm M) := (rfl)

/-- `CStarMatrix.ofMatrixₗ` is `CStarMatrix.ofMatrix`. -/
@[simp]
lemma ofMatrixₗ_apply [AddCommMonoid A] [Semiring R] [Module R A]
    (M : Matrix m n A) : ofMatrixₗ (R := R) M = ofMatrix M := (rfl)

/-- The inverse of `CStarMatrix.ofMatrixₗ` is the inverse of `CStarMatrix.ofMatrix`. -/
@[simp]
lemma ofMatrixₗ_symm_apply [AddCommMonoid A] [Semiring R] [Module R A]
    (M : CStarMatrix m n A) : (ofMatrixₗ (R := R)).symm M = ofMatrix.symm M := (rfl)

/-- Entries of a finite sum of C⋆-matrices are the sums of the entries. -/
theorem sum_apply [AddCommMonoid A] {ι : Type*} (s : Finset ι)
    (f : ι → CStarMatrix m n A) (i : m) (j : n) : (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j :=
  Matrix.sum_apply i j s f

/-- The entry of the `1 × 1` C⋆-matrix associated to `a`. -/
@[simp]
theorem toOneByOne_apply [Unique n] [Semiring R] [AddCommMonoid A] [Mul A] [Star A] [Module R A]
    (a : A) (i j : n) : toOneByOne n R A a i j = a :=
  rfl

variable (R) in
/-- The transpose of C⋆-matrices, as a linear map. -/
def transposeₗ [Semiring R] [AddCommMonoid A] [Module R A] :
    CStarMatrix m n A →ₗ[R] CStarMatrix n m A where
  toFun M := M.transpose
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem transposeₗ_apply [Semiring R] [AddCommMonoid A] [Module R A]
    (M : CStarMatrix m n A) : transposeₗ R M = M.transpose :=
  (rfl)

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
  have hv' : IsIdempotentElem ((ofMatrix.symm v)ᴴ * ofMatrix.symm v) := by
    rw [IsIdempotentElem, ← ofMatrix_symm_conjTranspose, ← ofMatrix_symm_mul,
      ← ofMatrix_symm_mul, hv.eq]
  exact ofMatrix.symm.injective <| by
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
      Matrix.mul_conjTranspose_mul_self_of_isIdempotentElem hv'

/-- A matrix over a complex star-algebra with proper star all of whose quadratic forms are
self-adjoint is self-adjoint. -/
theorem isSelfAdjoint_of_forall_isSelfAdjoint_sum [Fintype n] [NonUnitalRing A] [StarRing A]
    [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] [IsProperStar A]
    {M : CStarMatrix n n A}
    (hM : ∀ x : n → A, IsSelfAdjoint (∑ i, ∑ j, star (x i) * M i j * x j)) :
    IsSelfAdjoint M := by
  classical
  replace hM (x : n → A) : IsSelfAdjoint (star x ⬝ᵥ (ofMatrix.symm M *ᵥ x)) := by
    rw [dot_mulVec_eq_sum_sum, Finset.sum_comm]
    exact hM x
  -- Polarization: the sesquilinear form `P x y` satisfies `star (P x y) = P y x`.
  have hP (x y : n → A) :
      star (star x ⬝ᵥ (ofMatrix.symm M *ᵥ y)) = star y ⬝ᵥ (ofMatrix.symm M *ᵥ x) := by
    have h₁ := (hM (x + y)).star_eq
    have h₂ := (hM (x + Complex.I • y)).star_eq
    simp only [star_add, star_smul, star_neg, Complex.star_def, Complex.conj_I, mulVec_add,
      mulVec_smul, add_dotProduct, dotProduct_add, neg_dotProduct, smul_dotProduct,
      dotProduct_smul, neg_smul, (hM x).star_eq, (hM y).star_eq] at h₁ h₂
    linear_combination (norm := match_scalars) (1 / 2 : ℂ) • h₁ + (Complex.I / 2) • h₂ <;>
      simp [Complex.ext_iff] <;> norm_num
  refine ext fun i j => ?_
  apply sub_eq_zero.mp
  refine TauCeti.eq_zero_of_forall_star_mul_mul_eq_zero fun c d => ?_
  have := hP (Pi.single j c) (Pi.single i d)
  simp only [← Pi.single_star, single_dotProduct, mulVec_single, Pi.smul_apply, col_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, star_mul, star_star,
    ofMatrix_symm_apply] at this
  rw [star_apply, mul_sub, sub_mul, this, mul_assoc, sub_self]

end Algebraic

section AmplificationAndReindex

variable {l m n o p q R A B C : Type*}

/-- Applying the zero linear map to every entry gives the zero matrix. -/
@[simp]
theorem map_zero_linearMap [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (M : CStarMatrix m n A) : M.map ⇑(0 : A →ₗ[R] B) = 0 := by
  ext
  simp [zero_apply]

/-- Applying a sum of linear maps to every entry gives the sum of the entrywise images. -/
theorem map_add_linearMap [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (M : CStarMatrix m n A) (f g : A →ₗ[R] B) :
    M.map ⇑(f + g) = M.map f + M.map g := by
  ext
  simp [add_apply]

/-- Applying a scalar multiple of a linear map to every entry gives the scalar multiple of the
entrywise image. -/
theorem map_smul_linearMap [CommSemiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (M : CStarMatrix m n A) (c : R) (f : A →ₗ[R] B) :
    M.map ⇑(c • f) = c • M.map f := by
  ext
  simp [smul_apply]

theorem map_conjTranspose [Star A] [Star B] (M : CStarMatrix m n A) (f : A → B)
    (hf : ∀ a, f (star a) = star (f a)) :
    M.conjTranspose.map f = (M.map f).conjTranspose := by
  ext
  simp [hf]

@[simp]
theorem conjTranspose_map [Star A] [Star B] {F : Type*} [FunLike F A B] [StarHomClass F A B]
    (M : CStarMatrix m n A) (f : F) :
    (M.map f).conjTranspose = M.conjTranspose.map f :=
  (map_conjTranspose M f (map_star f)).symm

@[simp]
protected theorem star_map [Star A] [Star B] {F : Type*} [FunLike F A B] [StarHomClass F A B]
    (M : CStarMatrix n n A) (f : F) :
    star (M.map f) = (star M).map f :=
  conjTranspose_map M f

@[simp]
protected theorem map_mul [Fintype m] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B]
    (f : F) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).map f = M.map f * N.map f := by
  ext i k
  simp [mul_apply, map_sum, map_mul]

@[simp]
theorem mapₙₐ_id [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A] :
    mapₙₐ (NonUnitalStarAlgHom.id R A) = NonUnitalStarAlgHom.id R (CStarMatrix n n A) := by
  ext M i j
  simp

theorem mapₙₐ_comp [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    [NonUnitalNonAssocSemiring C] [Module R C] [Star C]
    (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) :
    mapₙₐ (g.comp f) = (mapₙₐ (n := n) g).comp (mapₙₐ f) := by
  ext M i j
  simp

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

theorem reindexₗ_apply' [Semiring R] [AddCommMonoid A] [Module R A]
    (eₘ : m ≃ o) (eₙ : n ≃ p) (M : CStarMatrix m n A) (i : o) (j : p) :
    reindexₗ R A eₘ eₙ M i j = M (eₘ.symm i) (eₙ.symm j) := (rfl)

@[simp]
theorem reindexₗ_refl [Semiring R] [AddCommMonoid A] [Module R A] :
    reindexₗ R A (Equiv.refl m) (Equiv.refl n) = LinearEquiv.refl R (CStarMatrix m n A) := by
  ext M i j
  rw [reindexₗ_apply']
  simp

@[simp]
theorem reindexₗ_conjTranspose [Semiring R] [AddCommMonoid A] [Module R A] [Star A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    (reindexₗ R A eₘ eₙ M).conjTranspose = reindexₗ R A eₙ eₘ M.conjTranspose := by
  ext i j
  simp only [conjTranspose_apply, reindexₗ_apply']

theorem reindexₗ_mul [Fintype m] [Fintype o] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A]
    (eₗ : l ≃ p) (eₘ : m ≃ o) (eₙ : n ≃ q)
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    reindexₗ R A eₗ eₙ (M * N) = reindexₗ R A eₗ eₘ M * reindexₗ R A eₘ eₙ N := by
  ext i k
  simp only [reindexₗ_apply', mul_apply]
  exact Fintype.sum_equiv eₘ _ _ fun _ => by simp

theorem reindexₐ_eq_reindexₗ [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] [Star A] (e : m ≃ n) (M : CStarMatrix m m A) :
    reindexₐ R A e M = reindexₗ R A e e M := (rfl)

@[simp]
theorem reindexₐ_refl [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A] :
    reindexₐ R A (Equiv.refl n) = StarAlgEquiv.refl R (CStarMatrix n n A) := by
  ext M i j
  rw [reindexₐ_eq_reindexₗ, reindexₗ_apply']
  simp

theorem reindexₐ_trans [Fintype l] [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] [Star A] (e₁ : l ≃ m) (e₂ : m ≃ n) :
    reindexₐ R A (e₁.trans e₂) = (reindexₐ R A e₁).trans (reindexₐ R A e₂) := by
  ext M i j
  simp only [StarAlgEquiv.trans_apply, reindexₐ_eq_reindexₗ, reindexₗ_apply',
    Equiv.symm_trans_apply]

end AmplificationAndReindex

section RectangularNorm

variable {l m n o A B : Type*}
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
    have hadj : ⟪toCLM M v, toCLM M v⟫_A = ⟪v, toCLM M.conjTranspose (toCLM M v)⟫_A := by
      rw [← inner_toCLM_conjTranspose_right]
      congr 1
    rw [hadj, ← ContinuousLinearMap.comp_apply, ← toCLM_mul]
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

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
private theorem conjTranspose_map_mul_map [Fintype m] [Fintype n]
    {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (f : F) (M : CStarMatrix m n A) :
    (M.map f).conjTranspose * M.map f =
      mapₙₐ (.ofClass f : A →⋆ₙₐ[ℂ] B) (M.conjTranspose * M) := by
  simp

/-- Entrywise application of a `⋆`-homomorphism to a rectangular `CStarMatrix` is
norm-contractive. -/
theorem norm_map_le [Fintype m] [Fintype n]
    {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (f : F) (M : CStarMatrix m n A) :
    ‖M.map f‖ ≤ ‖M‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_conjTranspose_mul_self,
    ← norm_conjTranspose_mul_self M, conjTranspose_map_mul_map]
  exact NonUnitalStarAlgHom.norm_apply_le (mapₙₐ (.ofClass f : A →⋆ₙₐ[ℂ] B)) (M.conjTranspose * M)

/-- Entrywise application of an injective `⋆`-homomorphism to a rectangular `CStarMatrix` is
isometric. -/
theorem norm_map_of_injective [Fintype m] [Fintype n]
    {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    {f : F} (hf : Function.Injective f) (M : CStarMatrix m n A) :
    ‖M.map f‖ = ‖M‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_conjTranspose_mul_self,
    ← norm_conjTranspose_mul_self M, conjTranspose_map_mul_map]
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
    ← norm_conjTranspose_mul_self M, reindexₗ_conjTranspose, ← reindexₗ_mul,
    ← reindexₐ_eq_reindexₗ, norm_reindexₐ]

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
    (reindexₗᵢ A eₘ eₙ).symm = reindexₗᵢ A eₘ.symm eₙ.symm :=
  LinearIsometryEquiv.ext fun M =>
    (reindexₗᵢ A eₘ eₙ).symm_apply_eq.mpr <| ext fun i j => by
      simp only [coe_reindexₗᵢ, reindexₗ_apply', Equiv.apply_symm_apply, Equiv.symm_symm]

end RectangularNorm

variable {n A : Type*} [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! The real continuous functional calculus of the C⋆-algebra `CStarMatrix n n A` is not found by
instance search, because the real scalar action on `CStarMatrix n n A` is the entrywise one rather
than the restriction of the complex action through which the general C⋆-algebra instances are
stated. The two actions agree definitionally, so we register the instances directly. -/

instance instNonUnitalContinuousFunctionalCalculusReal :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix n n A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

instance instNonnegSpectrumClassReal : NonnegSpectrumClass ℝ (CStarMatrix n n A) :=
  CStarAlgebra.instNonnegSpectrumClass'

/-- A matrix over a C⋆-algebra is positive exactly when all its finite quadratic forms are
positive. -/
theorem nonneg_iff_forall_sum_nonneg {M : CStarMatrix n n A} :
    0 ≤ M ↔ ∀ x : n → A, 0 ≤ ∑ i, ∑ j, star (x i) * M i j * x j := by
  -- For `R`, the quadratic form of `star R * R` at `x` is `star (R x) ⬝ᵥ R x`.
  have key (R : CStarMatrix n n A) (x : n → A) :
      star x ⬝ᵥ (ofMatrix.symm (star R * R) *ᵥ x) =
        star (ofMatrix.symm R *ᵥ x) ⬝ᵥ (ofMatrix.symm R *ᵥ x) := by
    rw [ofMatrix_symm_mul, ofMatrix_symm_star, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  have hform (x : n → A) :
      ∑ i, ∑ j, star (x i) * M i j * x j = star x ⬝ᵥ (ofMatrix.symm M *ᵥ x) := by
    rw [dot_mulVec_eq_sum_sum, Finset.sum_comm]
    rfl
  simp_rw [hform]
  refine ⟨fun hM x => ?_, fun hQ => ?_⟩
  · obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
    rw [key]
    exact dotProduct_star_self_nonneg _
  have hsa : IsSelfAdjoint M := isSelfAdjoint_of_forall_isSelfAdjoint_sum fun x => by
    rw [hform]
    exact .of_nonneg (hQ x)
  -- It remains to show that the negative part `N` of `M` vanishes.
  refine CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero.mpr ⟨hsa, ?_⟩
  set N := M⁻
  have hN : 0 ≤ N := CFC.negPart_nonneg M
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hN
  have hMN : M * N = -(star R * R * N) := by
    conv_lhs => rw [← CFC.posPart_sub_negPart M hsa]
    rw [sub_mul, CFC.posPart_mul_negPart, zero_sub, ← hR]
  -- Evaluating the quadratic form at `N y` shows `R N y = 0` for every `y`.
  have hRN : R * N = 0 := by
    classical
    have hv (y : n → A) : ofMatrix.symm (R * N) *ᵥ y = 0 := by
      have h := hQ (ofMatrix.symm N *ᵥ y)
      rw [mulVec_mulVec, ← ofMatrix_symm_mul, hMN, ofMatrix_symm_neg, neg_mulVec, dotProduct_neg,
        ofMatrix_symm_mul, ← mulVec_mulVec, key, Left.nonneg_neg_iff] at h
      rw [ofMatrix_symm_mul, ← mulVec_mulVec]
      exact dotProduct_star_self_eq_zero.mp (le_antisymm h (dotProduct_star_self_nonneg _))
    refine ext fun i j => ?_
    have h := congrFun (hv (Pi.single j (star ((R * N) i j)))) i
    simp only [mulVec_single, Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, ofMatrix_symm_apply, Pi.zero_apply, mul_star_self_eq_zero] at h
    rw [h, zero_apply]
  rw [← star_mul_self_eq_zero, hN.star_eq]
  calc N * N = star R * (R * N) := by rw [← mul_assoc, ← hR]
    _ = 0 := by rw [hRN, mul_zero]

/-- The diagonal entries of a positive matrix over a C⋆-algebra are positive. -/
theorem diag_nonneg_of_nonneg {M : CStarMatrix n n A} (hM : 0 ≤ M) (i : n) : 0 ≤ M i i := by
  obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
  rw [CStarMatrix.mul_apply]
  exact Finset.sum_nonneg fun k _ => by
    simp [CStarMatrix.star_apply]

/-- Reindexing a positive matrix along any map of indices gives a positive matrix. -/
theorem submatrix_nonneg {m : Type*} [Fintype m] (f : m → n) {M : CStarMatrix n n A}
    (hM : 0 ≤ M) : 0 ≤ ofMatrix ((ofMatrix.symm M).submatrix f f) := by
  obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
  refine nonneg_iff_forall_sum_nonneg.mpr fun x => ?_
  -- The quadratic form at `x` is `∑ k, star (y k) * y k` with `y k = ∑ i, R k (f i) * x i`.
  have h : ∑ i, ∑ j, star (x i) * ofMatrix ((ofMatrix.symm (star R * R)).submatrix f f) i j * x j =
      ∑ k, star (∑ i, R k (f i) * x i) * ∑ j, R k (f j) * x j := by
    simp only [ofMatrix_apply, ofMatrix_symm_apply, Matrix.submatrix_apply, mul_apply,
      star_apply, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    conv_lhs => enter [2, i]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [h]
  exact Finset.sum_nonneg fun k _ => star_mul_self_nonneg _

/-- Extending a positive matrix by zero along an injective map of indices gives a positive
matrix. -/
theorem extend_nonneg {m : Type*} [Fintype m] {f : m → n} (hf : Function.Injective f)
    {M : CStarMatrix m m A} (hM : 0 ≤ M) :
    0 ≤ ofMatrix (Matrix.of fun k l =>
      Function.extend f (fun i => Function.extend f (ofMatrix.symm M i) 0 l) 0 k) := by
  refine nonneg_iff_forall_sum_nonneg.mpr fun y => ?_
  convert nonneg_iff_forall_sum_nonneg.mp hM (y ∘ f) using 1
  symm
  refine Fintype.sum_of_injective f hf _ _ (fun k hk => ?_) fun i => ?_
  · refine Finset.sum_eq_zero fun l _ => ?_
    simp [Function.extend_apply' _ _ _ (by simpa using hk : ¬∃ a, f a = k)]
  refine Fintype.sum_of_injective f hf _ _ (fun l hl => ?_) fun j => ?_
  · simp [hf.extend_apply, Function.extend_apply' _ _ _ (by simpa using hl : ¬∃ a, f a = l)]
  simp [hf.extend_apply]

end CStarMatrix
