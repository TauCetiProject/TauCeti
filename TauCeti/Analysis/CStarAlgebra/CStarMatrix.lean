/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Algebra.Star.Basic
import TauCeti.Analysis.CStarAlgebra.Compression
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Positivity in matrix C⋆-algebras by quadratic forms

For a non-unital C⋆-algebra `A` and a finite type `n`, Mathlib makes `CStarMatrix n n A` a
C⋆-algebra and orders it by the spectral order. This file proves that a matrix `M` is positive in
this order exactly when its finite quadratic forms are positive in `A`:

`0 ≤ M ↔ ∀ x : n → A, 0 ≤ ∑ i, ∑ j, star (x i) * M i j * x j`.

No self-adjointness hypothesis is needed for the converse: positivity of all the quadratic forms
already forces `M` to be self-adjoint, by polarization over `ℂ`. The criterion is the standard way
to recognise positive matrices over a C⋆-algebra, for instance Gram matrices of vectors in a
Hilbert C⋆-module.

The file also collects basic algebraic API for `CStarMatrix` that Mathlib lacks: entries of finite
sums and of `1 × 1` matrices, entrywise images under sums and scalar multiples of linear maps,
and the transpose as a linear map. It also restates `Matrix`'s lemmas on rectangular products and
conjugate transposes for `CStarMatrix`: associativity, distributivity over subtraction, the
conjugate transpose of sums and products, entrywise maps of products and conjugate transposes,
and `conjTranspose_mul_self_eq_zero`. From these it shows that a rectangular matrix `v` with
`vᴴ * v` or `v * vᴴ` idempotent satisfies `v * vᴴ * v = v`. Finally, it defines the block sum
`M ⊕ N` of rectangular C⋆-matrices, with zero off-diagonal blocks.

## Main declarations

* `CStarMatrix.instNonUnitalContinuousFunctionalCalculusReal`: the real continuous functional
  calculus of `CStarMatrix n n A`, which instance search does not find on its own.
* `CStarMatrix.ofMatrix_symm_mul`, `CStarMatrix.ofMatrix_symm_star`: reading a C⋆-matrix as an
  ordinary matrix respects multiplication and sends `star` to the conjugate transpose.
* `CStarMatrix.of_mul_of`, `CStarMatrix.conjTranspose_of`: rectangular products and conjugate
  transposes of C⋆-matrices are those of the underlying matrices.
* `CStarMatrix.mul_assoc`, `CStarMatrix.conjTranspose_mul`, `CStarMatrix.map_mul`,
  `CStarMatrix.conjTranspose_map`, `CStarMatrix.conjTranspose_mul_self_eq_zero`: the rectangular
  product and conjugate-transpose calculus of `Matrix`, restated for `CStarMatrix`.
* `CStarMatrix.mul_conjTranspose_mul_self_of_isIdempotentElem_conjTranspose_mul_self` and
  `CStarMatrix.mul_conjTranspose_mul_self_of_isIdempotentElem_mul_conjTranspose_self`: a
  rectangular matrix whose initial or final matrix is idempotent is a partial isometry.
* `CStarMatrix.conjTranspose_mul_eq_zero_of_orthogonal` and
  `CStarMatrix.mul_conjTranspose_eq_zero_of_orthogonal`: partial isometries `v` and `w` with
  orthogonal final matrices have orthogonal ranges, `vᴴ * w = 0`, and those with orthogonal
  initial matrices satisfy `v * wᴴ = 0`.
* `CStarMatrix.blockSum`: the block sum `M ⊕ N` of rectangular C⋆-matrices, with
  `CStarMatrix.conjTranspose_blockSum`, `CStarMatrix.blockSum_mul_blockSum`,
  `CStarMatrix.blockSum_map` and `CStarMatrix.isStarProjection_blockSum`.
* `CStarMatrix.sum_apply`, `CStarMatrix.toOneByOne_apply`: entries of finite sums and of
  `1 × 1` C⋆-matrices.
* `CStarMatrix.transposeₗ`: the transpose of C⋆-matrices, as a linear map.
* `CStarMatrix.map_zero_linearMap`, `CStarMatrix.map_add_linearMap`,
  `CStarMatrix.map_smul_linearMap`: applying `0`, `f + g` or `c • f` to every entry.
* `CStarMatrix.isSelfAdjoint_of_forall_isSelfAdjoint_sum`: a matrix all of whose quadratic forms
  are self-adjoint is self-adjoint. This is purely algebraic, and holds over any complex
  star-algebra whose star is proper.
* `CStarMatrix.nonneg_iff_forall_sum_nonneg`: the quadratic-form criterion for positivity.
* `CStarMatrix.diag_nonneg_of_nonneg`: the diagonal entries of a positive matrix are positive.
* `CStarMatrix.submatrix_nonneg` and `CStarMatrix.extend_nonneg`: reindexing a positive matrix
  along any map of indices, or extending it by zero along an injective one, gives a positive
  matrix.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Lemma 4.1.
-/

public section

open Matrix

namespace CStarMatrix

section Algebraic

variable {n R A : Type*}

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

/-- Reading a C⋆-matrix as an ordinary matrix respects multiplication. -/
@[simp]
lemma ofMatrix_symm_mul [Fintype n] [Mul A] [AddCommMonoid A] (M N : CStarMatrix n n A) :
    ofMatrix.symm (M * N) = ofMatrix.symm M * ofMatrix.symm N := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix sends `star` to the conjugate transpose. -/
@[simp]
lemma ofMatrix_symm_star [Star A] (M : CStarMatrix n n A) :
    ofMatrix.symm (star M) = (ofMatrix.symm M)ᴴ := (rfl)

/-! ### Rectangular products and conjugate transposes -/

section Rectangular

variable {l m o B : Type*}

/-- Products of rectangular C⋆-matrices are the products of the underlying matrices. -/
@[simp]
theorem of_mul_of [Fintype m] [Mul A] [AddCommMonoid A] (M : Matrix l m A) (N : Matrix m n A) :
    ofMatrix M * ofMatrix N = ofMatrix (M * N) :=
  (rfl)

/-- The conjugate transpose of a C⋆-matrix is that of the underlying matrix. -/
@[simp]
theorem conjTranspose_of [Star A] (M : Matrix m n A) :
    (ofMatrix M).conjTranspose = ofMatrix Mᴴ :=
  (rfl)

/-- The conjugate transpose of C⋆-matrices is an involution. -/
@[simp]
theorem conjTranspose_conjTranspose [InvolutiveStar A] (M : CStarMatrix m n A) :
    M.conjTranspose.conjTranspose = M :=
  Matrix.conjTranspose_conjTranspose M

/-- The conjugate transpose of a sum of rectangular C⋆-matrices. -/
@[simp]
theorem conjTranspose_add [AddMonoid A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M + N).conjTranspose = M.conjTranspose + N.conjTranspose :=
  Matrix.conjTranspose_add M N

/-- The conjugate transpose of a difference of rectangular C⋆-matrices. -/
@[simp]
theorem conjTranspose_sub [AddGroup A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M - N).conjTranspose = M.conjTranspose - N.conjTranspose :=
  Matrix.conjTranspose_sub M N

/-- The conjugate transpose of a product of rectangular C⋆-matrices. -/
@[simp]
theorem conjTranspose_mul [Fintype m] [NonUnitalNonAssocSemiring A] [StarRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).conjTranspose = N.conjTranspose * M.conjTranspose :=
  Matrix.conjTranspose_mul M N

/-- Multiplication of rectangular C⋆-matrices is associative. -/
protected theorem mul_assoc [Fintype m] [Fintype n] [NonUnitalSemiring A]
    (L : CStarMatrix l m A) (M : CStarMatrix m n A) (N : CStarMatrix n o A) :
    L * M * N = L * (M * N) :=
  Matrix.mul_assoc L M N

/-- Left multiplication of rectangular C⋆-matrices distributes over subtraction. -/
protected theorem mul_sub [Fintype n] [NonUnitalNonAssocRing A]
    (L : CStarMatrix m n A) (M N : CStarMatrix n o A) :
    L * (M - N) = L * M - L * N :=
  Matrix.mul_sub L M N

/-- Right multiplication of rectangular C⋆-matrices distributes over subtraction. -/
protected theorem sub_mul [Fintype m] [NonUnitalNonAssocRing A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (L - M) * N = L * N - M * N :=
  Matrix.sub_mul L M N

/-- Applying a non-unital ring homomorphism to every entry respects products of rectangular
C⋆-matrices. -/
theorem map_mul [Fintype m] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B] (f : F)
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).map f = M.map f * N.map f :=
  Matrix.map_mul

/-- Applying a star-preserving map to every entry commutes with the conjugate transpose. -/
theorem conjTranspose_map [Star A] [Star B] {F : Type*} [FunLike F A B] [StarHomClass F A B]
    (f : F) (M : CStarMatrix m n A) :
    M.conjTranspose.map f = (M.map f).conjTranspose :=
  Matrix.conjTranspose_map f (map_star f)

/-- Over a star-ordered ring with proper star, a rectangular C⋆-matrix `M` vanishes as soon as
`Mᴴ * M` does. -/
@[simp]
theorem conjTranspose_mul_self_eq_zero [Fintype m] [PartialOrder A] [NonUnitalRing A]
    [StarRing A] [StarOrderedRing A] [IsProperStar A] {M : CStarMatrix m n A} :
    M.conjTranspose * M = 0 ↔ M = 0 :=
  Matrix.conjTranspose_mul_self_eq_zero

/-- Partial isometries with orthogonal final matrices have orthogonal ranges: if
`v * vᴴ * v = v`, `w * wᴴ * w = w` and `(v * vᴴ) * (w * wᴴ) = 0`, then `vᴴ * w = 0`. -/
theorem conjTranspose_mul_eq_zero_of_orthogonal [NonUnitalSemiring A] [StarRing A] [Fintype l]
    [Fintype m] [Fintype n] {v : CStarMatrix n m A} {w : CStarMatrix n l A}
    (hv : v * v.conjTranspose * v = v) (hw : w * w.conjTranspose * w = w)
    (h : v * v.conjTranspose * (w * w.conjTranspose) = 0) : v.conjTranspose * w = 0 := by
  have hv' : v.conjTranspose * v * v.conjTranspose = v.conjTranspose := by
    simpa [CStarMatrix.mul_assoc] using congrArg conjTranspose hv
  calc v.conjTranspose * w
      = v.conjTranspose * v * v.conjTranspose * (w * w.conjTranspose * w) := by rw [hv', hw]
    _ = v.conjTranspose * (v * v.conjTranspose * (w * w.conjTranspose)) * w := by
      simp only [CStarMatrix.mul_assoc]
    _ = 0 := by rw [h, CStarMatrix.mul_zero, CStarMatrix.zero_mul]

/-- The dual of `conjTranspose_mul_eq_zero_of_orthogonal`, for orthogonal initial matrices: if
`v * vᴴ * v = v`, `w * wᴴ * w = w` and `(vᴴ * v) * (wᴴ * w) = 0`, then `v * wᴴ = 0`. -/
theorem mul_conjTranspose_eq_zero_of_orthogonal [NonUnitalSemiring A] [StarRing A] [Fintype l]
    [Fintype m] [Fintype n] {v : CStarMatrix n m A} {w : CStarMatrix l m A}
    (hv : v * v.conjTranspose * v = v) (hw : w * w.conjTranspose * w = w)
    (h : v.conjTranspose * v * (w.conjTranspose * w) = 0) : v * w.conjTranspose = 0 := by
  have hw' : w.conjTranspose * w * w.conjTranspose = w.conjTranspose := by
    simpa [CStarMatrix.mul_assoc] using congrArg conjTranspose hw
  calc v * w.conjTranspose
      = v * v.conjTranspose * v * (w.conjTranspose * w * w.conjTranspose) := by rw [hv, hw']
    _ = v * (v.conjTranspose * v * (w.conjTranspose * w)) * w.conjTranspose := by
      simp only [CStarMatrix.mul_assoc]
    _ = 0 := by rw [h, CStarMatrix.mul_zero, CStarMatrix.zero_mul]

section Proper

variable [Fintype m] [Fintype n] [NonUnitalRing A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [IsProperStar A]

/-- If `vᴴ * v` is idempotent then `v * vᴴ * v = v`: a rectangular matrix whose initial matrix is
a projection is a partial isometry. -/
theorem mul_conjTranspose_mul_self_of_isIdempotentElem_conjTranspose_mul_self
    {v : CStarMatrix n m A} (hv : IsIdempotentElem (v.conjTranspose * v)) :
    v * v.conjTranspose * v = v := by
  rw [CStarMatrix.mul_assoc]
  -- With `x = v * (vᴴ * v) - v`, idempotence gives `vᴴ * x = 0`, hence `xᴴ * x = 0`.
  have h₁ : v.conjTranspose * (v * (v.conjTranspose * v) - v) = 0 := by
    rw [CStarMatrix.mul_sub, ← CStarMatrix.mul_assoc, hv.eq, sub_self]
  have h₂ : (v * (v.conjTranspose * v) - v).conjTranspose * v = 0 := by
    simpa using congrArg conjTranspose h₁
  rw [← sub_eq_zero, ← conjTranspose_mul_self_eq_zero, CStarMatrix.mul_sub,
    ← CStarMatrix.mul_assoc, h₂, CStarMatrix.zero_mul, sub_zero]

/-- If `v * vᴴ` is idempotent then `v * vᴴ * v = v`: a rectangular matrix whose final matrix is
a projection is a partial isometry. -/
theorem mul_conjTranspose_mul_self_of_isIdempotentElem_mul_conjTranspose_self
    {v : CStarMatrix n m A} (hv : IsIdempotentElem (v * v.conjTranspose)) :
    v * v.conjTranspose * v = v := by
  have := mul_conjTranspose_mul_self_of_isIdempotentElem_conjTranspose_mul_self
    (v := v.conjTranspose) (by rwa [conjTranspose_conjTranspose])
  simpa [CStarMatrix.mul_assoc] using congrArg conjTranspose this

end Proper

/-! ### Block sums -/

/-- The block sum `M ⊕ N` of two rectangular C⋆-matrices: the block matrix with `M` and `N` on
the diagonal and zero off-diagonal blocks. -/
@[expose] def blockSum [Zero A] (M : CStarMatrix l m A) (N : CStarMatrix n o A) :
    CStarMatrix (l ⊕ n) (m ⊕ o) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M) 0 0 (ofMatrix.symm N))

/-- Reading a block sum of C⋆-matrices as an ordinary matrix gives `Matrix.fromBlocks` with zero
off-diagonal blocks. -/
@[simp]
theorem ofMatrix_symm_blockSum [Zero A] (M : CStarMatrix l m A) (N : CStarMatrix n o A) :
    ofMatrix.symm (blockSum M N) = Matrix.fromBlocks (ofMatrix.symm M) 0 0 (ofMatrix.symm N) :=
  (rfl)

/-- The conjugate transpose of a block sum is the block sum of the conjugate transposes. -/
@[simp]
theorem conjTranspose_blockSum [AddMonoid A] [StarAddMonoid A] (M : CStarMatrix l m A)
    (N : CStarMatrix n o A) :
    (blockSum M N).conjTranspose = blockSum M.conjTranspose N.conjTranspose := by
  change ofMatrix (Matrix.fromBlocks (ofMatrix.symm M) 0 0 (ofMatrix.symm N))ᴴ = _
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero]
  rfl

/-- Block sums multiply blockwise. -/
@[simp]
theorem blockSum_mul_blockSum {p q : Type*} [Fintype m] [Fintype o] [NonUnitalNonAssocSemiring A]
    (M : CStarMatrix l m A) (N : CStarMatrix n o A) (M' : CStarMatrix m p A)
    (N' : CStarMatrix o q A) : blockSum M N * blockSum M' N' = blockSum (M * M') (N * N') := by
  change ofMatrix (Matrix.fromBlocks (ofMatrix.symm M) 0 0 (ofMatrix.symm N) *
    Matrix.fromBlocks (ofMatrix.symm M') 0 0 (ofMatrix.symm N')) = _
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rfl

/-- Applying a zero-preserving map to every entry of a block sum gives the block sum of the
entrywise images. -/
theorem blockSum_map [Zero A] [Zero B] (M : CStarMatrix l m A) (N : CStarMatrix n o A)
    {f : A → B} (hf : f 0 = 0) : (blockSum M N).map f = blockSum (M.map f) (N.map f) := by
  change ofMatrix ((Matrix.fromBlocks (ofMatrix.symm M) 0 0 (ofMatrix.symm N)).map f) = _
  simp only [Matrix.fromBlocks_map, Matrix.map_zero f hf]
  rfl

/-- The block sum of two star projections is a star projection. -/
theorem isStarProjection_blockSum [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A]
    [StarAddMonoid A] {p : CStarMatrix m m A} {q : CStarMatrix n n A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) : IsStarProjection (blockSum p q) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, blockSum_mul_blockSum, hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]
  · rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_blockSum, ← star_eq_conjTranspose,
      ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]

end Rectangular

/-- Entries of a finite sum of C⋆-matrices are the sums of the entries. -/
theorem sum_apply {m : Type*} [AddCommMonoid A] {ι : Type*} (s : Finset ι)
    (f : ι → CStarMatrix m n A) (i : m) (j : n) : (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j :=
  Matrix.sum_apply i j s f

/-- The entry of the `1 × 1` C⋆-matrix associated to `a`. -/
@[simp]
theorem toOneByOne_apply [Unique n] [Semiring R] [AddCommMonoid A] [Mul A] [Star A] [Module R A]
    (a : A) (i j : n) : toOneByOne n R A a i j = a :=
  rfl

variable (R) in
/-- The transpose of C⋆-matrices, as a linear map. -/
def transposeₗ {m : Type*} [Semiring R] [AddCommMonoid A] [Module R A] :
    CStarMatrix m n A →ₗ[R] CStarMatrix n m A where
  toFun M := M.transpose
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem transposeₗ_apply {m : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    (M : CStarMatrix m n A) : transposeₗ R M = M.transpose :=
  (rfl)

/-- Applying the zero linear map to every entry gives the zero matrix. -/
@[simp]
theorem map_zero_linearMap {m B : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (M : CStarMatrix m n A) : M.map ⇑(0 : A →ₗ[R] B) = 0 := by
  ext
  simp [zero_apply]

/-- Applying a sum of linear maps to every entry gives the sum of the entrywise images. -/
theorem map_add_linearMap {m B : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (M : CStarMatrix m n A) (f g : A →ₗ[R] B) :
    M.map ⇑(f + g) = M.map f + M.map g := by
  ext
  simp [add_apply]

/-- Applying a scalar multiple of a linear map to every entry gives the scalar multiple of the
entrywise image. -/
theorem map_smul_linearMap {m B : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (M : CStarMatrix m n A) (c : R) (f : A →ₗ[R] B) :
    M.map ⇑(c • f) = c • M.map f := by
  ext
  simp [smul_apply]

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

/-- `CStarMatrix.ofMatrixₗ` is `CStarMatrix.ofMatrix`. -/
@[simp]
lemma ofMatrixₗ_apply {m : Type*} [AddCommMonoid A] [Semiring R] [Module R A]
    (M : Matrix m n A) : ofMatrixₗ (R := R) M = ofMatrix M := (rfl)

/-- The inverse of `CStarMatrix.ofMatrixₗ` is the inverse of `CStarMatrix.ofMatrix`. -/
@[simp]
lemma ofMatrixₗ_symm_apply {m : Type*} [AddCommMonoid A] [Semiring R] [Module R A]
    (M : CStarMatrix m n A) : (ofMatrixₗ (R := R)).symm M = ofMatrix.symm M := (rfl)

end Algebraic

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
  -- Reduce positivity to showing no compression `star N * M * N` equals a nonzero `-(star R * R)`.
  refine hsa.nonneg_of_star_mul_mul_eq_neg_imp_eq_zero fun R N hRN => ?_
  classical
  have hv (y : n → A) : ofMatrix.symm R *ᵥ y = 0 := by
    have hneg : ofMatrix.symm (-(star R * R)) = -ofMatrix.symm (star R * R) :=
      ofMatrix.symm_apply_eq.mpr (by rw [← neg_of, Equiv.apply_symm_apply])
    have hpair : star (ofMatrix.symm N *ᵥ y) ⬝ᵥ (ofMatrix.symm M *ᵥ (ofMatrix.symm N *ᵥ y)) =
        -(star (ofMatrix.symm R *ᵥ y) ⬝ᵥ (ofMatrix.symm R *ᵥ y)) := by
      calc star (ofMatrix.symm N *ᵥ y) ⬝ᵥ (ofMatrix.symm M *ᵥ (ofMatrix.symm N *ᵥ y))
          = star y ⬝ᵥ (ofMatrix.symm (star N * M * N) *ᵥ y) := by
            simp [star_mulVec, ← dotProduct_mulVec, mul_assoc]
        _ = -(star (ofMatrix.symm R *ᵥ y) ⬝ᵥ (ofMatrix.symm R *ᵥ y)) := by
            rw [hRN, hneg, neg_mulVec, dotProduct_neg, key]
    have h := Left.nonneg_neg_iff.mp (hpair ▸ hQ (ofMatrix.symm N *ᵥ y))
    exact dotProduct_star_self_eq_zero.mp (le_antisymm h (dotProduct_star_self_nonneg _))
  refine ext fun i j => ?_
  have h := congrFun (hv (Pi.single j (star (R i j)))) i
  simp only [mulVec_single, Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, ofMatrix_symm_apply, Pi.zero_apply, mul_star_self_eq_zero] at h
  rw [h, zero_apply]

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
