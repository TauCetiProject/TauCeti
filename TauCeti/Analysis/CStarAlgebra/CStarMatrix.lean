/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Algebra.Star.Basic
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.Compression
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Algebra.Order.Star.Unitization
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Composition
import TauCeti.LinearAlgebra.Matrix.PartialIsometry
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Rectangular matrix operations and positivity by quadratic forms

We record associativity and conjugate-transpose identities for rectangular C⋆-matrices, together
with their conversion to ordinary matrices.

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
the transpose as a linear map, the star algebra isomorphism `M_m(M_n(A)) ≃ M_{m × n}(A)`, the
diagonal embedding `b ↦ diag(b, …, b)` and the matrix units `eᵢⱼ` of `M_n(ℂ)`.

## Main declarations

* `CStarMatrix.instNonUnitalContinuousFunctionalCalculusReal`: the real continuous functional
  calculus of `CStarMatrix n n A`, which instance search does not find on its own.
* `CStarMatrix.instSeparableSpace`: finite matrices over a separable C⋆-algebra form a separable
  space.
* `CStarMatrix.instModuleFinite`: `CStarMatrix m n A` is a finite module over finite index
  types when `A` is finite, so `CStarMatrix m n ℂ` is finite-dimensional.
* `CStarMatrix.ofMatrix_symm_mul`, `CStarMatrix.ofMatrix_symm_conjTranspose`,
  `CStarMatrix.ofMatrix_symm_star`: reading a C⋆-matrix as an ordinary matrix preserves
  rectangular multiplication and conjugate transpose, and sends `star` to conjugate transpose; the
  companions `CStarMatrix.ofMatrix_symm_zero`, `ofMatrix_symm_one`, `ofMatrix_symm_add`,
  `ofMatrix_symm_neg`, `ofMatrix_symm_sub` and `ofMatrix_symm_smul` do the same for the other
  algebraic operations.
* `CStarMatrix.isStarProjection_ofMatrix_symm_iff`, `CStarMatrix.isStarProjection_ofMatrix_iff`:
  a C⋆-matrix is a star projection exactly when the underlying matrix is; companions
  `CStarMatrix.isSelfAdjoint_ofMatrix_iff` and `CStarMatrix.ofMatrix_mem_unitary_iff` do the same
  for self-adjoint and unitary matrices.
* `CStarMatrix.mul_eq_self_of_conjTranspose_mul_eq`: over a star-ordered ring with proper star,
  a rectangular matrix is supported on its initial projection.
* `CStarMatrix.sum_apply`, `CStarMatrix.toOneByOne_apply`, `CStarMatrix.reindexₐ_apply_apply`:
  entries of finite sums, of `1 × 1` C⋆-matrices and of reindexed matrices, with
  `CStarMatrix.norm_toOneByOne`: `‖[a]‖ = ‖a‖`, and
  `CStarMatrix.norm_map_toOneByOne_linearMap`: `‖[φ a]‖ = ‖φ a‖` for a linear map `φ`.
* `CStarMatrix.norm_map_reindexₐ_linearMap`: reindexing preserves the norm of the entrywise
  image under a linear map.
* `CStarMatrix.transposeₗ`: the transpose of C⋆-matrices, as a linear map.
* `CStarMatrix.matrixUnit`: the matrix units `e_ij` of `M_n(ℂ)`, with
  `CStarMatrix.ofMatrix_symm_matrixUnit`, `CStarMatrix.star_matrixUnit`,
  `CStarMatrix.matrixUnit_mul_matrixUnit`, `CStarMatrix.isStarProjection_matrixUnit` (`e_ii` is a
  projection) and `CStarMatrix.norm_matrixUnit`: `‖e_ij‖ = 1`.
* `CStarMatrix.compStarAlgEquiv`: `Matrix.comp` as a star algebra isomorphism
  `M_m(M_n(A)) ≃ M_{m × n}(A)`.
* `CStarMatrix.diagonalNonUnitalStarAlgHom`: the diagonal embedding `b ↦ diag(b, …, b)` of `B`
  in `M_n(B)`, with `CStarMatrix.norm_diagonalNonUnitalStarAlgHom_le` and
  `CStarMatrix.norm_map_toSpanSingleton_le`: `‖[xᵢⱼ • a]‖ ≤ ‖x‖ ‖a‖` for a scalar matrix `x`.
* `CStarMatrix.map_zero_linearMap`, `CStarMatrix.map_add_linearMap`,
  `CStarMatrix.map_smul_linearMap`: applying `0`, `f + g` or `c • f` to every entry.
* `CStarMatrix.isSelfAdjoint_of_forall_isSelfAdjoint_sum`: a matrix all of whose quadratic forms
  are self-adjoint is self-adjoint. This is purely algebraic, and holds over any complex
  star-algebra whose star is proper.
* `CStarMatrix.sum_star_mul_mul_eq_dotProduct_mulVec`: rewriting a quadratic form as a
  dot product with `mulVec`.
* `CStarMatrix.nonneg_iff_forall_sum_nonneg`: the quadratic-form criterion for positivity, with
  `CStarMatrix.ofMatrix_smul_nonneg` (`[pᵢⱼ b]` is positive for positive `[pᵢⱼ]` and `b`).
* `CStarMatrix.diag_nonneg_of_nonneg`: the diagonal entries of a positive matrix are positive.
* `CStarMatrix.submatrix_nonneg` and `CStarMatrix.extend_nonneg`: reindexing a positive matrix
  along any map of indices, or extending it by zero along an injective one, gives a positive
  matrix.
* `CStarMatrix.map_fromBlocks_inl_nonneg` and `CStarMatrix.map_toBlocks₂₂_nonneg`: embedding a
  block matrix into the top-left corner and extracting the bottom-right block preserve positivity.
* `CStarMatrix.norm_sq_smul_sub_mulLeft_nonneg`: positivity of the matrix
  `(‖c‖ ^ 2 • (star (a i) * a j) - star (c * a i) * (c * a j))`.
* `WithCStarModule.norm_equiv_symm_pi_smul`: the vector `(vᵢ a)ᵢ` of the Hilbert `A`-module `Aᵐ`
  has norm `‖v‖ ‖a‖`.
* `CStarMatrix.norm_sum_smul_le`: compressing `x ∈ M_{m,n}(A)` by scalar vectors `v`, `w` gives
  `‖∑ i j, (vᵢ wⱼ*) xᵢⱼ‖ ≤ ‖v‖ ‖x‖ ‖w‖`. The proof tests `x` against the vectors `(vᵢ a)ᵢ` and
  `(wⱼ b)ⱼ` of `Aᵐ` and `Aⁿ`, which bounds `‖a z b*‖` for the compression `z`, and takes `a = z*`,
  `b = z* z`; no unit is needed.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Lemma 4.1.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Lemma 3.1.
-/

public section

open Matrix

namespace CStarMatrix

section Comp

variable (R m n A : Type*) [Fintype m] [Fintype n] [AddCommMonoid A] [Mul A] [Star A] [SMul R A]

/-- An `m × m` matrix of `n × n` matrices is an `(m × n) × (m × n)` matrix: `Matrix.comp` as a
star algebra isomorphism of C⋆-matrices. Multiplication of C⋆-matrices is multiplication of the
underlying matrices, so it is preserved by `Matrix.compRingEquiv`. -/
def compStarAlgEquiv :
    CStarMatrix m m (CStarMatrix n n A) ≃⋆ₐ[R] CStarMatrix (m × n) (m × n) A where
  toFun M := ofMatrix (Matrix.comp m m n n A M)
  invFun M := (Matrix.comp m m n n A).symm (ofMatrix.symm M)
  left_inv := (Matrix.comp m m n n A).left_inv
  right_inv := (Matrix.comp m m n n A).right_inv
  map_add' _ _ := rfl
  map_mul' := (Matrix.compRingEquiv m n A).map_mul
  map_smul' _ _ := rfl
  map_star' M := by
    ext ⟨i, k⟩ ⟨j, l⟩
    -- `Matrix.comp` takes a `Matrix` of `Matrix`es, so `Matrix.comp_apply` does not rewrite it at
    -- the C⋆-matrix `star M`; `change` reads both entries through the definition of `comp`.
    change (star M) i j k l = star (M j i l k)
    simp only [CStarMatrix.star_apply]

variable {R m n A}

@[simp]
theorem compStarAlgEquiv_apply (M : CStarMatrix m m (CStarMatrix n n A)) (i j : m × n) :
    compStarAlgEquiv R m n A M i j = M i.1 j.1 i.2 j.2 :=
  (rfl)

@[simp]
theorem compStarAlgEquiv_symm_apply (M : CStarMatrix (m × n) (m × n) A) (i j : m) (k l : n) :
    (compStarAlgEquiv R m n A).symm M i j k l = M (i, k) (j, l) :=
  (rfl)

/-- Applying a map entrywise commutes with `compStarAlgEquiv`. -/
theorem compStarAlgEquiv_map {B : Type*} [AddCommMonoid B] [Mul B] [Star B] [SMul R B]
    (M : CStarMatrix m m (CStarMatrix n n A)) (f : A → B) :
    compStarAlgEquiv R m n B (M.map (·.map f)) = (compStarAlgEquiv R m n A M).map f :=
  (rfl)

end Comp

section Diagonal

variable (R n B : Type*) [Fintype n] [DecidableEq n] [Monoid R] [NonUnitalNonAssocSemiring B]
  [StarAddMonoid B] [DistribMulAction R B]

/-- The diagonal embedding `b ↦ diag(b, …, b)` of `B` in `CStarMatrix n n B`. The operations of
C⋆-matrices are those of the underlying matrices, so each field is the corresponding identity
for `Matrix.diagonal`. -/
def diagonalNonUnitalStarAlgHom : B →⋆ₙₐ[R] CStarMatrix n n B where
  toFun b := ofMatrix (Matrix.diagonal fun _ => b)
  map_smul' c b := congrArg ofMatrix (Matrix.diagonal_smul c fun _ : n => b)
  map_zero' := congrArg ofMatrix Matrix.diagonal_zero
  map_add' a b := congrArg ofMatrix (Matrix.diagonal_add (fun _ : n => a) fun _ => b).symm
  map_mul' a b := congrArg ofMatrix (Matrix.diagonal_mul_diagonal (fun _ : n => a) fun _ => b).symm
  map_star' b := congrArg ofMatrix (Matrix.diagonal_conjTranspose fun _ : n => b).symm

variable {R n B}

@[simp]
theorem diagonalNonUnitalStarAlgHom_apply (b : B) (i j : n) :
    diagonalNonUnitalStarAlgHom R n B b i j = if i = j then b else 0 :=
  Matrix.diagonal_apply ..

end Diagonal

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

/-- Matrices over finite index types with entries in a finite module form a finite module. In
particular `CStarMatrix m n ℂ` is finite-dimensional. -/
instance instModuleFinite {m : Type*} [Finite m] [Finite n] [Semiring R] [AddCommMonoid A]
    [Module R A] [Module.Finite R A] : Module.Finite R (CStarMatrix m n A) :=
  inferInstanceAs (Module.Finite R (m → n → A))

/-- Reading a C⋆-matrix as an ordinary matrix respects multiplication. -/
@[simp]
lemma ofMatrix_symm_mul {m k : Type*} [Fintype n] [Mul A] [AddCommMonoid A]
    (M : CStarMatrix m n A) (N : CStarMatrix n k A) :
    ofMatrix.symm (M * N) = ofMatrix.symm M * ofMatrix.symm N := (rfl)

/-- Reading a rectangular C⋆-matrix as an ordinary matrix preserves conjugate transpose. -/
@[simp]
lemma ofMatrix_symm_conjTranspose {m : Type*} [Star A] (M : CStarMatrix m n A) :
    ofMatrix.symm M.conjTranspose = (ofMatrix.symm M)ᴴ := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix sends `star` to the conjugate transpose. -/
@[simp]
lemma ofMatrix_symm_star [Star A] (M : CStarMatrix n n A) :
    ofMatrix.symm (star M) = (ofMatrix.symm M)ᴴ := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix sends `0` to `0`. -/
@[simp]
lemma ofMatrix_symm_zero [Zero A] : ofMatrix.symm (0 : CStarMatrix n n A) = 0 := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix sends `1` to `1`. -/
@[simp]
lemma ofMatrix_symm_one [DecidableEq n] [Zero A] [One A] :
    ofMatrix.symm (1 : CStarMatrix n n A) = 1 := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix respects addition. -/
@[simp]
lemma ofMatrix_symm_add [Add A] (M N : CStarMatrix n n A) :
    ofMatrix.symm (M + N) = ofMatrix.symm M + ofMatrix.symm N := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix respects negation. -/
@[simp]
lemma ofMatrix_symm_neg [Neg A] (M : CStarMatrix n n A) :
    ofMatrix.symm (-M) = -ofMatrix.symm M := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix respects subtraction. -/
@[simp]
lemma ofMatrix_symm_sub [Sub A] (M N : CStarMatrix n n A) :
    ofMatrix.symm (M - N) = ofMatrix.symm M - ofMatrix.symm N := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix respects scalar multiplication. -/
@[simp]
lemma ofMatrix_symm_smul [SMul R A] (r : R) (M : CStarMatrix n n A) :
    ofMatrix.symm (r • M) = r • ofMatrix.symm M := (rfl)

/-- Rectangular matrix multiplication is associative. -/
lemma mul_assoc_rectangular {m k l : Type*} [Fintype n] [Fintype k] [NonUnitalSemiring A]
    (M : CStarMatrix m n A) (N : CStarMatrix n k A) (P : CStarMatrix k l A) :
    (M * N) * P = M * (N * P) := by
  apply ofMatrix.symm.injective
  simp only [ofMatrix_symm_mul, Matrix.mul_assoc]

/-- Conjugate transpose reverses rectangular multiplication. -/
@[simp]
lemma conjTranspose_mul {m k : Type*} [Fintype n] [NonUnitalNonAssocSemiring A] [StarRing A]
    (M : CStarMatrix m n A) (N : CStarMatrix n k A) :
    (M * N).conjTranspose = N.conjTranspose * M.conjTranspose := by
  apply ofMatrix.symm.injective
  simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Matrix.conjTranspose_mul]

/-- Conjugate transpose of rectangular matrices is involutive. -/
@[simp]
lemma conjTranspose_conjTranspose {m : Type*} [InvolutiveStar A] (M : CStarMatrix m n A) :
    M.conjTranspose.conjTranspose = M := by
  apply ofMatrix.symm.injective
  simp only [ofMatrix_symm_conjTranspose, Matrix.conjTranspose_conjTranspose]

/-- A C⋆-matrix is a star projection exactly when the underlying matrix is. -/
@[simp]
lemma isStarProjection_ofMatrix_symm_iff [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {M : CStarMatrix n n A} : IsStarProjection (ofMatrix.symm M) ↔ IsStarProjection M := by
  have h₁ : ofMatrix.symm M * ofMatrix.symm M = ofMatrix.symm M ↔ M * M = M := by
    rw [← ofMatrix_symm_mul, ofMatrix.symm.injective.eq_iff]
  have h₂ : star (ofMatrix.symm M) = ofMatrix.symm M ↔ star M = M := by
    rw [Matrix.star_eq_conjTranspose, ← ofMatrix_symm_star, ofMatrix.symm.injective.eq_iff]
  simp only [isStarProjection_iff, IsIdempotentElem, IsSelfAdjoint, h₁, h₂]

/-- A matrix is a star projection exactly when it is one as a C⋆-matrix. -/
@[simp]
lemma isStarProjection_ofMatrix_iff [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {M : Matrix n n A} : IsStarProjection (ofMatrix M) ↔ IsStarProjection M := by
  rw [← isStarProjection_ofMatrix_symm_iff, Equiv.symm_apply_apply]

/-- A matrix is self-adjoint exactly when it is self-adjoint as a C⋆-matrix. -/
@[simp]
lemma isSelfAdjoint_ofMatrix_iff [Star A] {M : Matrix n n A} :
    IsSelfAdjoint (ofMatrix M) ↔ IsSelfAdjoint M :=
  Iff.rfl

/-- A C⋆-matrix is self-adjoint exactly when the underlying matrix is. -/
@[simp]
lemma isSelfAdjoint_ofMatrix_symm_iff [Star A] {M : CStarMatrix n n A} :
    IsSelfAdjoint (ofMatrix.symm M) ↔ IsSelfAdjoint M :=
  Iff.rfl

/-- A matrix is unitary exactly when it is unitary as a C⋆-matrix. -/
@[simp]
lemma ofMatrix_mem_unitary_iff [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
    {M : Matrix n n A} : ofMatrix M ∈ unitary (CStarMatrix n n A) ↔ M ∈ unitary (Matrix n n A) :=
  Iff.rfl

/-- A C⋆-matrix is unitary exactly when the underlying matrix is. -/
@[simp]
lemma ofMatrix_symm_mem_unitary_iff [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
    {M : CStarMatrix n n A} :
    ofMatrix.symm M ∈ unitary (Matrix n n A) ↔ M ∈ unitary (CStarMatrix n n A) :=
  Iff.rfl

/-- Over a star-ordered ring with proper star, a rectangular matrix whose initial Gram matrix is
an idempotent `p` is supported on `p`. -/
lemma mul_eq_self_of_conjTranspose_mul_eq {m : Type*} [Fintype m] [Fintype n] [NonUnitalRing A]
    [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A] {p : CStarMatrix m m A}
    (v : CStarMatrix n m A) (hp : IsIdempotentElem p) (hv : v.conjTranspose * v = p) :
    v * p = v := by
  have hp' : IsIdempotentElem (v.conjTranspose * v) := by
    rw [hv]
    exact hp
  have hpM := congrArg ofMatrix.symm hp'.eq
  simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] at hpM
  have h := Matrix.mul_conjTranspose_mul_self_of_isIdempotentElem (ofMatrix.symm v) hpM
  rw [← hv]
  apply ofMatrix.symm.injective
  simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Matrix.mul_assoc] using h

/-- Entries of a finite sum of C⋆-matrices are the sums of the entries. -/
theorem sum_apply {m : Type*} [AddCommMonoid A] {ι : Type*} (s : Finset ι)
    (f : ι → CStarMatrix m n A) (i : m) (j : n) : (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j :=
  Matrix.sum_apply i j s f

/-- The entry of the `1 × 1` C⋆-matrix associated to `a`. -/
@[simp]
theorem toOneByOne_apply [Unique n] [Semiring R] [AddCommMonoid A] [Mul A] [Star A] [Module R A]
    (a : A) (i j : n) : toOneByOne n R A a i j = a :=
  rfl

/-- The entries of a reindexed C⋆-matrix. Mathlib's `CStarMatrix.reindexₐ_apply` has right-hand
side `Matrix.reindex e e M i j` with `M` a `CStarMatrix`, which is not type-correct at instance
transparency, so neither `simp` nor `rw` can continue from it to `Matrix.reindex_apply`; this
states the entry directly, and `simp` tries it first. -/
@[simp high]
theorem reindexₐ_apply_apply {m : Type*} [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A]
    [Mul A] [Star A] [Module R A] (e : m ≃ n) (M : CStarMatrix m m A) (i j : n) :
    reindexₐ R A e M i j = M (e.symm i) (e.symm j) :=
  (rfl)

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

/-- Applying a map entrywise commutes with `reindexₐ`. -/
theorem reindexₐ_map {m B : Type*} [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A]
    [Star A] [Module R A] [AddCommMonoid B] [Mul B] [Star B] [Module R B] (e : m ≃ n)
    (M : CStarMatrix m m A) (f : A → B) :
    reindexₐ R B e (M.map f) = (reindexₐ R A e M).map f :=
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

/-- The quadratic form `∑ i, ∑ j, star (x i) * M i j * x j` written as the matrix-vector
product `star x ⬝ᵥ (ofMatrix.symm M *ᵥ x)`. -/
theorem sum_star_mul_mul_eq_dotProduct_mulVec [Fintype n] [NonUnitalSemiring A] [Star A]
    (M : CStarMatrix n n A) (x : n → A) :
    ∑ i, ∑ j, star (x i) * M i j * x j = star x ⬝ᵥ (ofMatrix.symm M *ᵥ x) := by
  rw [dot_mulVec_eq_sum_sum, Finset.sum_comm]
  simp [ofMatrix_symm_apply]

/-- A matrix over a complex star-algebra with proper star all of whose quadratic forms are
self-adjoint is self-adjoint. -/
theorem isSelfAdjoint_of_forall_isSelfAdjoint_sum [Fintype n] [NonUnitalRing A] [StarRing A]
    [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] [IsProperStar A]
    {M : CStarMatrix n n A}
    (hM : ∀ x : n → A, IsSelfAdjoint (∑ i, ∑ j, star (x i) * M i j * x j)) :
    IsSelfAdjoint M := by
  classical
  replace hM (x : n → A) : IsSelfAdjoint (star x ⬝ᵥ (ofMatrix.symm M *ᵥ x)) := by
    rw [← sum_star_mul_mul_eq_dotProduct_mulVec]
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

/-- A matrix space over a separable C⋆-algebra with finite index types is separable. -/
instance instSeparableSpace {m n A : Type*} [Finite m] [Finite n] [NonUnitalCStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] :
    TopologicalSpace.SeparableSpace (CStarMatrix m n A) :=
  inferInstanceAs (TopologicalSpace.SeparableSpace (m → n → A))

section MatrixUnit

variable {n : Type*} [DecidableEq n]

/-- The matrix unit `e_ij` of `M_n(ℂ)`, with entry `1` at `(i, j)` and `0` elsewhere. -/
def matrixUnit (i j : n) : CStarMatrix n n ℂ :=
  ofMatrix (Matrix.single i j 1)

/-- Reading `e_ij` as an ordinary matrix gives `Matrix.single i j 1`. -/
@[simp]
theorem ofMatrix_symm_matrixUnit (i j : n) :
    ofMatrix.symm (matrixUnit i j) = Matrix.single i j 1 :=
  (rfl)

/-- The entries of `e_ij`. -/
theorem matrixUnit_apply (i j k l : n) :
    matrixUnit i j k l = if i = k ∧ j = l then 1 else 0 := by
  simp [matrixUnit, Matrix.single_apply]

/-- The `(i, j)` entry of `e_ij` is `1`. -/
@[simp]
theorem matrixUnit_apply_same (i j : n) : matrixUnit i j i j = 1 := by
  simp [matrixUnit_apply]

/-- The entries of `e_ij` away from `(i, j)` vanish. -/
@[simp]
theorem matrixUnit_apply_of_ne {i j k l : n} (h : ¬(i = k ∧ j = l)) : matrixUnit i j k l = 0 := by
  simp [matrixUnit_apply, h]

/-- The adjoint of `e_ij` is `e_ji`. -/
@[simp]
theorem star_matrixUnit (i j : n) : star (matrixUnit i j) = matrixUnit j i := by
  ext r s
  simp [matrixUnit_apply, star_apply, and_comm, apply_ite]

variable [Fintype n]

/-- `e_ij` is the image of `Matrix.single i j 1` under `CStarMatrix.ofMatrixStarAlgEquiv`. -/
theorem matrixUnit_eq_ofMatrixStarAlgEquiv (i j : n) :
    matrixUnit i j = ofMatrixStarAlgEquiv (Matrix.single i j 1) :=
  (rfl)

/-- Matrix units multiply as `e_ij e_jk = e_ik`. -/
@[simp]
theorem matrixUnit_mul_matrixUnit (i j k : n) :
    matrixUnit i j * matrixUnit j k = matrixUnit i k := by
  rw [matrixUnit_eq_ofMatrixStarAlgEquiv, matrixUnit_eq_ofMatrixStarAlgEquiv,
    matrixUnit_eq_ofMatrixStarAlgEquiv, ← map_mul, single_mul_single_same, one_mul]

/-- Matrix units multiply as `e_ij e_kl = 0` when `j ≠ k`. -/
@[simp]
theorem matrixUnit_mul_matrixUnit_of_ne (i : n) {j k : n} (l : n) (h : j ≠ k) :
    matrixUnit i j * matrixUnit k l = 0 := by
  rw [matrixUnit_eq_ofMatrixStarAlgEquiv, matrixUnit_eq_ofMatrixStarAlgEquiv, ← map_mul,
    single_mul_single_of_ne _ _ _ _ h, map_zero]

/-- The diagonal matrix unit `e_ii` is a self-adjoint idempotent. -/
theorem isStarProjection_matrixUnit (i : n) : IsStarProjection (matrixUnit i i) :=
  ⟨matrixUnit_mul_matrixUnit i i i, star_matrixUnit i i⟩

open scoped ComplexOrder in
/-- A matrix unit has norm one: `e_jj` is a nonzero projection and `e_ij⋆ e_ij = e_jj`. -/
@[simp]
theorem norm_matrixUnit (i j : n) : ‖matrixUnit i j‖ = 1 := by
  have hp : ‖matrixUnit j j‖ = 1 :=
    (isStarProjection_matrixUnit j).norm_eq_one
      fun h0 => by simpa using congrFun (congrFun h0 j) j
  have h := CStarRing.norm_star_mul_self (x := matrixUnit i j)
  rw [star_matrixUnit, matrixUnit_mul_matrixUnit, hp] at h
  nlinarith [norm_nonneg (matrixUnit i j)]

end MatrixUnit

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
  simp_rw [sum_star_mul_mul_eq_dotProduct_mulVec]
  refine ⟨fun hM x => ?_, fun hQ => ?_⟩
  · obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
    rw [key]
    exact dotProduct_star_self_nonneg _
  have hsa : IsSelfAdjoint M := isSelfAdjoint_of_forall_isSelfAdjoint_sum fun x => by
    rw [sum_star_mul_mul_eq_dotProduct_mulVec]
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

/-- Embedding a positive block matrix `M : CStarMatrix k k (CStarMatrix n n A)` into the top-left
block of `CStarMatrix k k (CStarMatrix (n ⊕ m) (n ⊕ m) A)` preserves positivity. -/
theorem map_fromBlocks_inl_nonneg {k m : Type*} [Fintype k] [Fintype m]
    {M : CStarMatrix k k (CStarMatrix n n A)} (hM : 0 ≤ M) :
    0 ≤ M.map fun B =>
      ofMatrix (Matrix.fromBlocks (ofMatrix.symm B) 0 0 0 : Matrix (n ⊕ m) (n ⊕ m) A) := by
  let e₁ := compStarAlgEquiv ℂ k n A
  let e₂ := compStarAlgEquiv ℂ k (n ⊕ m) A
  have hM₁ : 0 ≤ e₁ M := by simpa using (map_le_map_iff e₁).mpr hM
  have hf : Function.Injective (Prod.map (id : k → k) (Sum.inl : n → n ⊕ m)) :=
    Function.injective_id.prodMap Sum.inl_injective
  rw [← map_le_map_iff e₂, map_zero]
  convert extend_nonneg hf hM₁ using 1
  ext ⟨i, p⟩ ⟨j, q⟩
  have h_ext (g : k × n → A) (e' : k × (n ⊕ m) → A) (i : k) (p : n) :
      Function.extend (Prod.map id Sum.inl) g e' (i, Sum.inl p) = g (i, p) :=
    hf.extend_apply g e' (i, p)
  rcases p with p | p <;> rcases q with q | q
  · simp [e₂, e₁, h_ext, ofMatrix_symm_apply]
  · simp [e₂, e₁, h_ext]
  · simp [e₂, e₁]
  · simp [e₂, e₁]

/-- Extracting the bottom-right block of each entry of a positive block matrix
`M : CStarMatrix k k (CStarMatrix (n ⊕ m) (n ⊕ m) A)` preserves positivity. -/
theorem map_toBlocks₂₂_nonneg {k m : Type*} [Fintype k] [Fintype m]
    {M : CStarMatrix k k (CStarMatrix (n ⊕ m) (n ⊕ m) A)} (hM : 0 ≤ M) :
    0 ≤ M.map fun B => ofMatrix (ofMatrix.symm B).toBlocks₂₂ := by
  let e₂ := compStarAlgEquiv ℂ k (n ⊕ m) A
  let e₃ := compStarAlgEquiv ℂ k m A
  have hM₂ : 0 ≤ e₂ M := by simpa using (map_le_map_iff e₂).mpr hM
  rw [← map_le_map_iff e₃, map_zero]
  convert submatrix_nonneg (Prod.map id Sum.inr) hM₂ using 1
  ext ⟨i, p⟩ ⟨j, q⟩
  simp [e₃, e₂, Matrix.toBlocks₂₂]

/-- For any `c : A` and finite family `a : n → A`, the matrix with `(i, j)`-entry
`‖c‖ ^ 2 • (star (a i) * a j) - star (c * a i) * (c * a j)` is positive in `CStarMatrix n n A`. -/
theorem norm_sq_smul_sub_mulLeft_nonneg (c : A) (a : n → A) :
    0 ≤ ofMatrix (Matrix.of fun i j =>
      (‖c‖ ^ 2 : ℝ) • (star (a i) * a j) - star (c * a i) * (c * a j)) := by
  rw [nonneg_iff_forall_sum_nonneg]
  intro y
  have hvec (b : n → A) : star y ⬝ᵥ (Matrix.vecMulVec (star b) b *ᵥ y) =
      star (b ⬝ᵥ y) * (b ⬝ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMulVec, smul_dotProduct, smul_eq_mul,
      Matrix.star_dotProduct_star]
  let M : Matrix n n A :=
    (‖c‖ ^ 2 : ℝ) • Matrix.vecMulVec (star a) a - Matrix.vecMulVec (star (c • a)) (c • a)
  have hM : ofMatrix (Matrix.of fun i j =>
      (‖c‖ ^ 2 : ℝ) • (star (a i) * a j) - star (c * a i) * (c * a j)) = ofMatrix M := by
    ext i j
    simp [M, Matrix.vecMulVec_apply]
  rw [hM, sum_star_mul_mul_eq_dotProduct_mulVec, ofMatrix.symm_apply_apply]
  simp only [M, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, hvec, smul_dotProduct,
    smul_eq_mul, star_mul, mul_assoc]
  rw [sub_nonneg, sq, ← CStarRing.norm_star_mul_self (x := c)]
  simpa only [← mul_assoc] using CStarAlgebra.star_left_conjugate_le_norm_smul (a ⬝ᵥ y) (star c * c)

/-- The diagonal matrix `diag(a, …, a)` has norm at most `‖a‖`. -/
theorem norm_diagonalNonUnitalStarAlgHom_le [DecidableEq n] (a : A) :
    ‖diagonalNonUnitalStarAlgHom ℂ n A a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le _ a

open scoped ComplexOrder in
/-- The Kronecker product `[pᵢⱼ b]` of a positive scalar matrix `[pᵢⱼ]` and a positive element `b`
is a positive matrix. -/
theorem ofMatrix_smul_nonneg {P : CStarMatrix n n ℂ} (hP : 0 ≤ P) {b : A} (hb : 0 ≤ b) :
    0 ≤ ofMatrix (Matrix.of fun i j => P i j • b) := by
  obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP
  refine nonneg_iff_forall_sum_nonneg.mpr fun w => ?_
  have h : ∑ i, ∑ j, star (w i) * ofMatrix (Matrix.of fun i j => (star R * R) i j • b) i j * w j =
      ∑ k, star (∑ i, R k i • w i) * b * ∑ j, R k j • w j := by
    simp only [ofMatrix_apply, Matrix.of_apply, mul_apply, star_apply, Finset.sum_smul,
      Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, star_sum, star_smul, smul_mul_assoc,
      mul_smul_comm, smul_smul, mul_assoc]
    refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans <| Finset.sum_comm.trans <|
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans <| Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  rw [h]
  exact Finset.sum_nonneg fun k _ => star_left_conjugate_nonneg hb _

/-- The `1 × 1` C⋆-matrix associated to `a` has norm `‖a‖`. -/
@[simp]
theorem norm_toOneByOne {ι : Type*} [Unique ι] (a : A) : ‖toOneByOne ι ℂ A a‖ = ‖a‖ :=
  StarAlgEquiv.norm_map (toOneByOne ι ℂ A) a

omit [PartialOrder A] [StarOrderedRing A] in
/-- Reindexing a square matrix does not change the norm of its entrywise image under a linear
map. -/
theorem norm_map_reindexₐ_linearMap {κ ι B : Type*} [Fintype κ] [Fintype ι]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] (x : CStarMatrix κ κ A)
    (e : κ ≃ ι) (φ : A →ₗ[ℂ] B) : ‖(reindexₐ ℂ A e x).map φ‖ = ‖x.map φ‖ := by
  rw [← reindexₐ_map, StarAlgEquiv.norm_map]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The entrywise image of the `1 × 1` C⋆-matrix `[a]` under a linear map `φ` has norm
`‖φ a‖`. -/
@[simp]
theorem norm_map_toOneByOne_linearMap {ι B : Type*} [Unique ι] [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] (a : A) (φ : A →ₗ[ℂ] B) :
    ‖(toOneByOne ι ℂ A a).map φ‖ = ‖φ a‖ := by
  have hmap : (toOneByOne ι ℂ A a).map φ = toOneByOne ι ℂ B (φ a) := by
    ext
    simp
  rw [hmap, norm_toOneByOne]

open scoped ComplexOrder in
/-- The entrywise image of the scalar matrix `x` under `z ↦ z • a` has norm at most `‖x‖ ‖a‖`.
In matrices over the unitization of `A` it is the product of `x` and `diag(a, …, a)`, and the
inclusion of `A` in its unitization is isometric on matrices. -/
theorem norm_map_toSpanSingleton_le (a : A) (x : CStarMatrix n n ℂ) :
    ‖x.map (LinearMap.toSpanSingleton ℂ A a)‖ ≤ ‖x‖ * ‖a‖ := by
  classical
  let ι : A →⋆ₙₐ[ℂ] Unitization ℂ A := Unitization.inrNonUnitalStarAlgHom ℂ A
  let ιₙ := mapₙₐ (n := n) ι
  have hιₙ : Function.Injective ιₙ := map_injective Unitization.inr_injective
  let α := mapₙₐ (n := n) ((StarAlgHom.ofId ℂ (Unitization ℂ A)).toNonUnitalStarAlgHom)
  have hfac : ιₙ (x.map (LinearMap.toSpanSingleton ℂ A a)) =
      α x * diagonalNonUnitalStarAlgHom ℂ n _ (ι a) := by
    refine ext fun i j ↦ ?_
    simp [ιₙ, α, ι, mul_apply, Unitization.algebraMap_eq_inl, Unitization.inl_mul_inr,
      Unitization.inr_smul]
  rw [← NonUnitalStarAlgHom.norm_map ιₙ hιₙ, hfac]
  refine (norm_mul_le _ _).trans (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le α x) ?_
    (norm_nonneg _) (norm_nonneg _))
  exact (norm_diagonalNonUnitalStarAlgHom_le _).trans (Unitization.norm_inr a).le

section Compression

open WithCStarModule CStarModule
open scoped InnerProductSpace ComplexOrder

variable {m n A : Type*} [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A]
  [StarOrderedRing A]

/-- The vector `(v i • a)ᵢ` of the Hilbert `A`-module `Aᵐ` has norm `‖v‖ ‖a‖`, for a vector `v`
of the Hilbert space `ℂᵐ` and `a ∈ A`. -/
theorem _root_.WithCStarModule.norm_equiv_symm_pi_smul (v : C⋆ᵐᵒᵈ(ℂ, m → ℂ)) (a : A) :
    ‖(equiv A (m → A)).symm fun i => v i • a‖ = ‖v‖ * ‖a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow, norm_sq_eq A, norm_sq_eq ℂ,
    pi_inner, pi_inner]
  simp only [equiv_symm_pi_apply, inner_def, smul_mul_smul_comm, star_smul, ← Finset.sum_smul,
    norm_smul, CStarRing.norm_self_mul_star, sq]

/-- Compressing a matrix over a C⋆-algebra by scalar vectors does not increase norms:
`‖∑ i j, (vᵢ wⱼ*) xᵢⱼ‖ ≤ ‖v‖ ‖x‖ ‖w‖`. -/
theorem norm_sum_smul_le (x : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(ℂ, m → ℂ))
    (w : C⋆ᵐᵒᵈ(ℂ, n → ℂ)) :
    ‖∑ i, ∑ j, (v i * star (w j)) • x i j‖ ≤ ‖v‖ * ‖x‖ * ‖w‖ := by
  set z := ∑ i, ∑ j, (v i * star (w j)) • x i j
  set K := ‖v‖ * ‖x‖ * ‖w‖
  have key (a b : A) : ‖a * z * star b‖ ≤ K * (‖a‖ * ‖b‖) := by
    let V : C⋆ᵐᵒᵈ(A, m → A) := (equiv A (m → A)).symm fun i => v i • a
    let W : C⋆ᵐᵒᵈ(A, n → A) := (equiv A (n → A)).symm fun j => w j • b
    have hz : ⟪W, toCLM x V⟫_A = a * z * star b := by
      simp only [pi_inner, toCLM_apply_eq_sum, equiv_symm_pi_apply, inner_def, V, W, z,
        Finset.sum_mul, Finset.mul_sum, star_smul, smul_mul_assoc, mul_smul_comm,
        Finset.smul_sum, smul_smul, mul_comm (star (w _))]
      exact Finset.sum_comm
    rw [← hz]
    calc ‖⟪W, toCLM x V⟫_A‖ ≤ ‖W‖ * ‖toCLM x V‖ := norm_inner_le _
      _ ≤ ‖W‖ * (‖x‖ * ‖V‖) := by gcongr; exact (toCLM x).le_opNorm V
      _ = K * (‖a‖ * ‖b‖) := by
        rw [norm_equiv_symm_pi_smul, norm_equiv_symm_pi_smul]; simp only [K]; ring
  have hs : star (star z * z) = star z * z := by simp
  have h := key (star z) (star z * z)
  have e : ‖star z * z * (star z * z)‖ = ‖star z * z‖ * ‖star z * z‖ := by
    nth_rw 1 [← hs]
    exact CStarRing.norm_star_mul_self (x := star z * z)
  rw [hs, ← mul_assoc, mul_assoc (star z * z), norm_star, e, CStarRing.norm_star_mul_self] at h
  rcases (norm_nonneg z).eq_or_lt with hz | hz
  · rw [← hz]
    positivity
  have h3 : 0 < ‖z‖ * (‖z‖ * ‖z‖) := by positivity
  nlinarith

end Compression

end CStarMatrix
