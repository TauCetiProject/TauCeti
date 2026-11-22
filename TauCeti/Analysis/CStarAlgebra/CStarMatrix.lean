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
the transpose as a linear map, the star algebra isomorphism `M_m(M_n(A)) ≃ M_{m × n}(A)` and the
diagonal embedding `b ↦ diag(b, …, b)`.

## Main declarations

* `CStarMatrix.instNonUnitalContinuousFunctionalCalculusReal`: the real continuous functional
  calculus of `CStarMatrix n n A`, which instance search does not find on its own.
* `CStarMatrix.ofMatrix_symm_mul`, `CStarMatrix.ofMatrix_symm_conjTranspose`,
  `CStarMatrix.ofMatrix_symm_star`: reading a C⋆-matrix as an ordinary matrix preserves
  rectangular multiplication and conjugate transpose, and sends `star` to conjugate transpose; the
  companions `CStarMatrix.ofMatrix_symm_zero`, `ofMatrix_symm_one`, `ofMatrix_symm_add`,
  `ofMatrix_symm_neg`, `ofMatrix_symm_sub` and `ofMatrix_symm_smul` do the same for the other
  algebraic operations.
* `CStarMatrix.mul_eq_self_of_conjTranspose_mul_eq`: over a star-ordered ring with proper star,
  a rectangular matrix is supported on its initial projection.
* `CStarMatrix.sum_apply`, `CStarMatrix.toOneByOne_apply`: entries of finite sums and of
  `1 × 1` C⋆-matrices.
* `CStarMatrix.transposeₗ`: the transpose of C⋆-matrices, as a linear map.
* `CStarMatrix.compStarAlgEquiv`: `Matrix.comp` as a star algebra isomorphism
  `M_m(M_n(A)) ≃ M_{m × n}(A)`.
* `CStarMatrix.diagonal`, `CStarMatrix.diagonalStarAlgHom`,
  `CStarMatrix.diagonalNonUnitalStarAlgHom`: diagonal matrices `(n → B) →⋆ₙₐ[R] M_n(B)` and
  the constant-diagonal embedding `b ↦ diag(b, …, b)` of `B` in `M_n(B)`, with
  `CStarMatrix.norm_diagonalNonUnitalStarAlgHom_le`.
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
* `WithCStarModule.norm_equiv_symm_pi_smul`: the vector `(vᵢ a)ᵢ` of the Hilbert `A`-module `Aᵐ`
  has norm `‖v‖ ‖a‖`.
* `CStarMatrix.norm_sum_smul_le`: compressing `x ∈ M_{m,n}(A)` by scalar vectors `v`, `w` gives
  `‖∑ i j, (vᵢ wⱼ*) xᵢⱼ‖ ≤ ‖v‖ ‖x‖ ‖w‖`. The proof tests `x` against the vectors `(vᵢ a)ᵢ` and
  `(wⱼ b)ⱼ` of `Aᵐ` and `Aⁿ`, which bounds `‖a z b*‖` for the compression `z`, and takes `a = z*`,
  `b = z* z`; no unit is needed.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Lemma 4.1.
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

section Basic

variable {n R A : Type*}

/-- Diagonal `CStarMatrix` with diagonal entries `d : n → A`. -/
def diagonal [DecidableEq n] [Zero A] (d : n → A) : CStarMatrix n n A :=
  ofMatrix (Matrix.diagonal d)

@[simp]
theorem ofMatrix_symm_diagonal [DecidableEq n] [Zero A] (d : n → A) :
    ofMatrix.symm (diagonal d) = Matrix.diagonal d := (rfl)

theorem diagonal_apply [DecidableEq n] [Zero A] (d : n → A) (i j : n) :
    diagonal d i j = if i = j then d i else 0 := (rfl)

@[simp]
theorem diagonal_apply_eq [DecidableEq n] [Zero A] (d : n → A) (i : n) :
    diagonal d i i = d i := Matrix.diagonal_apply_eq d i

@[simp]
theorem diagonal_apply_ne [DecidableEq n] [Zero A] (d : n → A) {i j : n} (h : i ≠ j) :
    diagonal d i j = 0 := Matrix.diagonal_apply_ne d h

@[simp]
theorem diagonal_zero [DecidableEq n] [Zero A] :
    diagonal (0 : n → A) = 0 := Matrix.diagonal_zero

@[simp]
theorem diagonal_one [DecidableEq n] [Zero A] [One A] :
    diagonal (1 : n → A) = 1 := Matrix.diagonal_one

theorem diagonal_add [DecidableEq n] [AddZeroClass A] (d₁ d₂ : n → A) :
    diagonal (d₁ + d₂) = diagonal d₁ + diagonal d₂ := (Matrix.diagonal_add d₁ d₂).symm

theorem diagonal_mul [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring A] (d₁ d₂ : n → A) :
    diagonal d₁ * diagonal d₂ = diagonal (fun i ↦ d₁ i * d₂ i) :=
  congrArg ofMatrix (Matrix.diagonal_mul_diagonal d₁ d₂)

@[simp]
theorem star_diagonal [DecidableEq n] [AddMonoid A] [StarAddMonoid A] (d : n → A) :
    star (diagonal d) = diagonal (star d) :=
  congrArg ofMatrix (Matrix.diagonal_conjTranspose d)

/-- Diagonal `⋆`-homomorphism `(n → A) →⋆ₙₐ[R] CStarMatrix n n A`. -/
def diagonalStarAlgHom [Fintype n] [DecidableEq n] [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [StarAddMonoid A] :
    (n → A) →⋆ₙₐ[R] CStarMatrix n n A where
  toFun := diagonal
  map_smul' c d := congrArg ofMatrix (Matrix.diagonal_smul c d)
  map_zero' := diagonal_zero
  map_add' := diagonal_add
  map_mul' d₁ d₂ := (diagonal_mul d₁ d₂).symm
  map_star' d := (star_diagonal d).symm

@[simp]
theorem diagonalStarAlgHom_apply [Fintype n] [DecidableEq n] [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [StarAddMonoid A] (d : n → A) :
    (diagonalStarAlgHom : (n → A) →⋆ₙₐ[R] CStarMatrix n n A) d = diagonal d := (rfl)

theorem diagonalStarAlgHom_injective [Fintype n] [DecidableEq n] [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [StarAddMonoid A] :
    Function.Injective (diagonalStarAlgHom (n := n) (R := R) (A := A)) := fun _ _ h ↦ by
  ext i; simpa using congrArg (fun M : CStarMatrix n n A ↦ M i i) h

end Basic

variable (R n B : Type*) [Fintype n] [DecidableEq n] [Monoid R] [NonUnitalNonAssocSemiring B]
  [StarAddMonoid B] [DistribMulAction R B]

/-- The diagonal embedding `b ↦ diag(b, …, b)` of `B` in `CStarMatrix n n B`, obtained by
precomposing `CStarMatrix.diagonalStarAlgHom` with the constant-function homomorphism. -/
def diagonalNonUnitalStarAlgHom : B →⋆ₙₐ[R] CStarMatrix n n B :=
  (diagonalStarAlgHom (n := n) (R := R) (A := B)).comp
    { toFun := Function.const n
      map_smul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl
      map_mul' _ _ := rfl
      map_star' _ := rfl }

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
lemma ofMatrix_symm_zero {m : Type*} [Zero A] :
    ofMatrix.symm (0 : CStarMatrix m n A) = 0 := (rfl)

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
lemma ofMatrix_symm_neg {m : Type*} [Neg A] (M : CStarMatrix m n A) :
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

/-- The diagonal matrix `diag(a, …, a)` has norm at most `‖a‖`. -/
theorem norm_diagonalNonUnitalStarAlgHom_le [DecidableEq n] (a : A) :
    ‖diagonalNonUnitalStarAlgHom ℂ n A a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le _ a

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
