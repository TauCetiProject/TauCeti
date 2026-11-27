/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Unitization
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Topology.Instances.Matrix
import TauCeti.Algebra.Star.Basic
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.Compression
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Composition
import TauCeti.LinearAlgebra.Trace.Idempotent
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
diagonal embedding `b ↦ diag(b, …, b)`, the matrix units `eᵢⱼ` of `M_n(ℂ)` and the corner
embeddings into block-diagonal matrices.

## Main declarations

* `CStarMatrix.instNonUnitalContinuousFunctionalCalculusReal`: the real continuous functional
  calculus of `CStarMatrix n n A`, which instance search does not find on its own.
* `CStarMatrix.instIsSimpleRing`: square matrices over a simple ring form a simple ring.
* `CStarMatrix.instSeparableSpace`: finite matrices over a separable C⋆-algebra form a separable
  space.
* `CStarMatrix.instModuleFinite`: `CStarMatrix m n A` is a finite module over finite index
  types when `A` is finite, so `CStarMatrix m n ℂ` is finite-dimensional.
* `CStarMatrix.ofMatrix_symm_mul`, `CStarMatrix.ofMatrix_symm_conjTranspose`,
  `CStarMatrix.ofMatrix_symm_star`: reading a C⋆-matrix as an ordinary matrix preserves
  rectangular multiplication and conjugate transpose, and sends `star` to conjugate transpose; the
  companions `CStarMatrix.ofMatrix_symm_zero`, `ofMatrix_symm_one`, `ofMatrix_symm_add`,
  `ofMatrix_symm_neg`, `ofMatrix_symm_sub`, `ofMatrix_symm_smul`, `ofMatrix_symm_sum`,
  `CStarMatrix.ofMatrixL_symm_apply`, `CStarMatrix.trace_ofMatrix_symm_unitary_conj`,
  `CStarMatrix.continuous_trace_ofMatrix_symm`, and
  `CStarMatrix.eq_zero_of_isIdempotentElem_of_trace_eq_zero` do the same for the other algebraic
  operations, `CStarMatrix.ofMatrixL.symm`, and unitary invariance, continuity, and the idempotent
  vanishing criterion of the matrix trace.
* `Matrix.GeneralLinearGroup.toCStarMatrixUnits`: invertible matrices over a unital C⋆-algebra
  `A` as the invertible elements of `CStarMatrix n n A`, an isomorphism of topological groups.
* `Matrix.toCStarMatrixUnitary`: unitary matrices over a unital C⋆-algebra `A` as the unitaries
  of `CStarMatrix n n A`, a homeomorphism.
* `CStarMatrix.isStarProjection_ofMatrix_symm_iff`, `CStarMatrix.isStarProjection_ofMatrix_iff`:
  a C⋆-matrix is a star projection exactly when the underlying matrix is; companions
  `CStarMatrix.isSelfAdjoint_ofMatrix_iff` and `CStarMatrix.ofMatrix_mem_unitary_iff` do the same
  for self-adjoint and unitary matrices.
* `CStarMatrix.ofMatrix_single_mul_ofMatrix_single_same`,
  `CStarMatrix.ofMatrix_single_mul_ofMatrix_single_of_ne`,
  `CStarMatrix.ofMatrix_single_mul_mul_ofMatrix_single`,
  `CStarMatrix.conjTranspose_ofMatrix_single`, `CStarMatrix.star_ofMatrix_single`,
  `CStarMatrix.isIdempotentElem_ofMatrix_single_one`,
  `CStarMatrix.sum_ofMatrix_single_one`, `CStarMatrix.eq_sum_ofMatrix_single`,
  `CStarMatrix.eq_sum_smul_ofMatrix_single_one`, and their `Pi.single` product forms
  `CStarMatrix.piSingle_ofMatrix_single_mul_same`,
  `CStarMatrix.piSingle_ofMatrix_single_mul_of_ne`, `CStarMatrix.star_piSingle_ofMatrix_single`,
  `CStarMatrix.piSingle_one_eq_sum_ofMatrix_single`,
  `CStarMatrix.eq_sum_piSingle_ofMatrix_single`, and
  `CStarMatrix.eq_sum_smul_piSingle_ofMatrix_single_one`: matrix-unit multiplication, adjoint, and
  spanning identities for C⋆-matrices and their products.
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
* `CStarMatrix.piStarAlgEquiv`: a matrix over a product is the family of its components,
  `M_m(Π B_i) ≃ Π M_m(B_i)`, as a star algebra isomorphism.
* `CStarMatrix.diagonalNonUnitalStarAlgHom`: the constant-diagonal embedding `b ↦ diag(b, …, b)`
  of `B` in `M_n(B)`, with `CStarMatrix.norm_diagonalNonUnitalStarAlgHom_le` and
  `CStarMatrix.norm_map_toSpanSingleton_le`: `‖[xᵢⱼ • a]‖ ≤ ‖x‖ ‖a‖` for a scalar matrix `x`.
* `CStarMatrix.blockDiagonalSingle`: the corner embedding of `M_{n i}(B)` as the `i`-th diagonal
  block of `M_{Σ i, n i}(B)`, with `CStarMatrix.sum_blockDiagonalSingle`: a block-diagonal matrix
  is the sum of its corner embeddings.
* `CStarMatrix.blockDiagonalNonUnitalStarAlgHom`: the block-diagonal embedding
  `Π i, M_{n i}(B) → M_{Σ i, n i}(B)`, `x ↦ diag(x_i)`, an injective star homomorphism.
* `CStarMatrix.map_zero_linearMap`, `CStarMatrix.map_add_linearMap`,
  `CStarMatrix.map_smul_linearMap`: applying `0`, `f + g` or `c • f` to every entry.
* `CStarMatrix.isSelfAdjoint_of_forall_isSelfAdjoint_sum`: a matrix all of whose quadratic forms
  are self-adjoint is self-adjoint. This is purely algebraic, and holds over any complex
  star-algebra whose star is proper.
* `CStarMatrix.sum_star_mul_mul_eq_dotProduct_mulVec`: rewriting a quadratic form as a
  dot product with `mulVec`.
* `CStarMatrix.nonneg_iff_forall_sum_nonneg`: the quadratic-form criterion for positivity, with
  `CStarMatrix.ofMatrix_smul_nonneg` (`[pᵢⱼ b]` is positive for positive `[pᵢⱼ]` and `b`) and
  `CStarMatrix.star_left_conjugate_unitization_nonneg` (compressing a positive matrix over `A⁺¹`
  by `e ∈ A` gives a positive matrix over `A`).
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
* `WithCStarModule.norm_sq_eq_sum`: `‖v‖ ^ 2 = ∑ i, ‖vᵢ‖ ^ 2` for `v` in the Hilbert space `ℂᵐ`.
* `WithCStarModule.norm_equiv_symm_sum_smul_le`: multiplying by pairwise orthogonal scalar columns
  of norm at most `1` is a contraction `Aⁿ → Aᵐ` of Hilbert `A`-modules.
* `CStarMatrix.norm_compress_le`: compressing `x ∈ M_{m,n}(A)` by pairwise orthogonal scalar
  vectors of norm at most `1` (`CStarMatrix.compress`) does not increase norms.
* `CStarMatrix.compress_self_nonneg`: compressing a positive matrix by the same scalar vectors on
  both sides gives a positive matrix, `0 ≤ e x e⋆`.
* `CStarMatrix.star_compress_one_mul_self`, `CStarMatrix.compress_one_mul_star_self`: for
  `z = R u⋆ = compress 1 u R` with `R ∈ M_n(A)` and `u ∈ M_n(ℂ)`, `z⋆z = u (R⋆R) u⋆`, and
  `zz⋆ = RR⋆` when `u⋆u = 1`.
* `CStarMatrix.norm_sum_smul_le`: compressing `x ∈ M_{m,n}(A)` by scalar vectors `v`, `w` gives
  `‖∑ i j, (vᵢ wⱼ*) xᵢⱼ‖ ≤ ‖v‖ ‖x‖ ‖w‖`. The proof tests `x` against the vectors `(vᵢ a)ᵢ` and
  `(wⱼ b)ⱼ` of `Aᵐ` and `Aⁿ`, which bounds `‖a z b*‖` for the compression `z`, and takes `a = z*`,
  `b = z* z`; no unit is needed.
* `CStarMatrix.norm_ofMatrix_diagonal`: a diagonal matrix `diag(d₁, …, dₙ)` over a C⋆-algebra has
  norm `maxᵢ ‖dᵢ‖`, the sup norm of `d`; `CStarMatrix.norm_ofMatrix_diagonal_fin_two` is the
  `2 × 2` case `‖diag(a, b)‖ = max ‖a‖ ‖b‖`, and `CStarMatrix.norm_ofMatrix_blockDiagonal'` the
  block-diagonal case `‖diag(x_i)‖ = maxᵢ ‖x_i‖`.

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

section Pi

variable (R m : Type*) {ι : Type*} (B : ι → Type*) [Fintype m] [∀ i, AddCommMonoid (B i)]
  [∀ i, Mul (B i)] [∀ i, Star (B i)] [∀ i, SMul R (B i)]

/-- A matrix over a product is the family of its components: `M_m(Π B_i) ≃ Π M_m(B_i)`, as a
star algebra isomorphism of C⋆-matrices (`Matrix.piRingEquiv` with the star structure). -/
def piStarAlgEquiv : CStarMatrix m m (∀ i, B i) ≃⋆ₐ[R] ∀ i, CStarMatrix m m (B i) where
  toFun M i := M.map (· i)
  invFun f := ofMatrix (Matrix.of fun j l i ↦ f i j l)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' := (Matrix.piRingEquiv (n := m) (β := B)).map_mul
  map_smul' _ _ := rfl
  map_star' M := by
    ext i j l
    simp [CStarMatrix.star_apply]

variable {R m B}

@[simp]
theorem piStarAlgEquiv_apply (M : CStarMatrix m m (∀ i, B i)) (i : ι) (j l : m) :
    piStarAlgEquiv R m B M i j l = M j l i :=
  (rfl)

@[simp]
theorem piStarAlgEquiv_symm_apply (f : ∀ i, CStarMatrix m m (B i)) (j l : m) (i : ι) :
    (piStarAlgEquiv R m B).symm f j l i = f i j l :=
  (rfl)

end Pi

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
lemma ofMatrix_symm_zero {m : Type*} [Zero A] : ofMatrix.symm (0 : CStarMatrix m n A) = 0 := (rfl)

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

/-- Reading the entrywise nonunital star-algebra homomorphism as an ordinary matrix applies
its underlying star-ring homomorphism to each entry. -/
@[simp↓]
lemma ofMatrix_symm_mapₙₐ {B : Type*} [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    (f : A →⋆ₙₐ[R] B) (M : CStarMatrix n n A) :
    ofMatrix.symm (mapₙₐ f M) = (ofMatrix.symm M).map (NonUnitalStarRingHom.ofClass f) :=
  (rfl)

/-- `CStarMatrix.ofMatrixₗ` is `CStarMatrix.ofMatrix`. -/
@[simp]
lemma ofMatrixₗ_apply {m : Type*} [AddCommMonoid A] [Semiring R] [Module R A]
    (M : Matrix m n A) : ofMatrixₗ (R := R) M = ofMatrix M := (rfl)

/-- The inverse of `CStarMatrix.ofMatrixₗ` is the inverse of `CStarMatrix.ofMatrix`. -/
@[simp]
lemma ofMatrixₗ_symm_apply {m : Type*} [AddCommMonoid A] [Semiring R] [Module R A]
    (M : CStarMatrix m n A) : (ofMatrixₗ (R := R)).symm M = ofMatrix.symm M := (rfl)

/-- Reading a finite sum of C⋆-matrices as an ordinary matrix distributes over the sum. -/
@[simp]
lemma ofMatrix_symm_sum {m α : Type*} [AddCommMonoid A] (s : Finset α)
    (f : α → CStarMatrix m n A) :
    ofMatrix.symm (∑ x ∈ s, f x) = ∑ x ∈ s, ofMatrix.symm (f x) := by
  simpa only [ofMatrixₗ_symm_apply] using map_sum (ofMatrixₗ (R := ℕ)).symm f s

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

end Algebraic

section MatrixUnits

variable {n A : Type*}

/-- Multiplying two C⋆-matrix units with matching inner index yields a matrix unit with the product
of their entries. -/
theorem ofMatrix_single_mul_ofMatrix_single_same {l m k : Type*} [Fintype m]
    [DecidableEq l] [DecidableEq m] [DecidableEq k] [NonUnitalNonAssocSemiring A]
    (i : l) (j : m) (p : k) (c d : A) :
    ofMatrix (Matrix.single i j c) * ofMatrix (Matrix.single j p d) =
      ofMatrix (Matrix.single i p (c * d)) :=
  ofMatrix.symm.injective (by simp)

/-- Multiplying two C⋆-matrix units with distinct inner indices yields zero. -/
theorem ofMatrix_single_mul_ofMatrix_single_of_ne {l m k : Type*} [Fintype m]
    [DecidableEq l] [DecidableEq m] [DecidableEq k] [NonUnitalNonAssocSemiring A]
    (i : l) {j j' : m} (h : j ≠ j') (p : k) (c d : A) :
    ofMatrix (Matrix.single i j c) * ofMatrix (Matrix.single j' p d) = 0 :=
  ofMatrix.symm.injective (by simp [h])

/-- Sandwiching a C⋆-matrix between two matrix units extracts the `(i', j')` entry. -/
theorem ofMatrix_single_mul_mul_ofMatrix_single {l m k o : Type*} [Fintype m] [Fintype k]
    [DecidableEq l] [DecidableEq m] [DecidableEq k] [DecidableEq o]
    [NonUnitalNonAssocSemiring A] (i : l) (i' : m) (j' : k) (j : o) (a : A)
    (M : CStarMatrix m k A) (b : A) :
    ofMatrix (Matrix.single i i' a) * M * ofMatrix (Matrix.single j' j b) =
      ofMatrix (Matrix.single i j (a * M i' j' * b)) :=
  ofMatrix.symm.injective (by simp)

/-- Every diagonal unit C⋆-matrix unit `ofMatrix (Matrix.single p p 1)` is idempotent. -/
theorem isIdempotentElem_ofMatrix_single_one [Fintype n] [DecidableEq n] [NonAssocSemiring A]
    (p : n) :
    IsIdempotentElem (ofMatrix (Matrix.single p p (1 : A))) := by
  rw [IsIdempotentElem, ofMatrix_single_mul_ofMatrix_single_same, mul_one]

/-- The conjugate transpose of a C⋆-matrix unit swaps its indices and applies `star` to the
entry. -/
theorem conjTranspose_ofMatrix_single {m : Type*} [DecidableEq m] [DecidableEq n]
    [AddMonoid A] [StarAddMonoid A] (i : m) (j : n) (a : A) :
    (ofMatrix (Matrix.single i j a)).conjTranspose = ofMatrix (Matrix.single j i (star a)) :=
  ofMatrix.symm.injective (by simp)

/-- The star of a square C⋆-matrix unit swaps its indices and applies `star` to the entry. -/
@[simp]
theorem star_ofMatrix_single [DecidableEq n] [AddMonoid A] [StarAddMonoid A]
    (i j : n) (a : A) :
    star (ofMatrix (Matrix.single i j a)) = ofMatrix (Matrix.single j i (star a)) :=
  conjTranspose_ofMatrix_single i j a

/-- The identity C⋆-matrix is the sum of the diagonal unit matrix units. -/
theorem sum_ofMatrix_single_one [Fintype n] [DecidableEq n] [AddCommMonoid A] [One A] :
    ∑ i : n, ofMatrix (Matrix.single i i (1 : A)) = (1 : CStarMatrix n n A) :=
  ofMatrix.symm.injective (by simp [Matrix.sum_single_one])

/-- Every C⋆-matrix expands as the sum of its entrywise matrix units. -/
theorem eq_sum_ofMatrix_single {m : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [AddCommMonoid A] (M : CStarMatrix m n A) :
    M = ∑ i : m, ∑ j : n, ofMatrix (Matrix.single i j (M i j)) :=
  ofMatrix.symm.injective <| by
    simp only [ofMatrix_symm_sum, Equiv.symm_apply_apply]
    exact Matrix.matrix_eq_sum_single (ofMatrix.symm M)

/-- Every C⋆-matrix over a semiring expands as a linear combination of the unit matrix units
`ofMatrix (Matrix.single i j 1)`. -/
theorem eq_sum_smul_ofMatrix_single_one {m : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Semiring A] (M : CStarMatrix m n A) :
    M = ∑ i : m, ∑ j : n, M i j • ofMatrix (Matrix.single i j (1 : A)) := by
  conv_lhs => rw [eq_sum_ofMatrix_single M]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp [smul_eq_mul]

/-- Multiplying two single-block C⋆-matrix units in the same coordinate `i` with matching inner
index `b` yields a single-block matrix unit with the product of their entries. -/
@[simp]
theorem piSingle_ofMatrix_single_mul_same {ι : Type*} [DecidableEq ι] {n : ι → Type*}
    [∀ i, Fintype (n i)] [NonUnitalNonAssocSemiring A] (i : ι) [DecidableEq (n i)]
    (a b c : n i) (x y : A) :
    (Pi.single i (ofMatrix (Matrix.single a b x)) : ∀ i', CStarMatrix (n i') (n i') A) *
      Pi.single i (ofMatrix (Matrix.single b c y)) =
      Pi.single i (ofMatrix (Matrix.single a c (x * y))) := by
  rw [← Pi.single_mul, ofMatrix_single_mul_ofMatrix_single_same]

/-- Multiplying two single-block C⋆-matrix units in the same coordinate `i` with distinct inner
indices yields zero. -/
@[simp]
theorem piSingle_ofMatrix_single_mul_of_ne {ι : Type*} [DecidableEq ι] {n : ι → Type*}
    [∀ i, Fintype (n i)] [NonUnitalNonAssocSemiring A] (i : ι) [DecidableEq (n i)]
    (a : n i) {b b' : n i} (h : b ≠ b') (c : n i) (x y : A) :
    (Pi.single i (ofMatrix (Matrix.single a b x)) : ∀ i', CStarMatrix (n i') (n i') A) *
      Pi.single i (ofMatrix (Matrix.single b' c y)) = 0 := by
  rw [← Pi.single_mul, ofMatrix_single_mul_ofMatrix_single_of_ne a h c x y, Pi.single_zero]

/-- The star of a single-block C⋆-matrix unit swaps its matrix indices and applies `star` to its
entry. -/
theorem star_piSingle_ofMatrix_single {ι : Type*} [DecidableEq ι] {n : ι → Type*}
    [AddMonoid A] [StarAddMonoid A] (i : ι) [DecidableEq (n i)] (p q : n i) (a : A) :
    star (Pi.single i (ofMatrix (Matrix.single p q a)) :
        ∀ i', CStarMatrix (n i') (n i') A) =
      Pi.single i (ofMatrix (Matrix.single q p (star a))) := by
  simp

/-- The `i`-th block identity in a product of C⋆-matrix algebras is the sum of the diagonal unit
single-block matrix units at coordinate `i`. -/
theorem piSingle_one_eq_sum_ofMatrix_single {ι : Type*} [DecidableEq ι] {n : ι → Type*}
    [AddCommMonoid A] [One A] (i : ι) [Fintype (n i)] [DecidableEq (n i)] :
    (Pi.single i (1 : CStarMatrix (n i) (n i) A) : ∀ i', CStarMatrix (n i') (n i') A) =
      ∑ q : n i, Pi.single i (ofMatrix (Matrix.single q q (1 : A))) := by
  rw [← sum_ofMatrix_single_one]
  exact map_sum (AddMonoidHom.single (fun i' ↦ CStarMatrix (n i') (n i') A) i) _ _

/-- Every element of a finite product of C⋆-matrix algebras expands as a sum of single-block matrix
units. -/
theorem eq_sum_piSingle_ofMatrix_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] [AddCommMonoid A]
    (x : ∀ i, CStarMatrix (n i) (n i) A) :
    x = ∑ i : ι, ∑ p : n i, ∑ q : n i,
      Pi.single i (ofMatrix (Matrix.single p q (x i p q))) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [← AddMonoidHom.single_apply (f := fun i' ↦ CStarMatrix (n i') (n i') A)]
  conv_lhs => rw [eq_sum_ofMatrix_single (x i)]
  simp only [map_sum]

/-- Every element of a finite product of C⋆-matrix algebras over a semiring expands as a linear
combination of the unit single-block matrix units
`Pi.single i (ofMatrix (Matrix.single p q 1))`. -/
theorem eq_sum_smul_piSingle_ofMatrix_single_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] [Semiring A]
    (x : ∀ i, CStarMatrix (n i) (n i) A) :
    x = ∑ i : ι, ∑ p : n i, ∑ q : n i,
      x i p q • (Pi.single i (ofMatrix (Matrix.single p q (1 : A))) :
        ∀ i', CStarMatrix (n i') (n i') A) := by
  conv_lhs => rw [eq_sum_piSingle_ofMatrix_single x]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun p _ ↦
    Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← Pi.single_smul, smul_of, Matrix.smul_single, smul_eq_mul, mul_one]

end MatrixUnits

section BlockDiagonal

variable {ι : Type*} [DecidableEq ι] {n : ι → Type*} [∀ i, Fintype (n i)]

section NonUnital

variable {R B : Type*} [Monoid R] [NonUnitalNonAssocSemiring B] [StarAddMonoid B]
  [DistribMulAction R B]

variable (R B) in
/-- The corner embedding `x ↦ diag(0, …, x, …, 0)` of `CStarMatrix (n i) (n i) B` as the `i`-th
diagonal block of `CStarMatrix (Σ i, n i) (Σ i, n i) B`, as a non-unital star algebra
homomorphism. -/
def blockDiagonalSingle [Fintype ι] (i : ι) :
    CStarMatrix (n i) (n i) B →⋆ₙₐ[R] CStarMatrix (Σ i, n i) (Σ i, n i) B where
  toFun x := ofMatrix (Matrix.blockDiagonal' (Pi.single i (ofMatrix.symm x)))
  map_smul' c x := ofMatrix.symm.injective <| by
    simp [Pi.single_smul, Matrix.blockDiagonal'_smul]
  map_zero' := ofMatrix.symm.injective <| by simp
  map_add' x y := ofMatrix.symm.injective <| by simp [Pi.single_add, Matrix.blockDiagonal'_add]
  map_mul' x y := ofMatrix.symm.injective <| by
    simp only [Equiv.symm_apply_apply, ofMatrix_symm_mul, ← Matrix.blockDiagonal'_mul]
    exact congrArg _ (Pi.single_mul i _ _)
  map_star' x := ofMatrix.symm.injective <| by
    simp only [Equiv.symm_apply_apply, ofMatrix_symm_star, Matrix.blockDiagonal'_conjTranspose]
    congr 1
    ext j : 1
    by_cases h : j = i
    · subst h; simp
    · simp [h]

/-- The corner embedding places `x` as the block `i` of a block-diagonal matrix. -/
theorem blockDiagonalSingle_apply [Fintype ι] (i : ι) (x : CStarMatrix (n i) (n i) B) :
    blockDiagonalSingle R B i x =
      ofMatrix (Matrix.blockDiagonal' (Pi.single i (ofMatrix.symm x))) :=
  (rfl)

/-- The block `i` of the corner embedding at `i` is `x`. -/
@[simp]
theorem blockDiagonalSingle_apply_same [Fintype ι] (i : ι) (x : CStarMatrix (n i) (n i) B)
    (j k : n i) : blockDiagonalSingle R B i x ⟨i, j⟩ ⟨i, k⟩ = x j k := by
  simp [blockDiagonalSingle_apply, ofMatrix_apply, Matrix.blockDiagonal'_apply_eq]

/-- The corner embedding at `i` vanishes on the diagonal blocks `j ≠ i`. -/
@[simp]
theorem blockDiagonalSingle_apply_diag_of_ne [Fintype ι] {i j : ι} (h : j ≠ i)
    (x : CStarMatrix (n i) (n i) B) (p q : n j) :
    blockDiagonalSingle R B i x ⟨j, p⟩ ⟨j, q⟩ = 0 := by
  simp [blockDiagonalSingle_apply, ofMatrix_apply, Matrix.blockDiagonal'_apply_eq, h]

/-- The corner embedding vanishes off the diagonal blocks. -/
theorem blockDiagonalSingle_apply_ne [Fintype ι] (i : ι) (x : CStarMatrix (n i) (n i) B)
    {j j' : ι} (p : n j) (q : n j') (h : j ≠ j') :
    blockDiagonalSingle R B i x ⟨j, p⟩ ⟨j', q⟩ = 0 := by
  rw [blockDiagonalSingle_apply, ofMatrix_apply, Matrix.blockDiagonal'_apply_ne _ p q h]

/-- Corner embeddings at distinct blocks are orthogonal. -/
theorem blockDiagonalSingle_mul_of_ne [Fintype ι] {i j : ι} (h : i ≠ j)
    (x : CStarMatrix (n i) (n i) B) (y : CStarMatrix (n j) (n j) B) :
    blockDiagonalSingle R B i x * blockDiagonalSingle R B j y = 0 := by
  apply ofMatrix.symm.injective
  rw [blockDiagonalSingle_apply, blockDiagonalSingle_apply, ofMatrix_symm_mul, ofMatrix_symm_zero,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← Matrix.blockDiagonal'_mul,
    ← Matrix.blockDiagonal'_zero]
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk; simp [h]
  · simp [hk]

/-- A block-diagonal matrix is the sum of its corner embeddings. -/
theorem sum_blockDiagonalSingle [Fintype ι] (x : ∀ i, CStarMatrix (n i) (n i) B) :
    ∑ i, blockDiagonalSingle R B i (x i) =
      ofMatrix (Matrix.blockDiagonal' fun i => ofMatrix.symm (x i)) := by
  rw [← Finset.univ_sum_single fun i => ofMatrix.symm (x i)]
  -- `ofMatrix` is the identity equivalence, so this is additivity of `Matrix.blockDiagonal'`.
  exact (map_sum (Matrix.blockDiagonal'AddMonoidHom n n B) _ _).symm

variable (R B) in
/-- The **block-diagonal embedding** `x ↦ diag(x_i)` of `Π i, CStarMatrix (n i) (n i) B` into
`CStarMatrix (Σ i, n i) (Σ i, n i) B`, as a non-unital star algebra homomorphism: the
C⋆-matrix form of `Matrix.blockDiagonal'RingHom`. -/
def blockDiagonalNonUnitalStarAlgHom [Fintype ι] :
    (Π i, CStarMatrix (n i) (n i) B) →⋆ₙₐ[R] CStarMatrix (Σ i, n i) (Σ i, n i) B where
  toFun x := ofMatrix (Matrix.blockDiagonal' fun i => ofMatrix.symm (x i))
  -- each law is the corresponding law of `Matrix.blockDiagonal'`, applied blockwise
  map_smul' c x := ofMatrix.symm.injective <| by
    simp only [Pi.smul_apply, ofMatrix_symm_smul, Equiv.symm_apply_apply, MonoidHom.id_apply,
      ← Pi.smul_def, Matrix.blockDiagonal'_smul]
  map_zero' := ofMatrix.symm.injective <| by
    simp only [Pi.zero_apply, ofMatrix_symm_zero, Equiv.symm_apply_apply, ← Pi.zero_def,
      Matrix.blockDiagonal'_zero]
  map_add' x y := ofMatrix.symm.injective <| by
    simp only [Pi.add_apply, ofMatrix_symm_add, Equiv.symm_apply_apply, ← Pi.add_def,
      Matrix.blockDiagonal'_add]
  map_mul' x y := ofMatrix.symm.injective <| by
    simp only [Pi.mul_apply, ofMatrix_symm_mul, Equiv.symm_apply_apply, ← Pi.mul_def]
    -- `exact`, not `simp`: the blockwise products come from the rectangular `Matrix` product
    exact Matrix.blockDiagonal'_mul _ _
  map_star' x := ofMatrix.symm.injective <| by
    simp only [Pi.star_apply, ofMatrix_symm_star, Equiv.symm_apply_apply,
      Matrix.blockDiagonal'_conjTranspose]

/-- The block-diagonal embedding sends `x` to the block-diagonal matrix with blocks `x i`. -/
@[simp]
theorem blockDiagonalNonUnitalStarAlgHom_apply [Fintype ι] (x : Π i, CStarMatrix (n i) (n i) B) :
    blockDiagonalNonUnitalStarAlgHom R B x =
      ofMatrix (Matrix.blockDiagonal' fun i => ofMatrix.symm (x i)) :=
  (rfl)

/-- The block-diagonal embedding is injective. -/
theorem blockDiagonalNonUnitalStarAlgHom_injective [Fintype ι] :
    Function.Injective (blockDiagonalNonUnitalStarAlgHom R B (n := n)) := fun _ _ h =>
  funext fun i => ofMatrix.symm.injective <|
    congrFun (Matrix.blockDiagonal'_injective (ofMatrix.injective h)) i

end NonUnital

/-- The identity matrix is the sum of the corner embeddings of the identity matrices. -/
theorem sum_blockDiagonalSingle_one [Fintype ι] [∀ i, DecidableEq (n i)] (R : Type*)
    {B : Type*} [Monoid R] [NonAssocSemiring B] [StarAddMonoid B] [DistribMulAction R B] :
    ∑ i, blockDiagonalSingle R B i (1 : CStarMatrix (n i) (n i) B) = 1 := by
  apply ofMatrix.symm.injective
  simp only [sum_blockDiagonalSingle, Equiv.symm_apply_apply, ofMatrix_symm_one]
  rw [← Pi.one_def, Matrix.blockDiagonal'_one]

end BlockDiagonal

/-- Square matrices over a simple ring form a simple ring: their two-sided ideals are the matrices
over the two-sided ideals of the coefficient ring. -/
instance instIsSimpleRing {n A : Type*} [Fintype n] [Nonempty n] [Ring A] [IsSimpleRing A] :
    IsSimpleRing (CStarMatrix n n A) :=
  inferInstanceAs (IsSimpleRing (Matrix n n A))

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

open scoped ComplexOrder in
/-- Compressing a positive matrix `[λᵢⱼ + aᵢⱼ]` over the unitization `A⁺¹` by `e ∈ A` gives the
positive matrix `[e⋆ aᵢⱼ e + λᵢⱼ e⋆ e]` over `A`: it is the conjugate `diag(e)⋆ M diag(e)`, whose
entries lie in `A`. -/
theorem star_left_conjugate_unitization_nonneg {M : CStarMatrix n n (Unitization ℂ A)}
    (hM : 0 ≤ M) (e : A) : 0 ≤ ofMatrix
      (Matrix.of fun i j => star e * (M i j).snd * e + (M i j).fst • (star e * e)) := by
  refine nonneg_iff_forall_sum_nonneg.mpr fun z => ?_
  have h := nonneg_iff_forall_sum_nonneg.mp hM fun i => ((e * z i : A) : Unitization ℂ A)
  rw [← Unitization.inr_nonneg_iff ℂ]
  convert h using 1
  simp only [← Unitization.inrNonUnitalStarAlgHom_apply ℂ, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ext <;> simp [mul_assoc, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, add_comm]

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

/-- For a vector `v` of the Hilbert space `ℂᵐ`, `‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2`. -/
theorem _root_.WithCStarModule.norm_sq_eq_sum (v : C⋆ᵐᵒᵈ(ℂ, m → ℂ)) :
    ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [pi_norm_sq]
  simp only [inner_def, RCLike.star_def, RCLike.mul_conj]
  norm_cast
  exact Real.norm_of_nonneg (by positivity)

/-- The vector `(∑ t, e t i • a t)ᵢ` of the Hilbert `A`-module `Aᵐ`, for pairwise orthogonal
scalar vectors `e t ∈ ℂᵐ` of norm at most `1`, has norm at most `‖a‖`: the map `a ↦ (∑ t, e t i •
a t)ᵢ` is a contraction `Aⁿ → Aᵐ`. -/
theorem _root_.WithCStarModule.norm_equiv_symm_sum_smul_le {e : n → m → ℂ}
    (he : ∀ t t', t ≠ t' → ∑ i, e t i * star (e t' i) = 0) (he₁ : ∀ t, ∑ i, ‖e t i‖ ^ 2 ≤ 1)
    (a : C⋆ᵐᵒᵈ(A, n → A)) :
    ‖(equiv A (m → A)).symm fun i => ∑ t, e t i • a t‖ ≤ ‖a‖ := by
  have key : ∑ i, (∑ t, e t i • a t) * star (∑ t, e t i • a t) =
      ∑ t, (∑ i, ‖e t i‖ ^ 2) • (a t * star (a t)) := by
    simp only [star_sum, star_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single t]
    · rw [← Finset.sum_smul, ← Complex.coe_smul]
      congr 1
      push_cast
      exact Finset.sum_congr rfl fun i _ => by simp [RCLike.star_def, RCLike.mul_conj]
    · exact fun t' _ h => by rw [← Finset.sum_smul, he t' t h, zero_smul]
    · simp
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, pi_norm_sq, pi_norm_sq]
  simp only [equiv_symm_pi_apply, inner_def]
  rw [key]
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (Finset.sum_le_sum fun t _ => smul_le_of_le_one_left (mul_star_self_nonneg _) (he₁ t))
    (Finset.sum_nonneg fun t _ => smul_nonneg (by positivity) (mul_star_self_nonneg _))

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

/-- The compression `[∑ k l, (e t k * star (f t' l)) • x k l]_{t t'}` of `x ∈ M_{m,n}(A)` to
`M_{ι,ι'}(A)` by the scalar vectors `e t ∈ ℂᵐ` and `f t' ∈ ℂⁿ`. -/
def compress {ι ι' : Type*} (e : ι → m → ℂ) (f : ι' → n → ℂ) (x : CStarMatrix m n A) :
    CStarMatrix ι ι' A :=
  ofMatrix (Matrix.of fun t t' => ∑ k, ∑ l, (e t k * star (f t' l)) • x k l)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp]
theorem compress_apply {ι ι' : Type*} (e : ι → m → ℂ) (f : ι' → n → ℂ) (x : CStarMatrix m n A)
    (t : ι) (t' : ι') : compress e f x t t' = ∑ k, ∑ l, (e t k * star (f t' l)) • x k l :=
  (rfl)

omit [PartialOrder A] [StarOrderedRing A] in
/-- Compressing by the standard basis on the left multiplies by `f⋆` on the right:
`compress 1 f x = x f⋆`. -/
theorem compress_one_apply [DecidableEq m] {ι' : Type*} (f : ι' → n → ℂ) (x : CStarMatrix m n A)
    (k : m) (t' : ι') : compress (1 : CStarMatrix m m ℂ) f x k t' = ∑ l, star (f t' l) • x k l := by
  simp [compress_apply (1 : CStarMatrix m m ℂ) f, one_apply, ite_smul]

omit [PartialOrder A] [StarOrderedRing A] in
/-- For `R ∈ M_n(A)` and `u ∈ M_n(ℂ)`, the product `z = R u⋆ = compress 1 u R` satisfies
`z⋆z = u (R⋆R) u⋆ = compress u u (R⋆R)`. -/
theorem star_compress_one_mul_self [DecidableEq n] (u : CStarMatrix n n ℂ)
    (R : CStarMatrix n n A) :
    star (compress (1 : CStarMatrix n n ℂ) u R) * compress (1 : CStarMatrix n n ℂ) u R =
      compress u u (star R * R) := by
  ext t t'
  simp only [mul_apply, star_apply, compress_one_apply u, compress_apply u u, star_sum, star_smul,
    star_star, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, Finset.smul_sum]
  -- Reorder `∑ k, ∑ l, ∑ j` to `∑ j, ∑ l, ∑ k`.
  exact Finset.sum_comm_cycle.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)

omit [PartialOrder A] [StarOrderedRing A] in
/-- For `R ∈ M_n(A)` and `u ∈ M_n(ℂ)` with `u⋆u = 1`, the product `z = R u⋆ = compress 1 u R`
satisfies `zz⋆ = RR⋆`. -/
theorem compress_one_mul_star_self [DecidableEq n] {u : CStarMatrix n n ℂ} (hu : star u * u = 1)
    (R : CStarMatrix n n A) :
    compress (1 : CStarMatrix n n ℂ) u R * star (compress (1 : CStarMatrix n n ℂ) u R) =
      R * star R := by
  have h (k l : n) : ∑ t, star (u t k) * u t l = if k = l then 1 else 0 := by
    simpa [mul_apply, star_apply, one_apply] using CStarMatrix.ext_iff.mpr hu k l
  ext i j
  simp only [mul_apply, star_apply, compress_one_apply u, star_sum, star_smul, star_star,
    Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  -- Reorder `∑ t, ∑ k, ∑ l` to `∑ l, ∑ k, ∑ t` and use `u⋆u = 1`.
  rw [← Finset.sum_comm_cycle]
  simp_rw [← Finset.sum_smul, h, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- **Compression preserves positivity**: `0 ≤ x` gives `0 ≤ compress e e x` for any scalar
vectors `e t ∈ ℂⁿ`, i.e. `0 ≤ e x e⋆`. -/
theorem compress_self_nonneg {ι : Type*} [Fintype ι] (e : ι → n → ℂ) {x : CStarMatrix n n A}
    (hx : 0 ≤ x) : 0 ≤ compress e e x := by
  refine nonneg_iff_forall_sum_nonneg.mpr fun y => ?_
  -- The quadratic form at `y` is that of `x` at `w l = ∑ t, star (e t l) • y t`.
  convert nonneg_iff_forall_sum_nonneg.mp hx fun l => ∑ t, star (e t l) • y t using 1
  simp only [compress_apply, star_sum, star_smul, star_star, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul, ← Fintype.sum_prod_type']
  -- reindex `(t, t', k, l) ↦ (k, l, t', t)`
  exact Fintype.sum_equiv
    ⟨fun p => (p.2.2.1, p.2.2.2, p.2.1, p.1), fun q => (q.2.2.2, q.2.2.1, q.1, q.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => by
    dsimp only [Equiv.coe_fn_mk]
    rw [mul_comm (e _ _)]

/-- Compressing a matrix over a C⋆-algebra by pairwise orthogonal scalar vectors of norm at most
`1` does not increase norms: `‖compress e f x‖ ≤ ‖x‖`. -/
theorem norm_compress_le {ι ι' : Type*} [Fintype ι] [Fintype ι'] {e : ι → m → ℂ}
    {f : ι' → n → ℂ} (he : ∀ t t', t ≠ t' → ∑ k, e t k * star (e t' k) = 0)
    (he₁ : ∀ t, ∑ k, ‖e t k‖ ^ 2 ≤ 1) (hf : ∀ t t', t ≠ t' → ∑ l, f t l * star (f t' l) = 0)
    (hf₁ : ∀ t, ∑ l, ‖f t l‖ ^ 2 ≤ 1) (x : CStarMatrix m n A) : ‖compress e f x‖ ≤ ‖x‖ := by
  refine norm_le_of_forall_inner_le (C := ‖x‖₊) fun a b => ?_
  let a' : C⋆ᵐᵒᵈ(A, m → A) := (equiv A (m → A)).symm fun k => ∑ t, e t k • a t
  let b' : C⋆ᵐᵒᵈ(A, n → A) := (equiv A (n → A)).symm fun l => ∑ t, f t l • b t
  have h : ⟪b, toCLM (compress e f x) a⟫_A = ⟪b', toCLM x a'⟫_A := by
    simp only [pi_inner, toCLM_apply_eq_sum, equiv_symm_pi_apply, inner_def,
      compress_apply, a', b', star_sum, star_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
      mul_smul_comm, Finset.smul_sum, smul_smul]
    simp only [← Fintype.sum_prod_type']
    -- reindex `(t', t, k, l) ↦ (l, t', k, t)`
    exact Fintype.sum_equiv
      ⟨fun p => (p.2.2.2, p.1, p.2.2.1, p.2.1), fun p => (p.2.1, p.2.2.2, p.2.2.1, p.1),
        fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => by
      dsimp only [Equiv.coe_fn_mk]
      rw [mul_comm (e _ _)]
  rw [h]
  calc ‖⟪b', toCLM x a'⟫_A‖ ≤ ‖b'‖ * ‖toCLM x a'‖ := norm_inner_le _
    _ ≤ ‖b‖ * (‖x‖ * ‖a‖) := by
      gcongr
      · exact norm_equiv_symm_sum_smul_le hf hf₁ b
      · exact ((toCLM x).le_opNorm a').trans
          (mul_le_mul_of_nonneg_left (norm_equiv_symm_sum_smul_le he he₁ a) (norm_nonneg _))
    _ = _ := by simp only [coe_nnNorm]; ring

end Compression

section DiagonalNorm

open WithCStarModule CStarModule

variable {n A : Type*} [Fintype n] [DecidableEq n] [NonUnitalCStarAlgebra A] [PartialOrder A]
  [StarOrderedRing A]

/-- A diagonal matrix over a C⋆-algebra has norm the largest norm of its diagonal entries: the
diagonal matrices form a copy of `Aⁿ` with the sup norm. -/
theorem norm_ofMatrix_diagonal (d : n → A) : ‖ofMatrix (Matrix.diagonal d)‖ = ‖d‖ := by
  refine le_antisymm ?_ ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · rw [norm_def]
    refine (toCLM (ofMatrix (Matrix.diagonal d))).opNorm_le_bound (norm_nonneg d) fun v => ?_
    have hv : toCLM (ofMatrix (Matrix.diagonal d)) v =
        (equiv A (n → A)).symm fun j => v j * d j := by
      simp [toCLM_apply_eq_sum, Matrix.diagonal_apply]
    rw [hv, ← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, norm_sq_eq A (x := v),
      norm_sq_eq A (x := (equiv A (n → A)).symm _), pi_inner, pi_inner]
    simp only [equiv_symm_pi_apply, inner_def]
    -- Each term `vⱼ dⱼ (vⱼ dⱼ)⋆` is the conjugate of `dⱼ dⱼ⋆ ≤ ‖d‖²` by `vⱼ`.
    calc ‖∑ j, v j * d j * star (v j * d j)‖ ≤ ‖∑ j, ‖d‖ ^ 2 • (v j * star (v j))‖ := by
          refine CStarAlgebra.norm_le_norm_of_le_of_nonneg (Finset.sum_le_sum fun j _ => ?_)
            (Finset.sum_nonneg fun j _ => mul_star_self_nonneg _)
          calc v j * d j * star (v j * d j) = v j * (d j * star (d j)) * star (v j) := by
                simp [star_mul, mul_assoc]
            _ ≤ ‖d j * star (d j)‖ • (v j * star (v j)) :=
                CStarAlgebra.star_right_conjugate_le_norm_smul _ _
            _ ≤ ‖d‖ ^ 2 • (v j * star (v j)) := by
                refine smul_le_smul_of_nonneg_right ?_ (mul_star_self_nonneg _)
                rw [CStarRing.norm_self_mul_star, ← sq]
                exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm d j) 2
      _ = ‖d‖ ^ 2 * ‖∑ j, v j * star (v j)‖ := by
          rw [← Finset.smul_sum, norm_smul, Real.norm_of_nonneg (by positivity)]
  · simpa using norm_entry_le_norm (M := ofMatrix (Matrix.diagonal d)) (i := i) (j := i)

/-- A `2 × 2` diagonal matrix `diag(a, b)` over a C⋆-algebra has norm `max ‖a‖ ‖b‖`. -/
theorem norm_ofMatrix_diagonal_fin_two (a b : A) :
    ‖ofMatrix (Matrix.diagonal ![a, b])‖ = max ‖a‖ ‖b‖ := by
  rw [norm_ofMatrix_diagonal]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_)
    (max_le (norm_le_pi_norm ![a, b] 0) (norm_le_pi_norm ![a, b] 1))
  fin_cases i <;> simp

/-- A block-diagonal matrix over a C⋆-algebra has norm the largest norm of its diagonal blocks:
`‖diag(x_i)‖ = maxᵢ ‖x_i‖`, the sup norm of `x`, since the block-diagonal embedding is an injective
star homomorphism of C⋆-algebras. -/
theorem norm_ofMatrix_blockDiagonal' {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → Type*}
    [∀ i, Fintype (n i)] (x : Π i, CStarMatrix (n i) (n i) A) :
    ‖ofMatrix (Matrix.blockDiagonal' fun i => ofMatrix.symm (x i))‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map _ (blockDiagonalNonUnitalStarAlgHom_injective (R := ℂ) (B := A)) x

end DiagonalNorm

/-- The inverse of `CStarMatrix.ofMatrixL` agrees with `CStarMatrix.ofMatrix.symm`. -/
@[simp]
lemma ofMatrixL_symm_apply {m n A : Type*} [NonUnitalCStarAlgebra A] (M : CStarMatrix m n A) :
    ofMatrixL.symm M = ofMatrix.symm M :=
  ofMatrixL.symm_apply_eq.mpr <| by rw [← ofMatrix_eq_ofMatrixL, Equiv.apply_symm_apply]

/-- The matrix trace on `CStarMatrix n n A` is invariant under unitary conjugation. -/
theorem trace_ofMatrix_symm_unitary_conj {n A : Type*} [Fintype n] [DecidableEq n]
    [CommSemiring A] [StarRing A] {u : CStarMatrix n n A}
    (hu : u ∈ unitary (CStarMatrix n n A)) (x : CStarMatrix n n A) :
    Matrix.trace (ofMatrix.symm (u * x * star u)) = Matrix.trace (ofMatrix.symm x) := by
  rw [ofMatrix_symm_mul, ofMatrix_symm_mul, ofMatrix_symm_star, Matrix.trace_mul_cycle,
    ← ofMatrix_symm_star, ← ofMatrix_symm_mul, Unitary.star_mul_self_of_mem hu,
    ofMatrix_symm_one, Matrix.one_mul]

/-- The matrix trace `x ↦ Matrix.trace (ofMatrix.symm x)` on `CStarMatrix n n A` is continuous. -/
@[continuity, fun_prop]
theorem continuous_trace_ofMatrix_symm {n A : Type*} [Fintype n] [NonUnitalCStarAlgebra A] :
    Continuous fun x : CStarMatrix n n A ↦ Matrix.trace (ofMatrix.symm x) := by
  simpa only [← ofMatrixL_symm_apply] using ofMatrixL.symm.continuous.matrix_trace

/-- Over a field of characteristic zero, an idempotent C⋆-matrix of trace zero is zero. -/
theorem eq_zero_of_isIdempotentElem_of_trace_eq_zero {n K : Type*} [Fintype n] [Field K]
    [CharZero K] {P : CStarMatrix n n K} (hP : IsIdempotentElem P)
    (htr : Matrix.trace (ofMatrix.symm P) = 0) : P = 0 := by
  apply ofMatrix.symm.injective
  rw [ofMatrix_symm_zero]
  refine Matrix.IsIdempotentElem.eq_zero_of_trace_eq_zero ?_ htr
  rw [IsIdempotentElem, ← ofMatrix_symm_mul, hP.eq]

end CStarMatrix

namespace Matrix.GeneralLinearGroup

variable {n A : Type*} [Fintype n] [DecidableEq n] [CStarAlgebra A]

/-- Invertible matrices over a unital C⋆-algebra `A` are the invertible elements of the
C⋆-algebra `CStarMatrix n n A`, as an isomorphism of topological groups. -/
noncomputable def toCStarMatrixUnits : GL n A ≃ₜ* (CStarMatrix n n A)ˣ :=
  Units.mapContinuousMulEquiv
    { CStarMatrix.ofMatrixRingEquiv.toMulEquiv with
      continuous_toFun := CStarMatrix.ofMatrixL.continuous
      continuous_invFun := CStarMatrix.ofMatrixL.symm.continuous }

@[simp]
theorem coe_toCStarMatrixUnits (u : GL n A) :
    (toCStarMatrixUnits u : CStarMatrix n n A) = CStarMatrix.ofMatrix (u : Matrix n n A) :=
  (rfl)

@[simp]
theorem coe_toCStarMatrixUnits_symm (u : (CStarMatrix n n A)ˣ) :
    (toCStarMatrixUnits.symm u : Matrix n n A) =
      CStarMatrix.ofMatrix.symm (u : CStarMatrix n n A) :=
  (rfl)

end Matrix.GeneralLinearGroup

namespace Matrix

variable {n A : Type*} [Fintype n] [DecidableEq n] [CStarAlgebra A]

/-- Unitary matrices over a unital C⋆-algebra `A` are the unitaries of the C⋆-algebra
`CStarMatrix n n A`, as a homeomorphism. -/
noncomputable def toCStarMatrixUnitary : unitary (Matrix n n A) ≃ₜ unitary (CStarMatrix n n A) where
  toFun w := ⟨CStarMatrix.ofMatrix w, CStarMatrix.ofMatrix_mem_unitary_iff.2 w.prop⟩
  invFun w := ⟨CStarMatrix.ofMatrix.symm w, CStarMatrix.ofMatrix_symm_mem_unitary_iff.2 w.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (CStarMatrix.ofMatrixL.continuous.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun :=
    (CStarMatrix.ofMatrixL.symm.continuous.comp continuous_subtypeVal).subtype_mk _

/-- The C⋆-matrix underlying the image of a unitary matrix is the matrix itself. -/
@[simp]
theorem coe_toCStarMatrixUnitary (w : unitary (Matrix n n A)) :
    (toCStarMatrixUnitary w : CStarMatrix n n A) = CStarMatrix.ofMatrix (w : Matrix n n A) :=
  (rfl)

/-- The matrix underlying the preimage of a unitary C⋆-matrix is the C⋆-matrix itself. -/
@[simp]
theorem coe_toCStarMatrixUnitary_symm (w : unitary (CStarMatrix n n A)) :
    (toCStarMatrixUnitary.symm w : Matrix n n A) =
      CStarMatrix.ofMatrix.symm (w : CStarMatrix n n A) :=
  (rfl)

end Matrix
