/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.LinearAlgebra.Matrix.Reindex
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse
import TauCeti.Order.Preorder.Finite

/-!
# Triangular matrices

Mathlib's `Matrix.BlockTriangular` API computes determinants and inverses of triangular
matrices, but not their individual diagonal entries. This file supplies the facts that
consumers keep needing: on the diagonal, a product of triangular matrices multiplies
entrywise, because `∑ k, A i k * B k i` has a single surviving term — and consequences of
that, such as the diagonal of an inverse. It also proves uniqueness of a lower-triangular Gram
factor with positive diagonal, defines upper-unitriangular matrices, and proves that strictly
upper-triangular matrices are nilpotent, as are, more generally, matrices vanishing wherever a
ranking of the indices (not necessarily injective) fails to increase strictly. A nonzero
submodule invariant under a family of strictly upper-triangular matrices contains a nonzero vector
annihilated by the whole family.

The diagonal results are stated directly for `Matrix.IsUpperTriangular` and
`Matrix.IsLowerTriangular` rather than through membership in the Borel subalgebra, since there is
no Lie theory in them. It is
`Matrix.mul_apply_diag_of_isUpperTriangular` that `TauCeti.Algebra.Lie.GeneralLinear.Borel`
consumes in that form, and all of them are available to modules with no business importing
Lie-algebra theory.

## Main results

* `Matrix.BlockTriangular.det_eq_prod_diag` — a matrix that is block triangular for an injective
  ranking of its indices has the product of its diagonal entries as determinant.
* `Matrix.mul_apply_diag_of_isUpperTriangular` — the diagonal of a product of upper-triangular
  matrices is the pointwise product of the diagonals.
* `Matrix.mul_apply_diag_of_isLowerTriangular` — the corresponding formula for lower-triangular
  matrices.
* `Matrix.IsLowerTriangular.eq_one_of_mul_transpose_self_eq_one` — a lower-triangular orthogonal
  matrix with nonnegative diagonal is the identity.
* `Matrix.IsLowerTriangular.eq_of_mul_transpose_self_eq` — lower-triangular matrices with positive
  diagonal are determined by their product with their transpose.
* `Matrix.IsLowerTriangular.submatrix_castLE_mul_transpose` — a leading principal submatrix of a
  lower-triangular Gram matrix is the Gram matrix of the corresponding submatrix.
* `Matrix.mul_apply_eq_sum_Iic_of_isLowerTriangular_of_isUpperTriangular` — an entry of a product
  of lower- and upper-triangular matrices is a sum over the columns at most both indices.
* `Matrix.IsLowerTriangular.mul_transpose_apply_eq_sum_Iic` — the Gram-matrix specialization.
* `Matrix.IsUpperTriangular.submatrix_mul` and `submatrix_pow` — restriction to order-connected
  index sets preserves multiplication and powers.
* `Matrix.pow_apply_diag_of_isUpperTriangular` — the diagonal of a power of an upper-triangular
  matrix is the corresponding power of the diagonal entry.
* `Matrix.isUpperUnitriangular_geom_sum_of_isUpperTriangular_of_diag_eq_zero` — the geometric
  series in a strictly upper-triangular matrix is upper unitriangular, for any truncation that is
  positive whenever the index type is inhabited, and
  `Matrix.isUpperUnitriangular_geom_sum_card_of_isUpperTriangular_of_diag_eq_zero` for the
  truncation at the size of the matrix.
* `Matrix.inv_apply_diag_mul_of_isUpperTriangular` — on the diagonal, the inverse inverts
  entrywise: `M⁻¹ i i * M i i = 1`.
* `Matrix.inv_apply_diag_of_isUpperTriangular` — where an upper-triangular matrix carries a `1`
  on the diagonal, so does its inverse.
* `Matrix.inv_apply_diag_mul_of_isLowerTriangular` and
  `Matrix.inv_apply_diag_of_isLowerTriangular` — the corresponding facts for lower-triangular
  matrices.
* `Matrix.IsUpperUnitriangular` — an upper-triangular matrix with diagonal one.
* `Matrix.IsUpperUnitriangular.ext` — upper-unitriangular matrices are determined by their
  entries strictly above the diagonal.
* `Matrix.IsUpperUnitriangular.submatrix` — selecting rows and columns by a strictly increasing
  map preserves upper unitriangularity.
* `Matrix.isUnit_det_of_isUpperTriangular_map` — a matrix whose image under a local ring
  homomorphism is upper triangular with unit diagonal has a unit determinant.
* `Matrix.exists_isUpperUnitriangular_mul_apply` — subtracting a combination of later rows
  from each row is left multiplication by an upper-unitriangular matrix.
* `Matrix.IsUpperUnitriangular.det_eq_one` — an upper-unitriangular matrix has determinant one.
* `Matrix.IsUpperUnitriangular.diagonal_mul_mul_diagonal` — conjugation by an invertible diagonal
  matrix preserves upper-unitriangular matrices.
* `Matrix.IsUpperUnitriangular.mul` and `Matrix.IsUpperUnitriangular.pow` — upper-unitriangular
  matrices are closed under products and natural powers.
* `Matrix.IsUpperUnitriangular.mul_single_zero_last`,
  `Matrix.IsUpperUnitriangular.single_zero_last_mul` — upper-unitriangular factors absorb the
  corner matrix unit `E₀ₙ`, and `Matrix.IsUpperUnitriangular.eq_one_add_single_zero_last` — an
  upper-unitriangular matrix vanishing away from the diagonal and the corner is `1 + t E₀ₙ`.
* `Matrix.isNilpotent_of_apply_eq_zero_of_le` — a matrix that is strictly block triangular for a
  ranking of its indices, not necessarily injective, is nilpotent.
* `Matrix.isNilpotent_of_isUpperTriangular_of_diag_eq_zero` — strict upper triangularity implies
  nilpotence.
* `Matrix.blockDiagonalPart` — the entries of a matrix between indices of equal rank for a
  ranking `b`, and `Matrix.BlockTriangular.isIdempotentElem_blockDiagonalPart`: it is idempotent
  for a block triangular idempotent.
* `Matrix.BlockTriangular.mul_apply_eq_zero_of_le` and its primed form — vanishing wherever a
  ranking of the indices does not strictly increase survives multiplication by block triangular
  matrices on either side.
* `Matrix.updateCol_mul_updateCol_apply_of_lt` — replacing the same column of both factors of a
  product with an upper-triangular right factor leaves the earlier columns of the product
  unchanged.
* `Matrix.exists_sum_mul_eq_of_isUpperUnitriangular` — a unitriangular system on a set of rows has
  a solution supported on the rows together with one further index, equal to one there.
* `TauCeti.isUpperTriangular_transvection_iff` — a transvection with its off-diagonal entry
  strictly below the diagonal is upper triangular exactly when its parameter vanishes.
* `TauCeti.vecMul_injective_of_submatrix_isUpperTriangular` — a rectangular matrix has injective
  row multiplication when a square column selection is upper triangular with nonzero diagonal.
* `TauCeti.unitDiagonalMatrixOfEntries` — the matrix with diagonal entries `1`, prescribed
  entries at the off-diagonal pairs satisfying a predicate and all other entries `0`, with its
  evaluation lemmas `TauCeti.unitDiagonalMatrixOfEntries_apply_of_mem`, `_apply_self` and
  `_apply_of_notMem`, and `TauCeti.isUpperUnitriangular_unitDiagonalMatrixOfEntries` — it is
  upper unitriangular when the pairs satisfying the predicate lie above the diagonal.
-/

public section

namespace Matrix

variable {R : Type*} {m : Type*}

/-- A matrix that is block triangular for an injective ranking of its indices has the product of
its diagonal entries as determinant: an injective ranking cuts it into singleton blocks. -/
theorem BlockTriangular.det_eq_prod_diag {ι α S : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder α] [CommRing S] {N : Matrix ι ι S} {b : ι → α} (hN : N.BlockTriangular b)
    (hb : Function.Injective b) : N.det = ∏ i, N i i := by
  rw [hN.det, Finset.prod_image fun x _ y _ hxy ↦ hb hxy]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  let _ : Unique {j // b j = b i} := ⟨⟨⟨i, rfl⟩⟩, fun j ↦ Subtype.ext (hb j.property)⟩
  exact det_unique _

/-- A square matrix is upper unitriangular when it is upper triangular and every diagonal entry
is one. -/
def IsUpperUnitriangular [LT m] [Zero R] [One R] (M : Matrix m m R) : Prop :=
  M.IsUpperTriangular ∧ ∀ i, M i i = 1

/-- Upper unitriangularity consists of upper triangularity and diagonal entries equal to one. -/
theorem isUpperUnitriangular_def [LT m] [Zero R] [One R] (M : Matrix m m R) :
    M.IsUpperUnitriangular ↔ M.IsUpperTriangular ∧ ∀ i, M i i = 1 :=
  Iff.rfl

/-- A matrix is upper unitriangular exactly when its entries strictly below the diagonal vanish
and its diagonal entries are one. -/
theorem isUpperUnitriangular_iff [LT m] [Zero R] [One R] (M : Matrix m m R) :
    M.IsUpperUnitriangular ↔ (∀ ⦃i j⦄, j < i → M i j = 0) ∧ ∀ i, M i i = 1 :=
  Iff.rfl

/-- An upper-unitriangular matrix is upper triangular. -/
theorem IsUpperUnitriangular.isUpperTriangular [LT m] [Zero R] [One R]
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) : M.IsUpperTriangular :=
  (isUpperUnitriangular_def M).1 hM |>.1

/-- Every diagonal entry of an upper-unitriangular matrix is one. -/
theorem IsUpperUnitriangular.apply_diag [LT m] [Zero R] [One R]
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) (i : m) : M i i = 1 :=
  ((isUpperUnitriangular_def M).1 hM).2 i

/-- Subtracting the identity preserves upper triangularity of an upper-unitriangular matrix. -/
theorem IsUpperUnitriangular.isUpperTriangular_sub_one [Preorder m] [DecidableEq m]
    [AddGroupWithOne R] {M : Matrix m m R} (hM : M.IsUpperUnitriangular) :
    (M - 1).IsUpperTriangular :=
  hM.isUpperTriangular.sub blockTriangular_one

/-- Subtracting the identity from an upper-unitriangular matrix gives a zero diagonal. -/
theorem IsUpperUnitriangular.sub_one_apply_diag [LT m] [DecidableEq m] [AddGroupWithOne R]
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) (i : m) : (M - 1) i i = 0 := by
  simp [hM.apply_diag]

/-- Selecting rows and columns by the same strictly increasing map preserves upper
triangularity. -/
theorem IsUpperTriangular.submatrix_of_strictMono {n : Type*} [Preorder m] [Preorder n]
    [Zero R]
    {M : Matrix m m R} (hM : M.IsUpperTriangular) {f : n → m} (hf : StrictMono f) :
    (M.submatrix f f).IsUpperTriangular :=
  fun _ _ hij ↦ hM (hf hij)

/-- Selecting the same strictly increasing family of rows and columns preserves upper
unitriangularity. In particular, this applies to principal submatrices and order-preserving
reindexing. -/
theorem IsUpperUnitriangular.submatrix {n : Type*} [Preorder m] [Preorder n] [Zero R] [One R]
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) {f : n → m} (hf : StrictMono f) :
    (M.submatrix f f).IsUpperUnitriangular :=
  ⟨hM.isUpperTriangular.submatrix_of_strictMono hf, fun i ↦ hM.apply_diag (f i)⟩

/-- Two upper-unitriangular matrices are equal if their entries strictly above the diagonal
agree. -/
theorem IsUpperUnitriangular.ext [LinearOrder m] [Zero R] [One R] {M N : Matrix m m R}
    (hM : M.IsUpperUnitriangular) (hN : N.IsUpperUnitriangular)
    (h : ∀ i j, i < j → M i j = N i j) : M = N := by
  ext i j
  by_cases hij : i < j
  · exact h i j hij
  · obtain hji | rfl := lt_or_eq_of_le (le_of_not_gt hij)
    · exact (hM.isUpperTriangular hji).trans (hN.isUpperTriangular hji).symm
    · exact (hM.apply_diag _).trans (hN.apply_diag _).symm

/-- The determinant of an upper-unitriangular matrix is one. -/
theorem IsUpperUnitriangular.det_eq_one [Fintype m] [DecidableEq m] [LinearOrder m] [CommRing R]
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) : M.det = 1 := by
  rw [det_of_isUpperTriangular hM.isUpperTriangular]
  exact Finset.prod_eq_one fun i _ ↦ hM.apply_diag i

/-- The determinant of an upper-unitriangular matrix is a unit. -/
theorem IsUpperUnitriangular.isUnit_det [Fintype m] [DecidableEq m] [LinearOrder m] [CommRing R]
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) : IsUnit M.det := by
  rw [hM.det_eq_one]
  exact isUnit_one

/-- A square matrix whose image under a local ring homomorphism `f` is upper triangular, with
units on the diagonal, has a unit determinant. -/
theorem isUnit_det_of_isUpperTriangular_map {n : Type*} [Fintype n] [DecidableEq n]
    [LinearOrder n] {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} [IsLocalHom f]
    {M : Matrix n n R}
    (htri : (M.map f).IsUpperTriangular)
    (hdiag : ∀ i, IsUnit (f (M i i))) : IsUnit M.det := by
  rw [← _root_.isUnit_map_iff f, RingHom.map_det, RingHom.mapMatrix_apply,
    det_of_isUpperTriangular htri, IsUnit.prod_univ_iff]
  exact hdiag

/-- The identity matrix is upper unitriangular. -/
@[simp]
theorem isUpperUnitriangular_one [Preorder m] [DecidableEq m] [Zero R] [One R] :
    IsUpperUnitriangular (1 : Matrix m m R) := by
  refine ⟨blockTriangular_one, ?_⟩
  simp

/-- Applying a zero- and one-preserving map entrywise preserves upper-unitriangular matrices. -/
theorem IsUpperUnitriangular.map {S F : Type*} [LT m] [Zero R] [One R] [Zero S] [One S]
    [FunLike F R S] [ZeroHomClass F R S] [OneHomClass F R S] (f : F)
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) :
    (M.map f).IsUpperUnitriangular := by
  refine ⟨hM.1.map f, fun i ↦ ?_⟩
  simp [hM.2 i]

/-- Conjugating an upper-unitriangular matrix by a diagonal matrix with inverse diagonal
`diagonal d * M * diagonal e`, `d i * e i = 1`, gives an upper-unitriangular matrix. -/
theorem IsUpperUnitriangular.diagonal_mul_mul_diagonal [Fintype m] [DecidableEq m] [LT m]
    [NonAssocSemiring R] {M : Matrix m m R} (hM : M.IsUpperUnitriangular) {d e : m → R}
    (hde : ∀ i, d i * e i = 1) : (diagonal d * M * diagonal e).IsUpperUnitriangular := by
  refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · simp [mul_diagonal, diagonal_mul, hM.isUpperTriangular hij]
  · simp [mul_diagonal, diagonal_mul, hM.apply_diag i, hde i]

section Nilpotence

variable {S : Type*} [Semiring S] {n : ℕ}

/-- For a strictly upper-triangular matrix, `(M ^ k) i j = 0` whenever `j < i + k`. -/
theorem pow_apply_eq_zero_of_isUpperTriangular_of_diag_eq_zero
    {M : Matrix (Fin n) (Fin n) S} (htri : M.IsUpperTriangular)
    (hdiag : ∀ i, M i i = 0) (k : ℕ) (i j : Fin n)
    (hji : j.val < i.val + k) : (M ^ k) i j = 0 := by
  have hstrict : ∀ a b : Fin n, b ≤ a → M a b = 0 := by
    intro a b hba
    obtain hba | rfl := hba.lt_or_eq
    · exact htri hba
    · exact hdiag b
  induction k generalizing i j with
  | zero =>
      simp only [pow_zero]
      rw [one_apply_ne]
      intro hij
      subst j
      omega
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hil : i.val + k ≤ l.val
      · rw [hstrict l j (by omega), mul_zero]
      · rw [ih (i := i) (j := l) (by omega), zero_mul]

/-- Let `M` be strictly block triangular for a ranking `b` of its indices: `M i j = 0` unless
`b i < b j`. An entry `(M ^ k) i j` is a sum over chains `i = z₀, …, z_k = j` with strictly
increasing ranks, all but the last ranked strictly below `j`, so it vanishes once `k` exceeds the
number of indices ranked strictly below `j`. -/
theorem pow_apply_eq_zero_of_apply_eq_zero_of_le [Fintype m] [DecidableEq m] {α : Type*}
    [LinearOrder α] {b : m → α} {M : Matrix m m S} (hM : ∀ i j, b j ≤ b i → M i j = 0) {k : ℕ}
    (i j : m) (hk : (Finset.univ.filter fun z ↦ b z < b j).card < k) : (M ^ k) i j = 0 := by
  induction k generalizing j with
  | zero => exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ ↦ ?_
      by_cases hl : b l < b j
      · -- `l` is ranked below `j` but not below itself, so fewer indices are ranked below `l`.
        have hlt : (Finset.univ.filter fun z ↦ b z < b l).card <
            (Finset.univ.filter fun z ↦ b z < b j).card := by
          refine Finset.card_lt_card ⟨fun z hz ↦ ?_, fun hsub ↦ ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
            exact hz.trans hl
          · have := hsub (by simpa using hl)
            simp at this
        rw [ih l (by omega), zero_mul]
      · rw [hM l j (not_lt.1 hl), mul_zero]

/-- A strictly block-triangular matrix, `M i j = 0` unless `b i < b j` for a ranking `b` of its
indices, has power equal to zero at the cardinality of its index type. -/
theorem pow_card_eq_zero_of_apply_eq_zero_of_le [Fintype m] [DecidableEq m] {α : Type*}
    [LinearOrder α] {b : m → α} {M : Matrix m m S} (hM : ∀ i j, b j ≤ b i → M i j = 0) :
    M ^ Fintype.card m = 0 := by
  ext i j
  refine pow_apply_eq_zero_of_apply_eq_zero_of_le hM i j ?_
  exact Finset.card_lt_univ_of_notMem (x := j) (by simp)

/-- A strictly block-triangular matrix, `M i j = 0` unless `b i < b j` for a ranking `b` of its
indices, is nilpotent. Neither commutativity of the entries nor injectivity of `b` is needed. -/
theorem isNilpotent_of_apply_eq_zero_of_le [Fintype m] [DecidableEq m] {α : Type*}
    [LinearOrder α] {b : m → α} {M : Matrix m m S} (hM : ∀ i j, b j ≤ b i → M i j = 0) :
    _root_.IsNilpotent M :=
  ⟨Fintype.card m, pow_card_eq_zero_of_apply_eq_zero_of_le hM⟩

/-- A strictly upper-triangular matrix has power equal to zero at the cardinality of its index
type. -/
theorem pow_card_eq_zero_of_isUpperTriangular_of_diag_eq_zero [Fintype m] [LinearOrder m]
    {M : Matrix m m S} (htri : M.IsUpperTriangular) (hdiag : ∀ i, M i i = 0) :
    M ^ Fintype.card m = 0 :=
  pow_card_eq_zero_of_apply_eq_zero_of_le (b := id) fun i j hji ↦
    hji.lt_or_eq.elim (fun h ↦ htri h) fun h ↦ by
      obtain rfl : j = i := h
      exact hdiag j

/-- A strictly upper-triangular square matrix is nilpotent. -/
theorem isNilpotent_of_isUpperTriangular_of_diag_eq_zero [Fintype m] [LinearOrder m]
    {M : Matrix m m S} (htri : M.IsUpperTriangular) (hdiag : ∀ i, M i i = 0) :
    _root_.IsNilpotent M :=
  ⟨Fintype.card m, pow_card_eq_zero_of_isUpperTriangular_of_diag_eq_zero htri hdiag⟩

end Nilpotence

section BlockDiagonalPart

variable {S α : Type*} {b : m → α}

/-- The block-diagonal part of a matrix for a ranking `b` of its indices: the entries between
indices of equal rank, with all other entries replaced by zero. -/
def blockDiagonalPart [Zero S] [DecidableEq α] (M : Matrix m m S) (b : m → α) : Matrix m m S :=
  of fun i j ↦ if b i = b j then M i j else 0

@[simp]
theorem blockDiagonalPart_apply [Zero S] [DecidableEq α] (M : Matrix m m S) (b : m → α) (i j : m) :
    M.blockDiagonalPart b i j = if b i = b j then M i j else 0 :=
  (rfl)

@[simp]
theorem blockDiagonalPart_map [Zero S] [DecidableEq α] {T : Type*} [Zero T] (M : Matrix m m S)
    (b : m → α) {f : S → T} (hf : f 0 = 0) :
    (M.map f).blockDiagonalPart b = (M.blockDiagonalPart b).map f := by
  ext i j
  by_cases h : b i = b j <;> simp [h, hf]

variable [LinearOrder α]

/-- The product of a matrix that is block triangular for a ranking `b` with one that vanishes
wherever `b` does not strictly increase from row to column again vanishes there. -/
theorem BlockTriangular.mul_apply_eq_zero_of_le [Semiring S] [Fintype m] {M N : Matrix m m S}
    (hM : M.BlockTriangular b) (hN : ∀ ⦃i j⦄, b j ≤ b i → N i j = 0) ⦃i j : m⦄
    (hij : b j ≤ b i) : (M * N) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ ↦ ?_
  rcases lt_or_ge (b l) (b i) with h | h
  · rw [hM h, zero_mul]
  · rw [hN (hij.trans h), mul_zero]

/-- The product of a matrix that vanishes wherever a ranking `b` does not strictly increase from
row to column with one that is block triangular for `b` again vanishes there. -/
theorem BlockTriangular.mul_apply_eq_zero_of_le' [Semiring S] [Fintype m] {M N : Matrix m m S}
    (hN : N.BlockTriangular b) (hM : ∀ ⦃i j⦄, b j ≤ b i → M i j = 0) ⦃i j : m⦄
    (hij : b j ≤ b i) : (M * N) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ ↦ ?_
  rcases lt_or_ge (b j) (b l) with h | h
  · rw [hN h, mul_zero]
  · rw [hM (h.trans hij), zero_mul]

theorem blockTriangular_blockDiagonalPart [Zero S] (M : Matrix m m S) :
    (M.blockDiagonalPart b).BlockTriangular b :=
  fun _ _ h ↦ by simp [h.ne']

/-- For a block triangular matrix, the difference from its block-diagonal part vanishes wherever
the ranking does not strictly increase from row to column. -/
theorem BlockTriangular.sub_blockDiagonalPart_apply_eq_zero_of_le [AddGroup S] {M : Matrix m m S}
    (hM : M.BlockTriangular b) ⦃i j : m⦄ (hij : b j ≤ b i) :
    (M - M.blockDiagonalPart b) i j = 0 := by
  rcases hij.lt_or_eq with h | h
  · simp [hM h, h.ne']
  · simp [h]

/-- The block-diagonal part of a block triangular idempotent matrix is idempotent. -/
theorem BlockTriangular.isIdempotentElem_blockDiagonalPart [Semiring S] [Fintype m]
    {M : Matrix m m S}
    (hM : M.BlockTriangular b) (hMM : IsIdempotentElem M) :
    IsIdempotentElem (M.blockDiagonalPart b) := by
  rw [IsIdempotentElem]
  ext i j
  rw [Matrix.mul_apply, blockDiagonalPart_apply]
  split_ifs with hij
  · -- Only the indices `l` of the rank of `i` and `j` contribute to `(M * M) i j`.
    conv_rhs => rw [← hMM.eq, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [blockDiagonalPart_apply, blockDiagonalPart_apply]
    by_cases hl : b i = b l
    · rw [ite_eq_left hl, ite_eq_left (hl ▸ hij)]
    · rw [ite_eq_right hl, zero_mul]
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hM (show b j < b l from hij ▸ h), mul_zero]
      · rw [hM h, zero_mul]
  · refine Finset.sum_eq_zero fun l _ ↦ ?_
    rw [blockDiagonalPart_apply, blockDiagonalPart_apply]
    split_ifs with h1 h2 <;> simp_all

end BlockDiagonalPart

variable [NonUnitalNonAssocSemiring R] {n : Type*} [Fintype n] [LinearOrder n]
  {A B : Matrix n n R}

/-- The diagonal of a product of upper-triangular matrices is the pointwise product of the
diagonals. -/
theorem mul_apply_diag_of_isUpperTriangular (hA : A.IsUpperTriangular)
    (hB : B.IsUpperTriangular) (i : n) : (A * B) i i = A i i * B i i := by
  -- the only surviving term of `∑ k, A i k * B k i` is the one with `k = i`
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · exact fun h ↦ absurd (Finset.mem_univ i) h

/-- The diagonal of a product of lower-triangular matrices is the pointwise product of the
diagonals. -/
theorem mul_apply_diag_of_isLowerTriangular (hA : A.IsLowerTriangular)
    (hB : B.IsLowerTriangular) (i : n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hki | hik
    · rw [hB hki, mul_zero]
    · rw [hA hik, zero_mul]
  · exact fun h ↦ absurd (Finset.mem_univ i) h

/-- An upper-triangular matrix keeps a column vector zero from an index on: if `w` vanishes at
every index `≥ j`, then so does `A *ᵥ w` at `j`. -/
theorem IsUpperTriangular.mulVec_apply_eq_zero (hA : A.IsUpperTriangular) {w : n → R} {j : n}
    (hw : ∀ k, j ≤ k → w k = 0) : (A *ᵥ w) j = 0 := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rcases lt_or_ge k j with hkj | hjk
  · rw [hA hkj, zero_mul]
  · rw [hw k hjk, mul_zero]

/-- An entry of a product of lower- and upper-triangular matrices only involves the indices
`k ≤ min i j`. -/
theorem mul_apply_eq_sum_Iic_of_isLowerTriangular_of_isUpperTriangular
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [Fintype ι]
    {L U : Matrix ι ι R} (hL : L.IsLowerTriangular) (hU : U.IsUpperTriangular) (i j : ι) :
    (L * U) i j = ∑ k ∈ Finset.Iic (min i j), L i k * U k j := by
  rw [Matrix.mul_apply]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  rcases min_lt_iff.mp (not_le.mp (Finset.mem_Iic.not.mp hk)) with h | h
  · rw [hL h, zero_mul]
  · rw [hU h, mul_zero]

/-- An entry of `L * Lᵀ` for lower-triangular `L` only involves the columns `k ≤ min i j`. -/
theorem IsLowerTriangular.mul_transpose_apply_eq_sum_Iic
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [Fintype ι]
    {L : Matrix ι ι R} (hL : L.IsLowerTriangular) (i j : ι) :
    (L * Lᵀ) i j = ∑ k ∈ Finset.Iic (min i j), L i k * L j k := by
  apply mul_apply_eq_sum_Iic_of_isLowerTriangular_of_isUpperTriangular hL
  exact fun _ _ h ↦ hL h

/-- **The leading principal submatrix of a lower-triangular Gram matrix is a Gram matrix.** The
first `q` rows of a lower-triangular matrix vanish outside their first `q` columns, so the leading
`q × q` block of `L * Lᵀ` sees only the leading `q × q` block of `L`. -/
theorem IsLowerTriangular.submatrix_castLE_mul_transpose {p q : ℕ}
    {L : Matrix (Fin p) (Fin p) R} (hL : L.IsLowerTriangular) (hqp : q ≤ p) :
    (L * Lᵀ).submatrix (Fin.castLE hqp) (Fin.castLE hqp) =
      L.submatrix (Fin.castLE hqp) (Fin.castLE hqp) *
        (L.submatrix (Fin.castLE hqp) (Fin.castLE hqp))ᵀ := by
  ext i j
  simp only [submatrix_apply, Matrix.mul_apply, transpose_apply]
  have hvanish : ∀ k ∈ (Finset.univ : Finset (Fin p)),
      k ∉ Finset.univ.image (Fin.castLE hqp) →
      L (Fin.castLE hqp i) k * L (Fin.castLE hqp j) k = 0 := by
    intro k _ hk
    have hkq : q ≤ (k : ℕ) := by
      by_contra hcon
      exact hk (Finset.mem_image.2
        ⟨⟨(k : ℕ), not_le.1 hcon⟩, Finset.mem_univ _, by ext; simp⟩)
    have hlt : Fin.castLE hqp i < k := by
      have hi : ((Fin.castLE hqp i : Fin p) : ℕ) = (i : ℕ) := rfl
      have := i.isLt
      simp only [Fin.lt_def, hi]
      omega
    have h0 : L (Fin.castLE hqp i) k = 0 := hL hlt
    rw [h0, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Fin.castLE hqp))) hvanish,
    Finset.sum_image fun x _ y _ hxy => Fin.castLE_injective hqp hxy]

/-- A lower-triangular matrix over a linearly ordered commutative ring with nonnegative diagonal
whose product with its transpose is the identity is itself the identity. -/
theorem IsLowerTriangular.eq_one_of_mul_transpose_self_eq_one
    {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    {Q : Matrix n n K} (hQ : Q.IsLowerTriangular) (hQnonneg : ∀ i, 0 ≤ Q i i)
    (hQorth : Q * Qᵀ = 1) : Q = 1 := by
  let _ : Invertible Q := invertibleOfRightInverse Q Qᵀ hQorth
  have hQttri : Qᵀ.IsLowerTriangular := by
    rw [← inv_eq_right_inv hQorth]
    exact blockTriangular_inv_of_blockTriangular hQ
  have hQupper : Q.IsUpperTriangular := by
    intro i j hji
    simpa only [transpose_apply] using hQttri hji
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [hQ hij, one_apply_ne hij.ne]
  · have hii : Q i i * Q i i = 1 := by
      have hmul := mul_apply_diag_of_isUpperTriangular hQupper hQ.transpose i
      calc
        Q i i * Q i i = Q i i * Qᵀ i i := by rw [transpose_apply]
        _ = (Q * Qᵀ) i i := hmul.symm
        _ = 1 := by rw [hQorth, one_apply_eq]
    rw [one_apply_eq]
    nlinarith [hQnonneg i]
  · have hzero : Qᵀ j i = 0 := hQttri hij
    rw [one_apply_ne hij.ne']
    simpa only [transpose_apply] using hzero

/-- Lower-triangular matrices over an ordered field with positive diagonal are determined by
their Gram matrices `L * Lᵀ`.

Equivalently, the map `L ↦ L * Lᵀ` is injective on positive-diagonal lower-triangular matrices.
The empty index type is included. -/
theorem IsLowerTriangular.eq_of_mul_transpose_self_eq
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L M : Matrix n n K} (hL : L.IsLowerTriangular) (hM : M.IsLowerTriangular)
    (hLpos : ∀ i, 0 < L i i) (hMpos : ∀ i, 0 < M i i)
    (hgram : L * Lᵀ = M * Mᵀ) : L = M := by
  have hLdet : IsUnit L.det := by
    rw [det_of_isLowerTriangular L hL, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hLpos i).ne'
  let _ : Invertible L := invertibleOfIsUnitDet L hLdet
  have hLinv : L⁻¹.IsLowerTriangular :=
    blockTriangular_inv_of_blockTriangular hL
  have hQtri : (L⁻¹ * M).IsLowerTriangular := hLinv.mul hM
  have hQdiag : ∀ i, 0 < (L⁻¹ * M) i i := by
    intro i
    rw [mul_apply_diag_of_isLowerTriangular hLinv hM]
    apply mul_pos
    · have hinvdiag : L⁻¹ i i * L i i = 1 := by
        rw [← mul_apply_diag_of_isLowerTriangular hLinv hL,
          nonsing_inv_mul L hLdet, one_apply_eq]
      nlinarith [hLpos i]
    · exact hMpos i
  have hQorth := inv_mul_mul_transpose_inv_mul_eq_one hLdet hgram
  have hQone : L⁻¹ * M = 1 := by
    exact hQtri.eq_one_of_mul_transpose_self_eq_one (fun i ↦ (hQdiag i).le) hQorth
  calc
    L = L * 1 := (Matrix.mul_one L).symm
    _ = L * (L⁻¹ * M) := by rw [hQone]
    _ = M := by rw [← Matrix.mul_assoc, mul_nonsing_inv L hLdet, Matrix.one_mul]

section IntervalRestriction

variable {ι κ R : Type*} [LinearOrder ι] [Fintype ι] [Fintype κ]

/-- Restricting upper-triangular matrices to an order-connected set of indices preserves
multiplication. -/
theorem IsUpperTriangular.submatrix_mul [NonUnitalNonAssocSemiring R] {A B : Matrix ι ι R}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular)
    (e : κ ↪ ι) (he : Set.OrdConnected (Set.range e)) :
    (A * B).submatrix e e = A.submatrix e e * B.submatrix e e := by
  ext i j
  simp only [submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective e e.injective _ _ ?_ (fun _ ↦ rfl)
  intro k hk
  by_cases hki : k < e i
  · simp [hA hki]
  by_cases hjk : e j < k
  · simp [hB hjk]
  exact False.elim (hk (he.out ⟨i, rfl⟩ ⟨j, rfl⟩ ⟨not_lt.mp hki, not_lt.mp hjk⟩))

/-- Restricting an upper-triangular matrix to an order-connected set of indices preserves
powers. -/
theorem IsUpperTriangular.submatrix_pow [Semiring R] [DecidableEq ι] [DecidableEq κ]
    {A : Matrix ι ι R} (hA : A.IsUpperTriangular)
    (e : κ ↪ ι) (he : Set.OrdConnected (Set.range e)) (n : ℕ) :
    (A ^ n).submatrix e e = (A.submatrix e e) ^ n := by
  induction n with
  | zero => simp only [pow_zero, submatrix_one_embedding]
  | succ n ih => rw [pow_succ, IsUpperTriangular.submatrix_mul (hA.pow n) hA e he, ih, pow_succ]

end IntervalRestriction

/-- The diagonal of a power of an upper-triangular matrix is the corresponding power of the
diagonal entry. -/
@[simp]
theorem pow_apply_diag_of_isUpperTriangular {T : Type*} [Semiring T] {M : Matrix n n T}
    (hM : M.IsUpperTriangular) (k : ℕ) (i : n) : (M ^ k) i i = M i i ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_apply_diag_of_isUpperTriangular (hM.pow k) hM, ih, ← pow_succ]

/-- **A geometric series in a strictly upper-triangular matrix is upper unitriangular**, for any
truncation `k` that is positive whenever the index type is inhabited.

Over an empty index type both conditions are vacuous, so nothing is asked of `k` there. -/
theorem isUpperUnitriangular_geom_sum_of_isUpperTriangular_of_diag_eq_zero
    {T : Type*} [Semiring T] {M : Matrix n n T} (hM : M.IsUpperTriangular)
    (hdiag : ∀ i, M i i = 0) {k : ℕ} (hk : Nonempty n → 0 < k) :
    (∑ j ∈ Finset.range k, M ^ j).IsUpperUnitriangular := by
  -- below the diagonal every power vanishes; on the diagonal every power after the zeroth does,
  -- leaving the `1` that `M ^ 0` contributes -- and the index `i` is itself the inhabitant that
  -- makes the range nonempty
  rw [isUpperUnitriangular_def]
  refine ⟨?_, ?_⟩
  · intro i j hji
    simp only [Matrix.sum_apply]
    exact Finset.sum_eq_zero fun l _ ↦ (hM.pow l) hji
  · intro i
    simp only [Matrix.sum_apply, pow_apply_diag_of_isUpperTriangular hM, hdiag i]
    simp [zero_pow_eq, hk ⟨i⟩]

/-- **The geometric series in a strictly upper-triangular matrix, truncated at the size of the
matrix, is upper unitriangular.**

This is the truncation that appears when inverting `1 - M`, being the exponent at which `M` has
already died (`Matrix.pow_card_eq_zero_of_isUpperTriangular_of_diag_eq_zero`). -/
theorem isUpperUnitriangular_geom_sum_card_of_isUpperTriangular_of_diag_eq_zero
    {T : Type*} [Semiring T] {M : Matrix n n T} (hM : M.IsUpperTriangular)
    (hdiag : ∀ i, M i i = 0) :
    (∑ j ∈ Finset.range (Fintype.card n), M ^ j).IsUpperUnitriangular :=
  isUpperUnitriangular_geom_sum_of_isUpperTriangular_of_diag_eq_zero hM hdiag
    fun _ ↦ Fintype.card_pos

variable {S : Type*} [CommRing S] {M : Matrix n n S}

/-- On the diagonal, the inverse of an invertible upper-triangular matrix inverts entrywise:
`M⁻¹ i i * M i i = 1`. -/
theorem inv_apply_diag_mul_of_isUpperTriangular [Invertible M] (hM : M.IsUpperTriangular)
    (i : n) : M⁻¹ i i * M i i = 1 := by
  have hinv : M⁻¹.IsUpperTriangular := blockTriangular_inv_of_blockTriangular hM
  have h := congrFun (congrFun (nonsing_inv_mul M (isUnit_det_of_invertible M)) i) i
  rwa [mul_apply_diag_of_isUpperTriangular hinv hM i, one_apply_eq] at h

/-- Where an invertible upper-triangular matrix has a `1` on the diagonal, so does its inverse.
The hypothesis is needed only at the entry asked about. -/
theorem inv_apply_diag_of_isUpperTriangular [Invertible M] (hM : M.IsUpperTriangular) {i : n}
    (hdiag : M i i = 1) : M⁻¹ i i = 1 := by
  simpa [hdiag] using inv_apply_diag_mul_of_isUpperTriangular hM i

/-- On the diagonal, the inverse of an invertible lower-triangular matrix inverts entrywise:
`M⁻¹ i i * M i i = 1`. -/
theorem inv_apply_diag_mul_of_isLowerTriangular [Invertible M] (hM : M.IsLowerTriangular)
    (i : n) : M⁻¹ i i * M i i = 1 := by
  have hinv : M⁻¹.IsLowerTriangular := blockTriangular_inv_of_blockTriangular hM
  have h := congrFun (congrFun (nonsing_inv_mul M (isUnit_det_of_invertible M)) i) i
  rwa [mul_apply_diag_of_isLowerTriangular hinv hM i, one_apply_eq] at h

/-- Where an invertible lower-triangular matrix has a `1` on the diagonal, so does its inverse.
The hypothesis is needed only at the entry asked about. -/
theorem inv_apply_diag_of_isLowerTriangular [Invertible M] (hM : M.IsLowerTriangular) {i : n}
    (hdiag : M i i = 1) : M⁻¹ i i = 1 := by
  simpa [hdiag] using inv_apply_diag_mul_of_isLowerTriangular hM i

/-- A product of upper-unitriangular matrices is upper unitriangular. -/
theorem IsUpperUnitriangular.mul {T p : Type*} [NonAssocSemiring T] [Fintype p]
    [LinearOrder p] {M N : Matrix p p T} (hM : M.IsUpperUnitriangular)
    (hN : N.IsUpperUnitriangular) : (M * N).IsUpperUnitriangular := by
  refine ⟨hM.1.mul hN.1, fun i ↦ ?_⟩
  rw [mul_apply_diag_of_isUpperTriangular hM.1 hN.1, hM.2 i, hN.2 i, one_mul]

/-- An entry strictly above the diagonal of a product of upper-unitriangular matrices is the sum
of the two entries and of the products through the intermediate indices:
`(M * N) i j = M i j + N i j + ∑_{i < k < j} M i k * N k j`. -/
theorem IsUpperUnitriangular.mul_apply_of_lt {T p : Type*} [NonAssocSemiring T] [Fintype p]
    [LinearOrder p] [LocallyFiniteOrder p] {M N : Matrix p p T} (hM : M.IsUpperUnitriangular)
    (hN : N.IsUpperUnitriangular) {i j : p} (hij : i < j) :
    (M * N) i j = M i j + N i j + ∑ k ∈ Finset.Ioo i j, M i k * N k j := by
  rw [Matrix.mul_apply, ← Finset.sum_subset (Finset.subset_univ (Finset.Icc i j))]
  · rw [Finset.Icc_eq_cons_Ioc hij.le, Finset.sum_cons, Finset.Ioc_eq_cons_Ioo hij,
      Finset.sum_cons, hM.apply_diag, hN.apply_diag, one_mul, mul_one]
    abel
  · intro k _ hk
    rcases lt_trichotomy k i with hki | rfl | hik
    · rw [hM.isUpperTriangular hki, zero_mul]
    · exact absurd (Finset.left_mem_Icc.2 hij.le) hk
    · have hjk : j < k := lt_of_not_ge fun hkj ↦ hk (Finset.mem_Icc.2 ⟨hik.le, hkj⟩)
      rw [hN.isUpperTriangular hjk, mul_zero]

/-- The corner matrix unit `c E₀ₙ` is absorbed by multiplication on the right with an
upper-unitriangular matrix: its first column is that of the identity. -/
theorem IsUpperUnitriangular.mul_single_zero_last {T : Type*} [NonAssocSemiring T] {n : ℕ}
    {G : Matrix (Fin (n + 1)) (Fin (n + 1)) T} (hG : G.IsUpperUnitriangular) (c : T) :
    G * single 0 (Fin.last n) c = single 0 (Fin.last n) c := by
  have hlt : ∀ {a b : Fin (n + 1)}, b < a → G a b = 0 := fun h ↦ hG.isUpperTriangular h
  ext a b
  by_cases hb : b = Fin.last n
  · subst hb
    rw [mul_single_apply_same]
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨k, rfl⟩
    · rw [hG.apply_diag, one_mul, single_apply_same]
    · rw [hlt (Fin.succ_pos k), zero_mul,
        single_apply_of_row_ne (Fin.succ_ne_zero k).symm]
  · rw [mul_single_apply_of_ne (hbj := hb), single_apply_of_col_ne _ _ (Ne.symm hb)]

/-- The corner matrix unit `c E₀ₙ` is absorbed by multiplication on the left with an
upper-unitriangular matrix: its last row is that of the identity. -/
theorem IsUpperUnitriangular.single_zero_last_mul {T : Type*} [NonAssocSemiring T] {n : ℕ}
    {G : Matrix (Fin (n + 1)) (Fin (n + 1)) T} (hG : G.IsUpperUnitriangular) (c : T) :
    single (0 : Fin (n + 1)) (Fin.last n) c * G = single 0 (Fin.last n) c := by
  have hlt : ∀ {a b : Fin (n + 1)}, b < a → G a b = 0 := fun h ↦ hG.isUpperTriangular h
  ext a b
  by_cases ha : a = 0
  · subst ha
    rw [single_mul_apply_same]
    rcases eq_or_lt_of_le (Fin.le_last b) with rfl | h
    · rw [hG.apply_diag, mul_one, single_apply_same]
    · rw [hlt h, mul_zero, single_apply_of_col_ne _ _ h.ne']
  · rw [single_mul_apply_of_ne (h := ha), single_apply_of_row_ne (Ne.symm ha)]

/-- An upper-unitriangular matrix whose entries above the diagonal vanish away from the corner
`(0, n)`, `n > 0`, is `1 + t E₀ₙ`, with `t` its corner entry. -/
theorem IsUpperUnitriangular.eq_one_add_single_zero_last {T : Type*} [NonAssocSemiring T]
    {n : ℕ} {Z : Matrix (Fin (n + 1)) (Fin (n + 1)) T} (hZ : Z.IsUpperUnitriangular) (hn : 0 < n)
    (hz : ∀ i j : Fin (n + 1), i < j → ¬ (i = 0 ∧ j = Fin.last n) → Z i j = 0) :
    Z = 1 + single 0 (Fin.last n) (Z 0 (Fin.last n)) := by
  have : NeZero n := NeZero.of_pos hn
  ext a b
  by_cases hab : a = 0 ∧ b = Fin.last n
  · obtain ⟨rfl, rfl⟩ := hab
    rw [Matrix.add_apply, single_apply_same, one_apply_ne Fin.last_pos'.ne, zero_add]
  · rw [Matrix.add_apply, single_apply_of_ne (h := fun h : 0 = a ∧ Fin.last n = b ↦
      hab ⟨h.1.symm, h.2.symm⟩), add_zero]
    rcases lt_trichotomy a b with h | rfl | h
    · rw [hz a b h hab, one_apply_ne h.ne]
    · rw [hZ.apply_diag, one_apply_eq]
    · rw [hZ.isUpperTriangular h, one_apply_ne h.ne']

/-- Every natural power of an upper-unitriangular matrix is upper unitriangular. -/
theorem IsUpperUnitriangular.pow {T p : Type*} [Semiring T] [Fintype p] [LinearOrder p]
    {M : Matrix p p T} (hM : M.IsUpperUnitriangular) (k : ℕ) :
    (M ^ k).IsUpperUnitriangular := by
  induction k with
  | zero => exact isUpperUnitriangular_one
  | succ k ih => rw [pow_succ]; exact ih.mul hM

/-- The inverse of an upper-unitriangular matrix is upper unitriangular. -/
theorem IsUpperUnitriangular.inv {T p : Type*} [CommRing T] [Fintype p] [LinearOrder p]
    {M : Matrix p p T} (hM : M.IsUpperUnitriangular) :
    M⁻¹.IsUpperUnitriangular := by
  -- The determinant is `1`, so `M` is invertible.
  have := ((isUnit_iff_isUnit_det M).2 hM.isUnit_det).invertible
  refine ⟨blockTriangular_inv_of_blockTriangular hM.1, fun i ↦ ?_⟩
  exact inv_apply_diag_of_isUpperTriangular hM.1 (hM.2 i)

/-- Subtracting the identity from an upper-unitriangular matrix gives a nilpotent matrix. -/
theorem IsUpperUnitriangular.isNilpotent_sub_one {T p : Type*} [Ring T] [Fintype p]
    [LinearOrder p] {M : Matrix p p T} (hM : M.IsUpperUnitriangular) :
    _root_.IsNilpotent (M - 1) :=
  isNilpotent_of_isUpperTriangular_of_diag_eq_zero
    hM.isUpperTriangular_sub_one hM.sub_one_apply_diag

/-- A nonzero submodule invariant under strictly upper-triangular matrices contains a nonzero
vector annihilated by all of them. Neither a field nor commutation of the matrices is required. -/
theorem exists_ne_zero_forall_mulVec_eq_zero_of_invariant_submodule
    {S ι κ : Type*} [Semiring S] [Fintype ι] [LinearOrder ι]
    (A : κ → Matrix ι ι S) (htri : ∀ j, (A j).IsUpperTriangular)
    (hdiag : ∀ j a, A j a a = 0) (N : Submodule S (ι → S)) (hN : N ≠ ⊥)
    (hstable : ∀ j v, v ∈ N → A j *ᵥ v ∈ N) :
    ∃ v ∈ N, v ≠ 0 ∧ ∀ j, A j *ᵥ v = 0 := by
  classical
  let P : ι → Prop := fun a ↦ ∃ v ∈ N, v a ≠ 0 ∧ ∀ b, a < b → v b = 0
  have hP : ∃ a, P a := by
    obtain ⟨v, hv, hv0⟩ := N.ne_bot_iff.mp hN
    obtain ⟨a, ha, htop⟩ := TauCeti.exists_ne_zero_forall_gt_eq_zero v hv0
    exact ⟨a, v, hv, ha, htop⟩
  obtain ⟨a, ha, hmin⟩ := (Set.toFinite {a | P a}).exists_minimal hP
  obtain ⟨v, hv, hva, hsupport⟩ := ha
  refine ⟨v, hv, fun h ↦ hva (congrFun h a), fun j ↦ ?_⟩
  by_contra hzero
  obtain ⟨b, hb, htop'⟩ := TauCeti.exists_ne_zero_forall_gt_eq_zero (A j *ᵥ v) hzero
  have hvanish (c : ι) (hac : a ≤ c) : (A j *ᵥ v) c = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    by_cases hcd : d ≤ c
    · have hentry : A j c d = 0 := by
        obtain hdc | rfl := hcd.lt_or_eq
        · exact htri j hdc
        · exact hdiag j d
      exact mul_eq_zero_of_left hentry _
    · exact mul_eq_zero_of_right _ (hsupport d (hac.trans_lt (lt_of_not_ge hcd)))
  have hba : b < a := lt_of_not_ge fun hab ↦ hb (hvanish b hab)
  exact hba.not_ge (hmin ⟨A j *ᵥ v, hstable j v hv, hb, htop'⟩ hba.le)

/-- Replacing the column `a` of both factors of a product leaves every earlier column `c < a` of
the product unchanged, when the right factor is upper triangular. -/
theorem updateCol_mul_updateCol_apply_of_lt {T l p : Type*} [NonUnitalNonAssocSemiring T]
    [Fintype p] [DecidableEq p] [Preorder p] {J : Matrix l p T} {H : Matrix p p T}
    (hH : H.IsUpperTriangular) {a c : p} (hca : c < a) (x : l → T) (y : p → T) (i : l) :
    (J.updateCol a x * H.updateCol a y) i c = (J * H) i c := by
  simp only [Matrix.mul_apply, updateCol_apply, hca.ne, ↓reduceIte]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  split_ifs with hk
  · rw [hk, hH hca, mul_zero, mul_zero]
  · rfl

/-- A unitriangular system on a set `S` of rows not containing `a`: there is a vector `y`, equal to
`1` at `a` and supported on `S ∪ {a}`, whose product with the principal submatrix of `J` on `S` is
`u`. -/
theorem exists_sum_mul_eq_of_isUpperUnitriangular {ι T : Type*} [LinearOrder ι] [Ring T]
    {J : Matrix ι ι T} (hJ : J.IsUpperUnitriangular) (u : ι → T) (a : ι) (S : Finset ι)
    (haS : a ∉ S) :
    ∃ y : ι → T, y a = 1 ∧ (∀ l, l ∉ S → l ≠ a → y l = 0) ∧
      ∀ i ∈ S, ∑ l ∈ S, J i l * y l = u i := by
  -- On `S` the vector `y` solves a unitriangular system, a principal submatrix of `J`.
  let M : Matrix S S T := J.submatrix (↑) (↑)
  have hM : M.IsUpperUnitriangular := hJ.submatrix (Subtype.strictMono_coe _)
  -- The two `DecidableEq` instances on `S`, from `ι` and from the order of `S`, agree.
  have hN : IsNilpotent (M - 1) := by convert hM.isNilpotent_sub_one
  have hunit : IsUnit M := by simpa using hN.isUnit_one_add
  obtain ⟨M', hM'⟩ := hunit.exists_right_inv
  let z : S → T := M' *ᵥ fun t : S ↦ u t
  have hz : M *ᵥ z = fun t : S ↦ u t := by
    simp only [z, mulVec_mulVec, hM', one_mulVec]
  let y : ι → T := fun l ↦ if h : l ∈ S then z ⟨l, h⟩ else if l = a then 1 else 0
  refine ⟨y, by simp [y, haS], fun l hl hla ↦ by simp [y, hl, hla], fun i hi ↦ ?_⟩
  have := congrFun hz ⟨i, hi⟩
  simp only [M, mulVec, dotProduct, submatrix_apply] at this
  rw [← this, ← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl fun t _ ↦ by simp [y, t.property]

end Matrix

open scoped Matrix

namespace TauCeti

/-- A transvection whose off-diagonal entry lies strictly *below* the diagonal is upper
triangular exactly when its parameter vanishes. The complementary case, an entry on or above the
diagonal, is Mathlib's `Matrix.blockTriangular_transvection`. -/
@[simp]
theorem isUpperTriangular_transvection_iff {n : Type*} [DecidableEq n] [Preorder n]
    {A : Type*} [CommRing A] {i j : n} (hij : j < i) (c : A) :
    (Matrix.transvection i j c).IsUpperTriangular ↔ c = 0 := by
  refine ⟨fun h => ?_, fun hc => ?_⟩
  · have hentry := h hij
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hij.ne',
      Matrix.single_apply_same, zero_add] at hentry
    exact hentry
  · rw [hc, Matrix.transvection_zero]
    exact Matrix.blockTriangular_one

/-- **A triangular selection of coordinates makes the rows independent.** If some choice `e` of a
coordinate for each row makes the matrix upper triangular - `M i (e j) = 0` for `j < i` - with a
nonzero diagonal, then the rows are independent: the selected columns form a square submatrix whose
determinant is the product of that diagonal. -/
theorem vecMul_injective_of_submatrix_isUpperTriangular {K ι κ : Type*} [Field K]
    [Fintype ι] [LinearOrder ι] {M : Matrix ι κ K}
    (e : ι → κ) (hlt : ∀ i j, j < i → M i (e j) = 0) (hdiag : ∀ i, M i (e i) ≠ 0) :
    Function.Injective M.vecMul := by
  have hsub : Function.Injective (M.submatrix id e).vecMul := by
    refine Matrix.vecMul_injective_of_isUnit ?_
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      Matrix.det_of_isUpperTriangular (M := M.submatrix id e) fun i j hji ↦ hlt i j hji]
    exact Finset.prod_ne_zero_iff.2 fun i _ ↦ hdiag i
  refine fun x y hxy ↦ hsub (funext fun j ↦ ?_)
  have hcol : ∀ z : ι → K,
      (fun v ↦ v ᵥ* M.submatrix id e) z j = (fun v ↦ v ᵥ* M) z (e j) := by
    intro z
    simp [Matrix.vecMul, dotProduct]
  rw [hcol x, hcol y]
  exact congrFun hxy (e j)

/-! ### Unit-diagonal matrices with prescribed entries -/

section UnitDiagonalMatrixOfEntries

variable {ι R : Type*} [Zero R] [One R]

open Classical in
/-- The matrix with the entry `1` on the diagonal, the prescribed entry `f p` at each
off-diagonal pair `p` with `P p`, and the entry `0` everywhere else. When `P` holds only for
pairs `i < j` it is upper unitriangular
(`TauCeti.isUpperUnitriangular_unitDiagonalMatrixOfEntries`). -/
noncomputable def unitDiagonalMatrixOfEntries (P : ι × ι → Prop)
    (f : {p : ι × ι // P p} → R) : Matrix ι ι R :=
  Matrix.of fun i j => if i = j then 1 else if h : P (i, j) then f ⟨(i, j), h⟩ else 0

/-- The entry of `unitDiagonalMatrixOfEntries P f` at a pair satisfying `P`, off the
diagonal, is the prescribed one. -/
@[simp]
theorem unitDiagonalMatrixOfEntries_apply_of_mem (P : ι × ι → Prop)
    (f : {p : ι × ι // P p} → R) {i j : ι} (hij : i ≠ j) (h : P (i, j)) :
    unitDiagonalMatrixOfEntries P f i j = f ⟨(i, j), h⟩ := by
  simp only [unitDiagonalMatrixOfEntries, Matrix.of_apply, ite_eq_right hij, dite_eq_left h]

/-- Every diagonal entry of `unitDiagonalMatrixOfEntries P f` is one. -/
@[simp]
theorem unitDiagonalMatrixOfEntries_apply_self (P : ι × ι → Prop)
    (f : {p : ι × ι // P p} → R) (i : ι) :
    unitDiagonalMatrixOfEntries P f i i = 1 := by
  simp only [unitDiagonalMatrixOfEntries, Matrix.of_apply, ite_true]

/-- The entries of `unitDiagonalMatrixOfEntries P f` off the diagonal and off the pairs
satisfying `P` are zero. -/
@[simp]
theorem unitDiagonalMatrixOfEntries_apply_of_notMem (P : ι × ι → Prop)
    (f : {p : ι × ι // P p} → R) {i j : ι} (hij : i ≠ j) (h : ¬ P (i, j)) :
    unitDiagonalMatrixOfEntries P f i j = 0 := by
  simp only [unitDiagonalMatrixOfEntries, Matrix.of_apply, ite_eq_right hij, dite_eq_right h]

/-- If every pair satisfying `P` lies strictly above the diagonal,
`unitDiagonalMatrixOfEntries P f` is upper unitriangular. -/
theorem isUpperUnitriangular_unitDiagonalMatrixOfEntries [Preorder ι] (P : ι × ι → Prop)
    (hP : ∀ p, P p → p.1 < p.2) (f : {p : ι × ι // P p} → R) :
    (unitDiagonalMatrixOfEntries P f).IsUpperUnitriangular := by
  rw [Matrix.isUpperUnitriangular_def]
  exact ⟨fun i j hji => unitDiagonalMatrixOfEntries_apply_of_notMem P f (ne_of_lt hji).symm
      (fun h' => lt_irrefl j (hji.trans (hP (i, j) h'))),
    unitDiagonalMatrixOfEntries_apply_self P f⟩

end UnitDiagonalMatrixOfEntries

end TauCeti

namespace Matrix

open Classical in
/-- Subtracting from each row of `G` a combination of the rows below it is multiplication on the
left by an upper-unitriangular matrix. -/
theorem exists_isUpperUnitriangular_mul_apply {R m n : Type*} [Ring R] [Fintype m] [Preorder m]
    (G : Matrix m n R) {w : m → n → R}
    (hw : ∀ i, w i ∈ Submodule.span R (G.row '' ↑(Finset.univ.filter fun j ↦ i < j))) :
    ∃ U : Matrix m m R, U.IsUpperUnitriangular ∧ ∀ i l, (U * G) i l = G i l - w i l := by
  classical
  choose c hc using fun i ↦ (Submodule.mem_span_image_finset_iff_exists_fun' R).mp (hw i)
  let U := TauCeti.unitDiagonalMatrixOfEntries (fun p : m × m ↦ p.1 < p.2)
    (fun p ↦ -c p.val.1 p.val.2)
  refine ⟨U, TauCeti.isUpperUnitriangular_unitDiagonalMatrixOfEntries _ (fun _ h ↦ h) _,
    fun i l ↦ ?_⟩
  have hterm (j : m) : U i j * G j l =
      (if i = j then G j l else 0) - (if i < j then c i j * G j l else 0) := by
    by_cases hij : i = j
    · subst j
      simp [U, TauCeti.unitDiagonalMatrixOfEntries_apply_self]
    · by_cases hlt : i < j
      · simp [U, TauCeti.unitDiagonalMatrixOfEntries_apply_of_mem, hij, hlt]
      · simp [U, TauCeti.unitDiagonalMatrixOfEntries_apply_of_notMem, hij, hlt]
  rw [← hc i]
  simp [Matrix.mul_apply, hterm, Finset.sum_sub_distrib, Finset.sum_filter, Finset.sum_apply]

end Matrix
