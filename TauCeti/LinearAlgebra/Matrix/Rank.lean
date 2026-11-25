/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, Claude Fable 5
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Idempotents
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import TauCeti.Data.Matrix.DotProduct
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Matrix rank

This file records general results relating matrix rank to the corresponding linear maps,
minors and change of scalars. In particular, over an integral domain a finite family of
rows is linearly independent exactly when one of its maximal minors is nonzero, and over a field
the rank is the largest size of a nonzero minor. Over a star-ordered field, the source of `A`
splits into the kernel of `A` and the range of its conjugate transpose `Aᴴ`; read in a basis, this
splits a space into the common kernel and the sum of the ranges of a family of operators that are
self-adjoint for the Hermitian form making the basis orthonormal.

## Main results

* `Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero`: over an integral domain, the
  rows are linearly independent exactly when some maximal minor is nonzero.
* `Matrix.exists_det_submatrix_ne_zero_of_linearIndepOn`: over a field, for a matrix with
  independent rows, independent columns extend to a column basis with a nonzero maximal minor.
* `Matrix.linearIndependent_row_of_map`: row independence over a domain lifts along every ring
  homomorphism of domains, such as a reduction `ℤ → ZMod ℓ`.
* `Matrix.le_rank_iff_exists_det_submatrix_ne_zero` and
  `Matrix.rank_le_iff_forall_det_submatrix_eq_zero`: over a field, the rank is at least `p`
  exactly when some `p × p` minor is nonzero, and at most `p` exactly when every
  `(p + 1) × (p + 1)` minor vanishes.
* `Matrix.finrank_ker_mulVecLin` and `Matrix.finrank_ker_mulVecLin_of_linearIndependent_rows`: the
  kernel dimension of a matrix over a field (in general, and with independent rows).
* `Matrix.ker_mulVecLin_eq_span_of_dotProduct_eq_zero`: for an independent family `x` orthogonal
  to the independent rows of a matrix `A`, with complementary sizes, the kernel of `A` is the span
  of `x`.
* `Matrix.rank_map`: the rank is unchanged by a homomorphism of fields applied to the entries.
* `Matrix.ker_mulVecLin_transpose_mul_diagonal_mul` and
  `Matrix.rank_transpose_mul_diagonal_mul`: positive diagonal weights preserve the kernel and
  rank of a Gram matrix over a linearly ordered ring and field, respectively.
* `Matrix.isCompl_ker_mulVecLin_transpose_mul_diagonal_range_map`: the weighted transpose kernel
  and column range of a matrix over a linearly ordered field remain complementary after mapping
  its entries to any field.
* `Matrix.linearIndependent_map_algebraMap_row_iff`: row independence is unchanged by a faithful
  scalar extension to a domain.
* `Matrix.linearIndependent_rat_row_iff`: the case of integer matrices extended to `ℚ`.
* `Matrix.rank_eq_card_iff_vecMul_injective` characterizes full row rank by injectivity of right
  multiplication by the matrix.
* `Matrix.rank_eq_card_iff_mulVec_injective` characterizes full column rank by injectivity of
  matrix-vector multiplication.
* `Matrix.finite_of_mulVec_surjective`: a matrix whose `mulVec` is surjective has finitely many
  rows.
* `Matrix.rank_left_factor_eq` and `Matrix.range_left_factor_eq`: an exact-rank
  factorization gives a full-column-rank left factor with the same column range.
* `Matrix.rank_mul_eq_right_of_rank_eq_card`: left multiplication by a full-column-rank matrix
  preserves rank.
* `LinearMap.rank_toMatrix`: the rank of the matrix of a linear map is the dimension of its range.
* `LinearMap.finrank_range_eq_of_toMatrix_eq_transpose`: over a field, maps with transposed
  matrices have ranges of the same dimension.
* `Matrix.natCard_range_mulVec_eq_pow_rank`: the column space of a matrix over a field `K` has
  `|K| ^ rank` elements.
* `Matrix.rank_conjAct_smul` and `Matrix.rank_neg`: conjugation by an invertible matrix and
  negation preserve the rank.
* `Matrix.rank_add_le`: over a field, the rank of a sum is at most the sum of the ranks.
* `Matrix.IsIdempotentElem.rank_one_sub_add_rank`, `Matrix.IsIdempotentElem.rank_add` and
  `Matrix.OrthogonalIdempotents.rank_sum`: over a field, the ranks of `e` and `1 - e` add up to
  the size of the matrix, and the rank of a sum of orthogonal idempotent matrices is the sum of
  their ranks.
* `Matrix.rank_fromBlocks_zero₁₂_zero₂₁`: over a field, the rank of a block-diagonal matrix is the
  sum of the ranks of its diagonal blocks.
* `Matrix.rank_conjTranspose_of_field` and
  `Matrix.rank_mul_conjTranspose_self_sub_mul_conjTranspose_self_le`: over a field with a star ring
  structure, the conjugate transpose preserves the rank and `rank (X Xᴴ - Y Yᴴ) ≤ 2 * rank (X - Y)`.
* `Matrix.exists_eq_mul_fin_rank`: a rectangular matrix factors through `Fin A.rank`.
* `Matrix.exists_eq_mul_of_rank_le` and `Matrix.rank_le_iff_exists_eq_mul`: a matrix has rank at
  most `r` exactly when it factors through `Fin r`.
* `Matrix.isCompl_ker_mulVecLin_range_mulVecLin_conjTranspose`: over a star-ordered field the
  kernel of `A` and the range of `Aᴴ` are complementary, and
  `Matrix.isCompl_iInf_ker_mulVecLin_iSup_range_mulVecLin_conjTranspose` is the same for a finite
  family of matrices.
* `LinearMap.isCompl_iInf_ker_iSup_range_of_isHermitian_toMatrix`: a finite family of
  endomorphisms with Hermitian matrices in a common basis splits the space into their common kernel
  and the sum of their ranges.

-/

public section

namespace Matrix

/-- The difference of matrices that agree outside one column has rank at most one. -/
theorem rank_sub_le_one_of_col_eq {R m n : Type*} [CommRing R] [StrongRankCondition R]
    [Finite n] (A B : Matrix m n R) (j : n)
    (h : ∀ k ≠ j, A.col k = B.col k) : (A - B).rank ≤ 1 := by
  classical
  have hsub : A - B = vecMulVec (fun i ↦ A i j - B i j) (fun k ↦ if k = j then 1 else 0) := by
    ext i k
    by_cases hk : k = j
    · subst k
      simp [vecMulVec_apply]
    · have heq : A i k = B i k := congrFun (h k hk) i
      simp [vecMulVec_apply, hk, heq]
  rw [hsub]
  exact rank_vecMulVec_le _ _

/-- The difference of matrices that agree outside one row has rank at most one. -/
theorem rank_sub_le_one_of_row_eq {R m n : Type*} [CommRing R] [StrongRankCondition R]
    [Finite n] (A B : Matrix m n R) (i : m)
    (h : ∀ k ≠ i, A.row k = B.row k) : (A - B).rank ≤ 1 := by
  classical
  have hsub : A - B = vecMulVec (fun k ↦ if k = i then 1 else 0) (fun j ↦ A i j - B i j) := by
    ext k j
    by_cases hk : k = i
    · subst k
      simp [vecMulVec_apply]
    · have heq : A k j = B k j := congrFun (h k hk) j
      simp [vecMulVec_apply, hk, heq]
  rw [hsub]
  exact rank_vecMulVec_le _ _

section LinearIndependent

variable {m n R : Type*} [Fintype m] [DecidableEq m] [Finite n]

/-- **Column basis extension.** For a matrix with linearly independent rows over a field, every
linearly independent set of columns extends to a column basis: an embedding `e` of the rows into
the columns whose range contains the set and whose square submatrix is invertible. -/
theorem exists_det_submatrix_ne_zero_of_linearIndepOn {K : Type*} [Field K] {A : Matrix m n K}
    (hA : LinearIndependent K A.row) {s : Set n} (hs : LinearIndepOn K A.col s) :
    ∃ e : m ↪ n, s ⊆ Set.range e ∧ (A.submatrix id e).det ≠ 0 := by
  classical
  have := Fintype.ofFinite n
  -- The columns span, since the rows are independent.
  have hspan : Submodule.span K (Set.range A.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_range_col, hA.rank_matrix, Module.finrank_fintype_fun_eq_card]
  -- Extend `s` to a set `B` of columns forming a basis; it has as many elements as there are rows.
  obtain ⟨B, -, hsB, hBspan, hBli⟩ := exists_linearIndepOn_extension hs (Set.subset_univ s)
  have hBtop : ⊤ ≤ Submodule.span K (Set.range fun j : B => A.col j) := by
    rw [← Set.image_eq_range, ← hspan, Submodule.span_le, ← Set.image_univ]
    exact hBspan
  have hcard : Fintype.card m = Fintype.card B := by
    rw [← Module.finrank_fintype_fun_eq_card (R := K),
      Module.finrank_eq_card_basis (Module.Basis.mk hBli hBtop)]
  let e : m ≃ B := Fintype.equivOfCardEq hcard
  refine ⟨e.toEmbedding.trans (Function.Embedding.subtype _),
    fun j hj => ⟨e.symm ⟨j, hsB hj⟩, by simp⟩, ?_⟩
  -- The columns of the square submatrix are the basis `B`.
  exact ((isUnit_iff_isUnit_det _).1
    (linearIndependent_col_iff_isUnit.1 (hBli.comp e e.injective))).ne_zero

/-- The field case of `Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero`: a family
of independent columns of the size of the row rank exists. -/
private theorem linearIndependent_row_iff_exists_det_submatrix_ne_zero_of_field {K : Type*}
    [Field K] {A : Matrix m n K} :
    LinearIndependent K A.row ↔ ∃ e : m ↪ n, (A.submatrix id e).det ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨e, he⟩ ↦ ?_⟩
  · obtain ⟨e, -, he⟩ := exists_det_submatrix_ne_zero_of_linearIndepOn h (linearIndepOn_empty K _)
    exact ⟨e, he⟩
  · -- The rows of the square submatrix are the rows of `A` restricted to the columns `e`.
    exact LinearIndependent.of_comp (LinearMap.funLeft K K e)
      (linearIndependent_rows_of_det_ne_zero he)

omit [Fintype m] [DecidableEq m] in
/-- The rows of a matrix over `R` are linearly independent over a domain `S` containing `R`
exactly when they are linearly independent over `R`. -/
theorem linearIndependent_map_algebraMap_row_iff {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [FaithfulSMul R S] [IsDomain S] {A : Matrix m n R} :
    LinearIndependent S (A.map (algebraMap R S)).row ↔ LinearIndependent R A.row :=
  -- The rows of `A.map (algebraMap R S)` are the rows of `A` mapped entrywise (`row_map`).
  linearIndependent_algebraMap_comp_iff

/-- Over an integral domain, the rows of a matrix are linearly independent exactly when some
maximal minor is nonzero. -/
theorem linearIndependent_row_iff_exists_det_submatrix_ne_zero [CommRing R] [IsDomain R]
    {A : Matrix m n R} :
    LinearIndependent R A.row ↔ ∃ e : m ↪ n, (A.submatrix id e).det ≠ 0 := by
  let K := FractionRing R
  rw [← linearIndependent_map_algebraMap_row_iff (S := K),
    linearIndependent_row_iff_exists_det_submatrix_ne_zero_of_field]
  simp only [det_submatrix_map_ne_zero_iff (IsFractionRing.injective R K)]

omit [Fintype m] [DecidableEq m] in
/-- **Row independence lifts along a ring homomorphism of domains.** If the rows of `A.map f` are
linearly independent over `S`, then the rows of `A` are linearly independent over `R`, for every
ring homomorphism `f`, injective or not (for instance the reduction `ℤ → ZMod ℓ`): a nonzero
maximal minor of `A.map f` lifts to a nonzero maximal minor of `A` on the same columns.
`Matrix.linearIndependent_map_algebraMap_row_iff` is the converse for a faithful scalar extension
to a domain. -/
theorem linearIndependent_row_of_map {S : Type*} [Finite m] [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (f : R →+* S) {A : Matrix m n R}
    (h : LinearIndependent S (A.map f).row) : LinearIndependent R A.row := by
  have := Fintype.ofFinite m
  classical
  obtain ⟨e, he⟩ := linearIndependent_row_iff_exists_det_submatrix_ne_zero.1 h
  exact linearIndependent_row_iff_exists_det_submatrix_ne_zero.2
    ⟨e, det_submatrix_ne_zero_of_map f he⟩

omit [Fintype m] [DecidableEq m] [Finite n] in
/-- **Rank and minors.** Over a field, a matrix has rank at least `p` exactly when one of its
`p × p` minors is nonzero. -/
theorem le_rank_iff_exists_det_submatrix_ne_zero {K : Type*} [Field K] [Finite m] [Finite n]
    {A : Matrix m n K} {p : ℕ} :
    p ≤ A.rank ↔ ∃ (r : Fin p ↪ m) (c : Fin p ↪ n), (A.submatrix r c).det ≠ 0 := by
  refine ⟨fun hp ↦ ?_, fun ⟨r, c, h⟩ ↦ ?_⟩
  · -- Choose `p` linearly independent rows, then a nonzero maximal minor among them.
    obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
    have : Finite κ := Finite.of_injective a ha
    have : Fintype κ := Fintype.ofFinite κ
    have hcard : A.rank = Fintype.card κ := by
      rw [linearIndependent_iff_card_eq_finrank_span.1 hli, Set.finrank, hspan,
        finrank_span_range_row]
    let r : Fin p ↪ m :=
      ((Fin.castLEEmb (hcard ▸ hp)).trans (Fintype.equivFin κ).symm.toEmbedding).trans ⟨a, ha⟩
    -- The rows of `A.submatrix r id` are the rows `A.row (r i)`.
    have hr : LinearIndependent K (A.submatrix r id).row :=
      hli.comp _ (Fin.castLEEmb _ |>.trans (Fintype.equivFin κ).symm.toEmbedding).injective
    obtain ⟨c, hc⟩ := linearIndependent_row_iff_exists_det_submatrix_ne_zero.1 hr
    exact ⟨r, c, by rwa [submatrix_submatrix] at hc⟩
  · classical
    simpa [rank_of_det_ne_zero h] using rank_submatrix_le A r c

omit [Fintype m] [DecidableEq m] [Finite n] in
/-- Over a field, a matrix has rank at most `p` exactly when all of its `(p + 1) × (p + 1)` minors
vanish. -/
theorem rank_le_iff_forall_det_submatrix_eq_zero {K : Type*} [Field K] [Finite m] [Finite n]
    {A : Matrix m n K} {p : ℕ} :
    A.rank ≤ p ↔ ∀ (r : Fin (p + 1) ↪ m) (c : Fin (p + 1) ↪ n), (A.submatrix r c).det = 0 := by
  rw [← not_lt, Nat.lt_iff_add_one_le, le_rank_iff_exists_det_submatrix_ne_zero]
  simp only [not_exists, ne_eq, not_not]

omit [Fintype m] [DecidableEq m] [Finite n] in
/-- The rank of a matrix over a field is unchanged by applying a homomorphism to another field to
its entries, since the images of its minors are the minors of its image. -/
theorem rank_map {K L : Type*} [Field K] [Field L] [Finite m] [Finite n] (A : Matrix m n K)
    (φ : K →+* L) : (A.map φ).rank = A.rank :=
  eq_of_forall_le_iff fun p ↦ by
    simp only [le_rank_iff_exists_det_submatrix_ne_zero, det_submatrix_map_ne_zero_iff φ.injective]

omit [Fintype m] [DecidableEq m] in
/-- The rows of an integer matrix are linearly independent over `ℚ` exactly when they are linearly
independent over `ℤ`. -/
theorem linearIndependent_rat_row_iff {A : Matrix m n ℤ} :
    LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row ↔ LinearIndependent ℤ A.row :=
  linearIndependent_map_algebraMap_row_iff

end LinearIndependent

section KernelDimension

/-- **Rank-nullity for a matrix over a field.** The kernel of `A.mulVecLin` has dimension equal to
its number of columns minus its rank. -/
theorem finrank_ker_mulVecLin {K m ι : Type*} [Field K] [Fintype ι] (A : Matrix m ι K) :
    Module.finrank K (LinearMap.ker A.mulVecLin) = Fintype.card ι - A.rank := by
  have h := A.mulVecLin.finrank_range_add_finrank_ker
  rw [finrank_range_mulVecLin, Module.finrank_fintype_fun_eq_card] at h
  omega

/-- The kernel of a matrix over a field with independent rows has dimension equal to its
number of columns minus its number of rows. -/
theorem finrank_ker_mulVecLin_of_linearIndependent_rows {K m ι : Type*} [Field K]
    [Fintype m] [Fintype ι] {A : Matrix m ι K} (hA : LinearIndependent K A.row) :
    Module.finrank K (LinearMap.ker A.mulVecLin) = Fintype.card ι - Fintype.card m := by
  rw [finrank_ker_mulVecLin, hA.rank_matrix]

/-- Let `x : m → ι → K` be a linearly independent family of vectors, and `A` a matrix with
linearly independent rows, with `#m + #n = #ι` where `n` indexes the rows of `A`, such that every
`x i` has dot product zero with every row of `A`. Then the kernel of `A` is the span of `x`. -/
theorem ker_mulVecLin_eq_span_of_dotProduct_eq_zero {K ι m n : Type*} [Field K] [Fintype ι]
    [Fintype m] [Fintype n] (hmn : Fintype.card m + Fintype.card n = Fintype.card ι)
    {x : m → ι → K} {A : Matrix n ι K} (hx : LinearIndependent K x)
    (hA : LinearIndependent K A.row) (hxA : ∀ i j, x i ⬝ᵥ A.row j = 0) :
    LinearMap.ker A.mulVecLin = Submodule.span K (Set.range x) := by
  have hle : Submodule.span K (Set.range x) ≤ LinearMap.ker A.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, mulVecLin_apply]
    ext j
    simp [mulVec_apply, dotProduct_comm, hxA]
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_span_eq_card hx, finrank_ker_mulVecLin_of_linearIndependent_rows hA]
  omega

end KernelDimension

section WeightedGram

/-- A Gram matrix with strictly positive diagonal weights has the same kernel as the original
matrix over a linearly ordered commutative ring. This is the weighted analogue of
`Matrix.ker_mulVecLin_transpose_mul_self`. -/
theorem ker_mulVecLin_transpose_mul_diagonal_mul {R m n : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n R) (w : m → R) (hw : ∀ i, 0 < w i) :
    LinearMap.ker (Aᵀ * diagonal w * A).mulVecLin = LinearMap.ker A.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_mulVec]
  constructor
  · intro h
    have h' := congrArg (dotProduct x) h
    rw [dotProduct_transpose_mulVec, dotProduct_zero] at h'
    have hs : w ⬝ᵥ (fun i ↦ (A *ᵥ x) i ^ 2) = 0 := by
      simpa only [mulVec_diagonal, dotProduct, pow_two, mul_assoc] using h'
    have hz := (TauCeti.dotProduct_eq_zero_iff_of_pos hw (fun i ↦ sq_nonneg ((A *ᵥ x) i))).1 hs
    ext i
    exact sq_eq_zero_iff.1 (congrFun hz i)
  · intro h
    rw [h, mulVec_zero, mulVec_zero]

/-- A Gram matrix with strictly positive diagonal weights has the same rank as the original
matrix over a linearly ordered field. This is the weighted analogue of
`Matrix.rank_transpose_mul_self`. -/
theorem rank_transpose_mul_diagonal_mul {R m n : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [Fintype m] [Finite n] [DecidableEq m]
    (A : Matrix m n R) (w : m → R) (hw : ∀ i, 0 < w i) :
    (Aᵀ * diagonal w * A).rank = A.rank := by
  let := Fintype.ofFinite n
  have h := congrArg (fun S : Submodule R (n → R) ↦ Module.finrank R S)
    (ker_mulVecLin_transpose_mul_diagonal_mul A w hw)
  rw [finrank_ker_mulVecLin, finrank_ker_mulVecLin] at h
  have hA := A.rank_le_card_width
  have hGram := (Aᵀ * diagonal w * A).rank_le_card_width
  omega

/-- After mapping a matrix and its positively weighted transpose from a linearly ordered field
to any field, the kernel of the weighted transpose complements the column range of the matrix.
The target field can be unordered. -/
theorem isCompl_ker_mulVecLin_transpose_mul_diagonal_range_map {R K m n : Type*} [Field R]
    [LinearOrder R] [IsStrictOrderedRing R] [Field K] [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n R) (φ : R →+* K) (w : m → R) (hw : ∀ i, 0 < w i) :
    IsCompl (LinearMap.ker ((Aᵀ * diagonal w).map φ).mulVecLin)
      (LinearMap.range (A.map φ).mulVecLin) := by
  set D := A.map φ
  set B := (Aᵀ * diagonal w).map φ
  have hrank : (B * D).rank = D.rank := by
    dsimp only [B, D]
    rw [← Matrix.map_mul, Matrix.rank_map, Matrix.rank_map]
    exact rank_transpose_mul_diagonal_mul A w hw
  have hrankB : B.rank ≤ D.rank := by
    dsimp only [B, D]
    rw [Matrix.rank_map, Matrix.rank_map]
    exact (Matrix.rank_mul_le_left _ _).trans_eq A.rank_transpose
  apply (Submodule.isCompl_iff_disjoint _ _ ?_).2
  · apply Disjoint.symm
    apply Submodule.disjoint_ker_of_finrank_le B.mulVecLin
    rw [← LinearMap.range_comp, ← mulVecLin_mul, finrank_range_mulVecLin,
      finrank_range_mulVecLin, hrank]
  · rw [finrank_ker_mulVecLin, finrank_range_mulVecLin, Module.finrank_fintype_fun_eq_card]
    omega

end WeightedGram

section FullColumnRank

variable {R m n : Type*} [CommSemiring R] [OrzechProperty R] [Nontrivial R] [Fintype n]

/-- A matrix has full column rank exactly when matrix-vector multiplication by it is injective.
The row index type need not be finite. -/
theorem rank_eq_card_iff_mulVec_injective (B : Matrix m n R) :
    B.rank = Fintype.card n ↔ Function.Injective B.mulVec := by
  rw [mulVec_injective_iff, ← finrank_span_range_col,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank, eq_comm]

end FullColumnRank

section FiniteRows

/-- If `A.mulVec` is surjective, then `A` has finitely many rows: a finite-dimensional space
cannot surject onto the infinite-dimensional space `m → K`. -/
theorem finite_of_mulVec_surjective {K : Type*} [Field K] {m n : Type*} [Fintype n]
    (A : Matrix m n K) (h : Function.Surjective A.mulVec) : Finite m := by
  have : Module.Finite K (m → K) := Module.Finite.of_surjective (mulVecLin A) h
  classical
  exact (Pi.linearIndependent_single_one m K).finite

end FiniteRows

section ExactRankFactorization

variable {R m n : Type*} [CommSemiring R] [StrongRankCondition R] [Finite n]

/-- If `M = L * C` has rank equal to the number of columns of `L`, then `L`
has full column rank. This holds over a commutative semiring with the strong rank condition;
the row index type need not be finite. -/
theorem rank_left_factor_eq {ι : Type*} [Fintype ι]
    {M : Matrix m n R} {L : Matrix m ι R}
    {C : Matrix ι n R} (hM : M.rank = Fintype.card ι)
    (h : M = L * C) : L.rank = Fintype.card ι := by
  refine le_antisymm (by simpa using L.rank_le_card_width) ?_
  calc Fintype.card ι = M.rank := hM.symm
    _ = (L * C).rank := by rw [h]
    _ ≤ L.rank := rank_mul_le_left L C

end ExactRankFactorization

/-- Left multiplication by a full-column-rank matrix preserves matrix rank. -/
theorem rank_mul_eq_right_of_rank_eq_card {R m r o : Type*} [CommRing R] [IsDomain R]
    [Fintype r] [Finite o] (A : Matrix m r R) (B : Matrix r o R)
    (hA : A.rank = Fintype.card r) : (A * B).rank = B.rank := by
  apply le_antisymm (rank_mul_le_right A B)
  have h := rank_mul_ge A B
  omega

section ExactRankFactorRange

variable {𝕜 m n : Type*} [Field 𝕜] [Fintype n]

/-- An exact-rank left factor spans the column space of the factored matrix. -/
theorem range_left_factor_eq {ι : Type*} [Fintype ι]
    {M : Matrix m n 𝕜} {L : Matrix m ι 𝕜}
    {R : Matrix ι n 𝕜} (hM : M.rank = Fintype.card ι) (h : M = L * R) :
    LinearMap.range L.mulVecLin = LinearMap.range M.mulVecLin := by
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [h, mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · have hL := rank_left_factor_eq hM h
    rw [← finrank_range_mulVecLin] at hM hL
    exact hM.trans hL.symm

end ExactRankFactorRange

section ToMatrix

/-- The rank of the matrix of a linear map in any pair of bases is the dimension of its range. -/
theorem _root_.LinearMap.rank_toMatrix {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁]
    [Module R M₁] [AddCommMonoid M₂] [Module R M₂] {m n : Type*} [Fintype m] [DecidableEq m]
    [Finite n] (f : M₁ →ₗ[R] M₂) (v₁ : Module.Basis m R M₁) (v₂ : Module.Basis n R M₂) :
    (LinearMap.toMatrix v₁ v₂ f).rank = Module.finrank R (LinearMap.range f) := by
  rw [rank_eq_finrank_range_toLin _ v₂ v₁, toLin_toMatrix]

/-- If the matrix of `g` in bases `e'`, `e` is the transpose of the matrix of `f` in bases `c`,
`c'`, then the ranges of `f` and `g` have the same dimension. -/
theorem _root_.LinearMap.finrank_range_eq_of_toMatrix_eq_transpose {K V V' W W' : Type*}
    [Field K] [AddCommMonoid V] [Module K V] [AddCommMonoid V'] [Module K V'] [AddCommMonoid W]
    [Module K W] [AddCommMonoid W'] [Module K W'] {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {c : Module.Basis ι K V} {c' : Module.Basis ι' K V'}
    {e : Module.Basis ι K W} {e' : Module.Basis ι' K W'} {f : V →ₗ[K] V'} {g : W' →ₗ[K] W}
    (h : LinearMap.toMatrix e' e g = (LinearMap.toMatrix c c' f)ᵀ) :
    Module.finrank K (LinearMap.range g) = Module.finrank K (LinearMap.range f) := by
  rw [← g.rank_toMatrix e' e, h, rank_transpose, f.rank_toMatrix]

end ToMatrix

section Conjugation

/-- Conjugation by an invertible matrix preserves the rank. -/
@[simp]
theorem rank_conjAct_smul {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (g : ConjAct (GL n R)) (A : Matrix n n R) : (g • A).rank = A.rank := by
  rw [ConjAct.units_smul_def, rank_mul_eq_left_of_isUnit_det _ _ (isUnits_det_units _),
    rank_mul_eq_right_of_isUnit_det _ _ (isUnits_det_units _)]

/-- Negation preserves the rank. -/
@[simp]
theorem rank_neg {m n R : Type*} [Finite n] [CommRing R] (A : Matrix m n R) :
    (-A).rank = A.rank := by
  simpa using rank_smul_of_mem_nonZeroDivisors A (isUnit_one (M := R)).neg.mem_nonZeroDivisors

/-- Inverting two invertible matrices preserves the rank of their difference. -/
theorem rank_inv_sub_inv {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    {P Q : Matrix n n R} (hP : IsUnit P) (hQ : IsUnit Q) :
    (P⁻¹ - Q⁻¹).rank = (P - Q).rank := by
  have hdetP := (isUnit_iff_isUnit_det _).mp hP
  have hdetQ := (isUnit_iff_isUnit_det _).mp hQ
  rw [inv_sub_inv (iff_of_true hP hQ),
    rank_mul_eq_left_of_isUnit_det _ _ (isUnit_nonsing_inv_det _ hdetQ),
    rank_mul_eq_right_of_isUnit_det _ _ (isUnit_nonsing_inv_det _ hdetP),
    ← neg_sub P Q, rank_neg]

end Conjugation

variable {K : Type*} [Field K] {m n : Type*} [Finite n]

section

variable [Fintype m]

/-- A matrix has full row rank exactly when right multiplication by it is injective. -/
theorem rank_eq_card_iff_vecMul_injective (B : Matrix m n K) :
    B.rank = Fintype.card m ↔ Function.Injective B.vecMul := by
  rw [vecMul_injective_iff, ← finrank_span_range_row,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank, eq_comm]

end

/-- The rank of a sum of matrices over a field is at most the sum of the ranks. -/
theorem rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  have := Fintype.ofFinite n
  rw [← finrank_range_mulVecLin, ← finrank_range_mulVecLin, ← finrank_range_mulVecLin,
    mulVecLin_add]
  refine (Submodule.finrank_mono ?_).trans
    (Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range A.mulVecLin)
      (LinearMap.range B.mulVecLin))
  exact LinearMap.range_add_le A.mulVecLin B.mulVecLin

/-- Over a field, the rank of the block-diagonal matrix `fromBlocks A 0 0 D` is the sum of the
ranks of `A` and `D`. -/
theorem rank_fromBlocks_zero₁₂_zero₂₁ {l l' m' : Type*} [Finite l] [Finite l']
    (A : Matrix m l K) (D : Matrix m' l' K) :
    (fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  classical
  have := Fintype.ofFinite l
  have := Fintype.ofFinite l'
  have h : (fromBlocks A 0 0 D).mulVecLin =
      (LinearEquiv.sumArrowLequivProdArrow m m' K K).symm.toLinearMap ∘ₗ
        (A.mulVecLin.prodMap D.mulVecLin) ∘ₗ
          (LinearEquiv.sumArrowLequivProdArrow l l' K K).toLinearMap := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨⟨u, v⟩, rfl⟩ := (LinearEquiv.sumArrowLequivProdArrow l l' K K).symm.surjective x
    ext (i | i) <;> simp [fromBlocks_mulVec, Function.comp_def]
  have hr : LinearMap.range (fromBlocks A 0 0 D).mulVecLin =
      ((LinearMap.range A.mulVecLin).prod (LinearMap.range D.mulVecLin)).map
        (LinearEquiv.sumArrowLequivProdArrow m m' K K).symm.toLinearMap := by
    simp [h, LinearMap.range_comp, LinearMap.range_prodMap]
  simp only [← finrank_range_mulVecLin]
  rw [hr, LinearEquiv.finrank_map_eq]
  exact (Submodule.prodEquiv _ _).finrank_eq.trans Module.finrank_prod

/-- Over a field, if `P + e + Q = 1` then the ranks of `P`, `e` and `Q` add up to at least the
size of the matrices. -/
lemma card_le_rank_add_rank_add_rank [Fintype m] [DecidableEq m] (P e Q : Matrix m m K)
    (h : P + e + Q = 1) : Fintype.card m ≤ P.rank + e.rank + Q.rank := by
  rw [← rank_one (R := K) (n := m), ← h]
  exact (rank_add_le _ _).trans (Nat.add_le_add_right (rank_add_le _ _) _)

/-- Over a field, let `e` be an idempotent and `A₁`, `A₂` matrices with `e A₁ = 0`, `A₂ e = 0` and
`A₂ A₁ = 0`. Then the ranks of `e`, `A₁` and `A₂` add up to at most the size of `e`: the images of
`e` and `A₁` are independent and both lie in the kernel of `A₂`. -/
lemma rank_add_rank_add_rank_le [Fintype m] {a c : Type*} [Finite a] (e : Matrix m m K)
    (A₁ : Matrix m a K) (A₂ : Matrix c m K) (he : e * e = e) (h₁ : e * A₁ = 0) (h₂ : A₂ * e = 0)
    (h₃ : A₂ * A₁ = 0) : e.rank + A₁.rank + A₂.rank ≤ Fintype.card m := by
  classical
  have := Fintype.ofFinite a
  have hdisj : LinearMap.range e.mulVecLin ⊓ LinearMap.range A₁.mulVecLin = ⊥ := by
    refine eq_bot_iff.2 fun x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ ↦ ?_
    simp only [mulVecLin_apply] at hy hz
    have h1 : e *ᵥ x = x := by rw [← hy, mulVec_mulVec, he]
    have h2 : e *ᵥ x = 0 := by rw [← hz, mulVec_mulVec, h₁, zero_mulVec]
    exact (Submodule.mem_bot K).2 (h1.symm.trans h2)
  have hle : LinearMap.range e.mulVecLin ⊔ LinearMap.range A₁.mulVecLin ≤
      LinearMap.ker A₂.mulVecLin := by
    refine sup_le ?_ ?_ <;> rintro _ ⟨y, rfl⟩ <;>
      simp [LinearMap.mem_ker, mulVec_mulVec, h₂, h₃]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range e.mulVecLin)
    (LinearMap.range A₁.mulVecLin)
  rw [hdisj, finrank_bot, add_zero] at hsum
  have hker := LinearMap.finrank_range_add_finrank_ker A₂.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hker
  have := Submodule.finrank_mono hle
  simp only [← finrank_range_mulVecLin]
  omega

/-- A decomposition of the identity into a homology projector and two null-homotopy terms
computes the sum of the three ranks. -/
lemma rank_add_rank_add_rank_eq_card [Fintype m] [DecidableEq m]
    {a c : Type*} [Fintype a] [Fintype c] (e : Matrix m m K)
    (A₁ : Matrix m a K) (A₂ : Matrix c m K) (σ : Matrix a m K) (τ : Matrix m c K)
    (he : e * e = e) (h₁ : e * A₁ = 0) (h₂ : A₂ * e = 0) (h₃ : A₂ * A₁ = 0)
    (h : e + A₁ * σ + τ * A₂ = 1) : e.rank + A₁.rank + A₂.rank = Fintype.card m := by
  have hle := rank_add_rank_add_rank_le e A₁ A₂ he h₁ h₂ h₃
  have hge := card_le_rank_add_rank_add_rank _ _ _ h
  have hσ := rank_mul_le_left A₁ σ
  have hτ := rank_mul_le_right τ A₂
  omega

/-- The ranks of an idempotent matrix `e` and of the complementary idempotent `1 - e` add up to
the size of the matrix: this is the decomposition `e + (1 - e) = 1` with `e (1 - e) = 0`. -/
theorem IsIdempotentElem.rank_one_sub_add_rank [Fintype m] [DecidableEq m] {e : Matrix m m K}
    (he : IsIdempotentElem e) : (1 - e).rank + e.rank = Fintype.card m := by
  have h := rank_add_rank_add_rank_eq_card e (1 - e) (0 : Matrix m m K) 1 0 he.eq
    (by rw [mul_sub, mul_one, he.eq, sub_self]) (zero_mul _) (zero_mul _) (by simp)
  rw [rank_zero, add_zero] at h
  omega

/-- The rank of the sum of two idempotent matrices `p` and `q` with `p * q = 0` and `q * p = 0`
is the sum of their ranks: `p`, `q` and `1 - p - q` are mutually annihilating, and `p + q` is the
idempotent complementary to `1 - p - q`. -/
theorem IsIdempotentElem.rank_add [Fintype m] {p q : Matrix m m K}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : p * q = 0) (hqp : q * p = 0) :
    (p + q).rank = p.rank + q.rank := by
  classical
  have hle := rank_add_rank_add_rank_le p q (1 - p - q) hp.eq hpq
    (by simp [sub_mul, hp.eq, hqp]) (by simp [sub_mul, hq.eq, hpq])
  have hcard := IsIdempotentElem.rank_one_sub_add_rank (hp.add hq (by simp [hpq, hqp]))
  rw [← sub_sub] at hcard
  have := rank_add_le p q
  omega

/-- The rank of a sum of orthogonal idempotent matrices is the sum of their ranks: the range of
the sum is the direct sum of the ranges. -/
theorem OrthogonalIdempotents.rank_sum [Fintype m] [DecidableEq m] {I : Type*}
    {e : I → Matrix m m K} (he : OrthogonalIdempotents e) (s : Finset I) :
    (∑ i ∈ s, e i).rank = ∑ i ∈ s, (e i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hqp : (∑ i ∈ s, e i) * e a = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i hi => he.ortho (ne_of_mem_of_not_mem hi ha)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact IsIdempotentElem.rank_add (he.idem a) he.isIdempotentElem_sum
      (he.mul_sum_of_notMem ha) hqp

section Field

variable {K : Type*} [Field K] {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]

/-- **Ranks in a split complex over a field.** Let `B * A = 0` over a field, and suppose that the
middle term `K^{ι₁}` is split by matrices `I`, `P` with `P I = 1`, `B I = 0`, `P A = 0` and
`I P + A σ + τ B = 1`. Then `rank A + rank B + |k| = |ι₁|`: the cohomology has dimension `|k|`. -/
theorem rank_add_rank_add_card_eq {k : Type*} [Fintype k] [DecidableEq k] [DecidableEq ι₁]
    (A : Matrix ι₁ ι₀ K) (B : Matrix ι₂ ι₁ K) (I : Matrix ι₁ k K) (P : Matrix k ι₁ K)
    (σ : Matrix ι₀ ι₁ K) (τ : Matrix ι₁ ι₂ K) (hBA : B * A = 0) (hPI : P * I = 1)
    (hBI : B * I = 0) (hPA : P * A = 0) (h : I * P + A * σ + τ * B = 1) :
    A.rank + B.rank + Fintype.card k = Fintype.card ι₁ := by
  have hk : (I * P).rank = Fintype.card k := by
    refine le_antisymm ((rank_mul_le_right _ _).trans (rank_le_card_height P)) ?_
    calc Fintype.card k = (1 : Matrix k k K).rank := (rank_one).symm
      _ = (P * (I * P) * I).rank := by
        rw [← Matrix.mul_assoc, hPI, Matrix.one_mul, hPI]
      _ ≤ (I * P).rank := (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  have hrank := rank_add_rank_add_rank_eq_card (I * P) A B σ τ
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hPI, Matrix.one_mul])
    (by rw [Matrix.mul_assoc, hPA, Matrix.mul_zero])
    (by rw [← Matrix.mul_assoc, hBI, Matrix.zero_mul]) hBA h
  omega

end Field

omit [Finite n] in
/-- The column space of a matrix over a field `K` has `|K| ^ rank` elements. Over an infinite
field both sides are `0` unless the rank is `0`. -/
theorem natCard_range_mulVec_eq_pow_rank [Fintype n] (A : Matrix m n K) :
    Nat.card (Set.range A.mulVec) = Nat.card K ^ A.rank := by
  rw [← finrank_range_mulVecLin, ← Module.natCard_eq_pow_finrank, ← coe_mulVecLin,
    ← LinearMap.coe_range, SetLike.coe_sort_coe]

/-- Every matrix with finitely many columns over a field factors through a space whose dimension
is its rank. The factorization also applies to a rank-zero matrix, with inner index type `Fin 0`. -/
theorem exists_eq_mul_fin_rank (A : Matrix m n K) :
    ∃ (L : Matrix m (Fin A.rank) K) (R : Matrix (Fin A.rank) n K), A = L * R := by
  classical
  have := Fintype.ofFinite n
  let e : LinearMap.range A.mulVecLin ≃ₗ[K] (Fin A.rank → K) :=
    ((Module.finBasis K (LinearMap.range A.mulVecLin)).reindex
      (finCongr A.finrank_range_mulVecLin)).equivFun
  let l := (LinearMap.range A.mulVecLin).subtype.comp e.symm.toLinearMap
  let r := e.toLinearMap.comp A.mulVecLin.rangeRestrict
  have h : l.comp r = A.mulVecLin := by
    ext v i
    simp [l, r, LinearMap.comp_apply]
  refine ⟨LinearMap.toMatrix' l, LinearMap.toMatrix' r, ?_⟩
  rw [← LinearMap.toMatrix'_comp, h, ← toLin'_apply', LinearMap.toMatrix'_toLin']

/-- A rank bound gives a factorization through `Fin r`, padding an exact-rank factorization
with zero columns and rows when necessary. -/
theorem exists_eq_mul_of_rank_le (A : Matrix m n K) {r : ℕ} (h : A.rank ≤ r) :
    ∃ (L : Matrix m (Fin r) K) (R : Matrix (Fin r) n K), A = L * R := by
  classical
  obtain ⟨L, R, hA⟩ := A.exists_eq_mul_fin_rank
  let e : Fin r ≃ Fin A.rank ⊕ Fin (r - A.rank) :=
    (finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm
  refine ⟨(fromCols L (0 : Matrix m (Fin (r - A.rank)) K)).submatrix id e,
    (fromRows R (0 : Matrix (Fin (r - A.rank)) n K)).submatrix e id, ?_⟩
  simpa only [submatrix_mul_equiv, fromCols_mul_fromRows, Matrix.zero_mul, add_zero,
    submatrix_id_id] using hA

/-- Matrix rank is at most `r` if and only if the matrix is a product with inner index `Fin r`.
In particular, rank is the least possible inner dimension of a factorization. -/
theorem rank_le_iff_exists_eq_mul (A : Matrix m n K) (r : ℕ) :
    A.rank ≤ r ↔ ∃ (L : Matrix m (Fin r) K) (R : Matrix (Fin r) n K), A = L * R := by
  refine ⟨A.exists_eq_mul_of_rank_le, ?_⟩
  rintro ⟨L, R, rfl⟩
  exact (rank_mul_le_left L R).trans (by simpa using L.rank_le_card_width)

section StarOrderedField

variable {R : Type*} [Field R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
  {m n : Type*} [Fintype m] [Fintype n]

/-- **The kernel of a matrix and the range of its conjugate transpose are complementary** over a
star-ordered field, such as `ℚ`, `ℝ` or `ℂ` (with `ComplexOrder`). Some such hypothesis is
needed: over `ZMod 2`, the kernel of the `1 × 2` matrix `!![1, 1]` and the range of its transpose
are both the line spanned by `![1, 1]`. -/
theorem isCompl_ker_mulVecLin_range_mulVecLin_conjTranspose (A : Matrix m n R) :
    IsCompl (LinearMap.ker A.mulVecLin) (LinearMap.range Aᴴ.mulVecLin) := by
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).mpr ?_
  · have h := A.mulVecLin.finrank_range_add_finrank_ker
    have hrank : Aᴴ.rank = A.rank := A.rank_conjTranspose
    rw [← finrank_range_mulVecLin, ← finrank_range_mulVecLin] at hrank
    rw [hrank, ← h, add_comm]
  · refine Submodule.disjoint_def.mpr fun x hx hx' => ?_
    obtain ⟨y, rfl⟩ := hx'
    have hy : y ∈ LinearMap.ker (Aᴴᴴ * Aᴴ).mulVecLin := by
      simpa [conjTranspose_conjTranspose, mulVec_mulVec] using hx
    rw [ker_mulVecLin_conjTranspose_mul_self] at hy
    exact hy

/-- **The common kernel of a finite family of matrices and the sum of the ranges of their conjugate
transposes are complementary** over a star-ordered field. This is
`Matrix.isCompl_ker_mulVecLin_range_mulVecLin_conjTranspose` for the matrix stacking the family. -/
theorem isCompl_iInf_ker_mulVecLin_iSup_range_mulVecLin_conjTranspose {ι : Type*} [Finite ι]
    (A : ι → Matrix m n R) :
    IsCompl (⨅ i, LinearMap.ker (A i).mulVecLin) (⨆ i, LinearMap.range (A i)ᴴ.mulVecLin) := by
  classical
  have := Fintype.ofFinite ι
  -- Stack the family into one matrix with rows indexed by `ι × m`.
  let B : Matrix (ι × m) n R := of fun p => A p.1 p.2
  have hker : LinearMap.ker B.mulVecLin = ⨅ i, LinearMap.ker (A i).mulVecLin := by
    ext x
    simp [B, Submodule.mem_iInf, funext_iff, mulVec, Prod.forall]
  -- The conjugate transpose of the stack sums the conjugate transposes of its blocks.
  have hsum (y : ι × m → R) : Bᴴ *ᵥ y = ∑ i, (A i)ᴴ *ᵥ fun r => y (i, r) := by
    ext u
    simp [B, mulVec, dotProduct, Fintype.sum_prod_type]
  have hrange : LinearMap.range Bᴴ.mulVecLin = ⨆ i, LinearMap.range (A i)ᴴ.mulVecLin := by
    refine le_antisymm ?_ (iSup_le fun i => ?_)
    · rintro _ ⟨y, rfl⟩
      rw [mulVecLin_apply, hsum]
      exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨_, rfl⟩
    · rintro _ ⟨z, rfl⟩
      refine ⟨fun p => if p.1 = i then z p.2 else 0, ?_⟩
      rw [mulVecLin_apply, hsum, Finset.sum_eq_single i
        (fun j _ hj => by simp only [hj, ite_false]; exact mulVec_zero _) (by simp)]
      simp
  rw [← hker, ← hrange]
  exact B.isCompl_ker_mulVecLin_range_mulVecLin_conjTranspose

end StarOrderedField

/-- The conjugate transpose of a matrix over a field with a star ring structure has the same
rank. -/
@[simp]
theorem rank_conjTranspose_of_field {R : Type*} [Field R] [StarRing R] {m n : Type*} [Finite m]
    [Finite n] (A : Matrix m n R) : Aᴴ.rank = A.rank := by
  have h : Aᴴ = (A.map (starRingEnd R))ᵀ := rfl
  rw [h, rank_transpose, rank_map]

section StarField

variable {R : Type*} [Field R] [StarRing R] {m n : Type*} [Finite m] [Fintype n]

/-- The rank of the difference of two Gram matrices `X * Xᴴ` and `Y * Yᴴ` is at most twice the
rank of the difference of the factors. -/
theorem rank_mul_conjTranspose_self_sub_mul_conjTranspose_self_le (X Y : Matrix m n R) :
    (X * Xᴴ - Y * Yᴴ).rank ≤ 2 * (X - Y).rank := by
  have h : X * Xᴴ - Y * Yᴴ = (X - Y) * Xᴴ + Y * (X - Y)ᴴ := by
    rw [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [h, two_mul]
  refine (rank_add_le _ _).trans (add_le_add (rank_mul_le_left _ _) ?_)
  exact (rank_mul_le_right _ _).trans (rank_conjTranspose_of_field _).le

end StarField
end Matrix

open Matrix in
/-- **Self-adjoint operators split off their common kernel.** Over a star-ordered field, let `f`
be a finite family of endomorphisms whose matrices in a basis `b` are Hermitian, that is, which are
self-adjoint for the Hermitian form making `b` orthonormal. Then their common kernel and the sum of
their ranges are complementary. This is
`Matrix.isCompl_iInf_ker_mulVecLin_iSup_range_mulVecLin_conjTranspose` read in the basis `b`. -/
theorem LinearMap.isCompl_iInf_ker_iSup_range_of_isHermitian_toMatrix {R V ι P : Type*} [Field R]
    [PartialOrder R] [StarRing R] [StarOrderedRing R] [AddCommGroup V] [Module R V] [Fintype ι]
    [DecidableEq ι] [Finite P] (b : Module.Basis ι R V) (f : P → V →ₗ[R] V)
    (hf : ∀ p, (LinearMap.toMatrix b b (f p)).IsHermitian) :
    IsCompl (⨅ p, LinearMap.ker (f p)) (⨆ p, LinearMap.range (f p)) := by
  let e := Submodule.orderIsoMapComap b.equivFun.symm
  -- In the coordinates of `b`, each `f p` is multiplication by its matrix.
  have hcoord (p : P) (x : V) :
      LinearMap.toMatrix b b (f p) *ᵥ b.equivFun x = b.equivFun (f p x) := by
    simpa using LinearMap.toMatrix_mulVec_repr b b (f p) x
  have hker (p : P) :
      LinearMap.ker (f p) = e (LinearMap.ker (LinearMap.toMatrix b b (f p)).mulVecLin) := by
    ext x
    simp [e, Submodule.mem_map_equiv, LinearMap.toMatrix_mulVec_repr]
  have hrange (p : P) :
      LinearMap.range (f p) = e (LinearMap.range (LinearMap.toMatrix b b (f p))ᴴ.mulVecLin) := by
    rw [(hf p).eq]
    ext x
    rw [Submodule.orderIsoMapComap_apply, Submodule.mem_map_equiv, LinearEquiv.symm_symm]
    refine ⟨fun ⟨y, hy⟩ => ⟨b.equivFun y, by rw [mulVecLin_apply, hcoord, hy]⟩,
      fun ⟨z, hz⟩ => ⟨b.equivFun.symm z, b.equivFun.injective ?_⟩⟩
    rw [← hcoord, LinearEquiv.apply_symm_apply, ← hz, mulVecLin_apply]
  simp only [hker, hrange, ← e.map_iInf, ← e.map_iSup]
  exact e.isCompl (Matrix.isCompl_iInf_ker_mulVecLin_iSup_range_mulVecLin_conjTranspose _)
