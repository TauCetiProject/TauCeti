/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, Claude Fable 5
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Matrix rank

This file records general results relating matrix rank to the corresponding linear maps,
maximal minors and change of scalars. In particular, over an integral domain a finite family of
rows is linearly independent exactly when one of its maximal minors is nonzero. Over a
star-ordered field, the source of `A` splits into the kernel of `A` and the range of its conjugate
transpose `Aᴴ`; read in a basis, this splits a space into the common kernel and the sum of the
ranges of a family of operators that are self-adjoint for the Hermitian form making the basis
orthonormal.

## Main results

* `Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero`: over an integral domain, the
  rows are linearly independent exactly when some maximal minor is nonzero.
* `Matrix.linearIndependent_map_algebraMap_row_iff`: row independence is unchanged by a faithful
  scalar extension to a domain.
* `Matrix.linearIndependent_rat_row_iff`: the case of integer matrices extended to `ℚ`.
* `Matrix.rank_eq_card_iff_vecMul_injective` characterizes full row rank by injectivity of right
  multiplication by the matrix.
* `Matrix.rank_eq_card_iff_mulVec_injective` characterizes full column rank by injectivity of
  matrix-vector multiplication.
* `Matrix.rank_left_factor_eq` and `Matrix.range_left_factor_eq`: an exact-rank
  factorization gives a full-column-rank left factor with the same column range.
* `Matrix.rank_add_rank_le_rank_mul_add_card`: Sylvester's rank inequality
  `rank A + rank B ≤ rank (A * B) + n` for an `m × n` matrix `A` and an `n × o` matrix `B`.
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

section LinearIndependent

variable {m n R : Type*} [Fintype m] [DecidableEq m] [Finite n]

/-- The field case of `Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero`: a family
of independent columns of the size of the row rank exists. -/
private theorem linearIndependent_row_iff_exists_det_submatrix_ne_zero_of_field {K : Type*}
    [Field K] {A : Matrix m n K} :
    LinearIndependent K A.row ↔ ∃ e : m ↪ n, (A.submatrix id e).det ≠ 0 := by
  have : Fintype n := Fintype.ofFinite n
  refine ⟨fun h ↦ ?_, fun ⟨e, he⟩ ↦ ?_⟩
  · obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
    have : Finite κ := Finite.of_injective a ha
    have : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card m = Fintype.card κ := by
      rw [linearIndependent_iff_card_eq_finrank_span.1 hli, Set.finrank, hspan,
        ← rank_eq_finrank_span_cols, h.rank_matrix]
    let e : m ↪ n := (Fintype.equivOfCardEq hcard).toEmbedding.trans ⟨a, ha⟩
    -- The columns of the square submatrix are the columns `A.col (e j)` (`col_submatrix_eq_comp`).
    have hcol : LinearIndependent K (A.submatrix id e).col :=
      hli.comp _ (Fintype.equivOfCardEq hcard).injective
    exact ⟨e, ((isUnit_iff_isUnit_det _).1 (linearIndependent_col_iff_isUnit.1 hcol)).ne_zero⟩
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
  simp only [submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    map_ne_zero_iff _ (IsFractionRing.injective R K)]

omit [Fintype m] [DecidableEq m] in
/-- The rows of an integer matrix are linearly independent over `ℚ` exactly when they are linearly
independent over `ℤ`. -/
theorem linearIndependent_rat_row_iff {A : Matrix m n ℤ} :
    LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row ↔ LinearIndependent ℤ A.row :=
  linearIndependent_map_algebraMap_row_iff

end LinearIndependent

section FullColumnRank

variable {R m n : Type*} [CommSemiring R] [OrzechProperty R] [Nontrivial R] [Fintype n]

/-- A matrix has full column rank exactly when matrix-vector multiplication by it is injective.
The row index type need not be finite. -/
theorem rank_eq_card_iff_mulVec_injective (B : Matrix m n R) :
    B.rank = Fintype.card n ↔ Function.Injective B.mulVec := by
  rw [mulVec_injective_iff, rank_eq_finrank_span_cols,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank, eq_comm]

end FullColumnRank

section ExactRankFactorization

variable {R m n : Type*} [CommSemiring R] [StrongRankCondition R] [Fintype n]

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
    _ ≤ L.rank := Matrix.rank_mul_le_left L C

end ExactRankFactorization

section ExactRankFactorRange

variable {𝕜 m n : Type*} [Field 𝕜] [Fintype n]

/-- An exact-rank left factor spans the column space of the factored matrix. -/
theorem range_left_factor_eq {ι : Type*} [Fintype ι]
    {M : Matrix m n 𝕜} {L : Matrix m ι 𝕜}
    {R : Matrix ι n 𝕜} (hM : M.rank = Fintype.card ι) (h : M = L * R) :
    LinearMap.range L.mulVecLin = LinearMap.range M.mulVecLin := by
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [h, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · have hL := rank_left_factor_eq hM h
    rw [Matrix.rank] at hM hL
    exact hM.trans hL.symm

end ExactRankFactorRange

variable {K : Type*} [Field K] {m n : Type*} [Fintype n]

section

variable [Fintype m]

/-- A matrix has full row rank exactly when right multiplication by it is injective. -/
theorem rank_eq_card_iff_vecMul_injective (B : Matrix m n K) :
    B.rank = Fintype.card m ↔ Function.Injective B.vecMul := by
  rw [vecMul_injective_iff, rank_eq_finrank_span_row,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank, eq_comm]

end

/-- Every matrix with finitely many columns over a field factors through a space whose dimension
is its rank. The factorization also applies to a rank-zero matrix, with inner index type `Fin 0`. -/
theorem exists_eq_mul_fin_rank (A : Matrix m n K) :
    ∃ (L : Matrix m (Fin A.rank) K) (R : Matrix (Fin A.rank) n K), A = L * R := by
  classical
  let e : LinearMap.range A.mulVecLin ≃ₗ[K] (Fin A.rank → K) :=
    (Module.finBasis K (LinearMap.range A.mulVecLin)).equivFun
  let l := (LinearMap.range A.mulVecLin).subtype.comp e.symm.toLinearMap
  let r := e.toLinearMap.comp A.mulVecLin.rangeRestrict
  have h : l.comp r = A.mulVecLin := by
    ext v i
    simp [l, r, LinearMap.comp_apply]
  refine ⟨LinearMap.toMatrix' l, LinearMap.toMatrix' r, ?_⟩
  rw [← LinearMap.toMatrix'_comp, h, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']

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

/-- **Sylvester's rank inequality**: for an `m × n` matrix `A` and an `n × o` matrix `B` over a
field, `rank A + rank B ≤ rank (A * B) + n`. Equivalently, multiplying by `A` lowers the rank of
`B` by at most the nullity of `A`. -/
theorem rank_add_rank_le_rank_mul_add_card {o : Type*} [Fintype o] (A : Matrix m n K)
    (B : Matrix n o K) : A.rank + B.rank ≤ (A * B).rank + Fintype.card n := by
  classical
  set S := LinearMap.range B.mulVecLin
  set g := A.mulVecLin.domRestrict S
  have hrange : (A * B).rank = Module.finrank K (LinearMap.range g) := by
    rw [rank, mulVecLin_mul, LinearMap.range_comp, LinearMap.range_domRestrict]
  have hker : Module.finrank K (LinearMap.ker g) ≤ Module.finrank K (LinearMap.ker A.mulVecLin) :=
    LinearMap.finrank_le_finrank_of_injective
      (f := S.subtype.restrict (p := LinearMap.ker g) (q := LinearMap.ker A.mulVecLin)
        fun x hx ↦ by simpa [g] using hx)
      fun x y h ↦ Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  have hg := g.finrank_range_add_finrank_ker
  have hA := A.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hA
  have hB : B.rank = Module.finrank K S := rfl
  rw [rank, hB, hrange]
  omega

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
    rw [rank, rank] at hrank
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
  let B : Matrix (ι × m) n R := Matrix.of fun p => A p.1 p.2
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
