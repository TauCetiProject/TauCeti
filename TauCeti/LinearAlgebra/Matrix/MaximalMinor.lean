/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Maximal minors, their gcd, and the Gram determinant

A *maximal minor* of a matrix `A` with rows indexed by `m` and columns indexed by `n` is the
determinant `det (A.submatrix id e)` of the square submatrix on all the rows and on the columns
picked out by an embedding `e : m ↪ n`. Over an integral domain the rows of `A` are linearly
independent exactly when some maximal minor is nonzero.

Over a GCD domain, `Matrix.minorGcd A` is the normalized gcd of the maximal minors. For an
integer matrix `A` with linearly independent rows, the quotient `√det (A * Aᵀ) / minorGcd A` is
classically the covolume of the lattice of integer solutions of `A *ᵥ x = 0`, which enters the
sharp form of Siegel's lemma due to Bombieri and Vaaler; that identity is not proved here. Since
the covolume depends only on the kernel, the quotient must be unchanged when `A` is replaced by
`B * A` with `det B ≠ 0`, and this file proves that invariance directly: the maximal minors are
multiplied by `det B` and the Gram determinant `det (A * Aᵀ)` by `det B ^ 2`. In particular the
quotient is invariant under `GL_m(ℤ)`, unlike Siegel's bound in terms of the entries of `A`. The
examples at the end of the file check this on the row `[2, 2]` and on a unimodular shear.

## Main definitions

* `Matrix.minorGcd`: the normalized gcd of the maximal minors.

## Main results

* `Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero`: over an integral domain, the
  rows are linearly independent exactly when some maximal minor is nonzero.
* `Matrix.minorGcd_ne_zero_iff`: the minor gcd is nonzero exactly when the rows are linearly
  independent.
* `Matrix.minorGcd_mul_left` and `Matrix.minorGcd_unit_mul`: left multiplication by `B`
  multiplies the minor gcd by `normalize (det B)`, and leaves it unchanged for `B` invertible.
* `Matrix.det_mul_transpose_mul_left`: the Gram determinant of `B * A` is `det B ^ 2` times that
  of `A`.
* `Matrix.det_mul_transpose_ne_zero_iff`: over a linearly ordered commutative ring, the Gram
  determinant `det (A * Aᵀ)` is nonzero exactly when the rows are linearly independent.
* `Matrix.det_mul_transpose_nonneg` and `Matrix.det_mul_transpose_pos_iff`: over `ℤ` the Gram
  determinant is nonnegative, and positive exactly when the rows are linearly independent.
* `Matrix.linearIndependent_rat_row_iff`: the rows of an integer matrix are linearly independent
  over `ℚ` exactly when they are over `ℤ`; `Matrix.det_mul_transpose_pos` and
  `Matrix.one_le_minorGcd` take independence over `ℚ` as their hypothesis.
* `Matrix.sqrt_det_div_minorGcd_mul_left` and `Matrix.sqrt_det_div_minorGcd_unit_mul`: the
  quotient `√det (A * Aᵀ) / minorGcd A` is unchanged by `A ↦ B * A` for `det B ≠ 0`, in
  particular for `B ∈ GL_m(ℤ)`.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.
* I. Aliev and M. Henk, *Minkowski's successive minima in convex and discrete geometry*,
  Commun. Math. **31** (2023), no. 2, 35–59, §6.
-/

public section

namespace Matrix

variable {m n R : Type*} [Fintype m] [DecidableEq m]

section LinearIndependent

variable [Finite n]

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

/-- Over an integral domain, the rows of a matrix are linearly independent exactly when some
maximal minor is nonzero. -/
theorem linearIndependent_row_iff_exists_det_submatrix_ne_zero [CommRing R] [IsDomain R]
    {A : Matrix m n R} :
    LinearIndependent R A.row ↔ ∃ e : m ↪ n, (A.submatrix id e).det ≠ 0 := by
  let K := FractionRing R
  -- `linearIndependent_algebraMap_comp_iff` maps each row entrywise; these are the rows of the
  -- matrix `A.map (algebraMap R K)`, to which the field case applies.
  have hrow : (fun i ↦ algebraMap R K ∘ A.row i) = (A.map (algebraMap R K)).row :=
    funext fun i ↦ (row_map A _ i).symm
  rw [← linearIndependent_algebraMap_comp_iff (S := K), hrow,
    linearIndependent_row_iff_exists_det_submatrix_ne_zero_of_field]
  simp only [submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    map_ne_zero_iff _ (IsFractionRing.injective R K)]

omit [Fintype m] [DecidableEq m] in
/-- The rows of an integer matrix are linearly independent over `ℚ` exactly when they are linearly
independent over `ℤ`. -/
theorem linearIndependent_rat_row_iff {A : Matrix m n ℤ} :
    LinearIndependent ℚ (fun i j ↦ (A i j : ℚ)) ↔ LinearIndependent ℤ A.row := by
  rw [← linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ) (v := A.row)]
  simp only [Function.comp_def, eq_intCast, row_apply]

end LinearIndependent

/-- A minor of `B * A` on all the rows is `det B` times the corresponding minor of `A`. -/
theorem det_submatrix_mul_left [CommRing R] (B : Matrix m m R) (A : Matrix m n R) (e : m → n) :
    ((B * A).submatrix id e).det = B.det * (A.submatrix id e).det := by
  rw [submatrix_mul B A id id e Function.bijective_id, submatrix_id_id, det_mul]

variable [Fintype n]

/-- The Gram determinant of the rows of `B * A` is `det B ^ 2` times that of `A`. -/
theorem det_mul_transpose_mul_left [CommRing R] (B : Matrix m m R) (A : Matrix m n R) :
    (B * A * (B * A)ᵀ).det = B.det ^ 2 * (A * Aᵀ).det := by
  rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc A, det_mul, det_mul, det_transpose]
  ring

section Gcd

section NormalizedGCDMonoid

variable [CommRing R] [NormalizedGCDMonoid R]

/-- The gcd of the maximal minors of `A`: the normalized gcd of the determinants
`det (A.submatrix id e)` over all embeddings `e : m ↪ n`. It is `0` exactly when every maximal
minor vanishes, in particular when `n` has fewer elements than `m`. -/
noncomputable def minorGcd (A : Matrix m n R) : R :=
  Finset.univ.gcd fun e : m ↪ n ↦ (A.submatrix id e).det

theorem minorGcd_def (A : Matrix m n R) :
    A.minorGcd = Finset.univ.gcd fun e : m ↪ n ↦ (A.submatrix id e).det :=
  (rfl)

theorem minorGcd_dvd (A : Matrix m n R) (e : m ↪ n) : A.minorGcd ∣ (A.submatrix id e).det :=
  Finset.gcd_dvd (Finset.mem_univ e)

theorem dvd_minorGcd_iff {A : Matrix m n R} {a : R} :
    a ∣ A.minorGcd ↔ ∀ e : m ↪ n, a ∣ (A.submatrix id e).det := by
  simp [minorGcd_def, Finset.dvd_gcd_iff]

@[simp]
theorem normalize_minorGcd (A : Matrix m n R) : normalize A.minorGcd = A.minorGcd :=
  Finset.normalize_gcd

theorem minorGcd_eq_zero_iff {A : Matrix m n R} :
    A.minorGcd = 0 ↔ ∀ e : m ↪ n, (A.submatrix id e).det = 0 := by
  simp [minorGcd_def, Finset.gcd_eq_zero_iff]

/-- The minor gcd is nonzero exactly when the rows are linearly independent. -/
theorem minorGcd_ne_zero_iff [Nontrivial R] {A : Matrix m n R} :
    A.minorGcd ≠ 0 ↔ LinearIndependent R A.row := by
  have : IsDomain R := {}
  simp [minorGcd_eq_zero_iff, linearIndependent_row_iff_exists_det_submatrix_ne_zero]

/-- Left multiplication by an invertible matrix does not change the minor gcd. -/
@[simp]
theorem minorGcd_unit_mul (U : GL m R) (A : Matrix m n R) :
    minorGcd ((U : Matrix m m R) * A) = A.minorGcd := by
  simp only [minorGcd_def, det_submatrix_mul_left]
  refine Associated.eq_of_normalized ?_ Finset.normalize_gcd Finset.normalize_gcd
  exact (Finset.gcd_mul_left' _ _ _).trans
    ((associated_isUnit_mul_left_iff (isUnits_det_units U)).2 (.refl _))

end NormalizedGCDMonoid

/-- Left multiplication by `B` multiplies the minor gcd by `normalize (det B)`. -/
theorem minorGcd_mul_left [CommRing R] [StrongNormalizedGCDMonoid R] (B : Matrix m m R)
    (A : Matrix m n R) : minorGcd (B * A) = normalize B.det * A.minorGcd := by
  simp only [minorGcd_def, det_submatrix_mul_left, Finset.gcd_mul_left]

end Gcd

section Gram

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Over a linearly ordered commutative ring, the Gram determinant `det (A * Aᵀ)` of the rows of
`A` is nonzero exactly when the rows are linearly independent. -/
theorem det_mul_transpose_ne_zero_iff {A : Matrix m n R} :
    (A * Aᵀ).det ≠ 0 ↔ LinearIndependent R A.row := by
  have key (v : m → R) : v ᵥ* (A * Aᵀ) = 0 ↔ v ᵥ* A = 0 := by
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [← vecMul_vecMul, h, zero_vecMul]⟩
    have := congr($h ⬝ᵥ v)
    rw [← vecMul_vecMul, ← dotProduct_mulVec, mulVec_transpose] at this
    simpa using this
  rw [← vecMul_injective_iff, Ne, ← exists_vecMul_eq_zero_iff, ← coe_vecMulLinear,
    injective_iff_map_eq_zero]
  simp only [key, vecMulLinear_apply]
  grind

end Gram

section Int

theorem minorGcd_nonneg (A : Matrix m n ℤ) : 0 ≤ A.minorGcd :=
  Int.nonneg_of_normalize_eq_self (normalize_minorGcd A)

/-- The minor gcd of an integer matrix is positive exactly when its rows are linearly
independent. -/
theorem minorGcd_pos_iff {A : Matrix m n ℤ} : 0 < A.minorGcd ↔ LinearIndependent ℤ A.row := by
  rw [← minorGcd_ne_zero_iff, (minorGcd_nonneg A).lt_iff_ne', ne_eq]

/-- The Gram determinant of the rows of an integer matrix is nonnegative. -/
theorem det_mul_transpose_nonneg (A : Matrix m n ℤ) : 0 ≤ (A * Aᵀ).det := by
  rw [← Int.cast_nonneg_iff (R := ℝ), Int.cast_det]
  convert (posSemidef_self_mul_conjTranspose (A.map (Int.castRingHom ℝ))).det_nonneg using 2
  ext
  simp [mul_apply]

/-- The Gram determinant of the rows of an integer matrix is positive exactly when the rows are
linearly independent. -/
theorem det_mul_transpose_pos_iff {A : Matrix m n ℤ} :
    0 < (A * Aᵀ).det ↔ LinearIndependent ℤ A.row := by
  rw [← det_mul_transpose_ne_zero_iff, (det_mul_transpose_nonneg A).lt_iff_ne', ne_eq]

/-- The Gram determinant of an integer matrix whose rows are linearly independent over `ℚ` is
positive. -/
theorem det_mul_transpose_pos {A : Matrix m n ℤ} (hA : LinearIndependent ℚ fun i j ↦ (A i j : ℚ)) :
    0 < (A * Aᵀ).det :=
  det_mul_transpose_pos_iff.2 (linearIndependent_rat_row_iff.1 hA)

/-- The minor gcd of an integer matrix whose rows are linearly independent over `ℚ` is at
least `1`. -/
theorem one_le_minorGcd {A : Matrix m n ℤ} (hA : LinearIndependent ℚ fun i j ↦ (A i j : ℚ)) :
    1 ≤ A.minorGcd :=
  minorGcd_pos_iff.2 (linearIndependent_rat_row_iff.1 hA)

/-- The quotient `√det (A * Aᵀ) / minorGcd A` is unchanged by `A ↦ B * A` for any square integer
matrix `B` with `det B ≠ 0`: both numerator and denominator are multiplied by `|det B|`. -/
theorem sqrt_det_div_minorGcd_mul_left {B : Matrix m m ℤ} (hB : B.det ≠ 0)
    (A : Matrix m n ℤ) :
    √((B * A * (B * A)ᵀ).det : ℝ) / ((B * A).minorGcd : ℝ) =
      √((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ) := by
  rw [det_mul_transpose_mul_left, minorGcd_mul_left, ← Int.abs_eq_normalize]
  push_cast [-Int.cast_det]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, mul_div_mul_left _ _ (by simpa)]

/-- The quotient `√det (A * Aᵀ) / minorGcd A` is invariant under `A ↦ U * A` for `U ∈ GL_m(ℤ)`. -/
theorem sqrt_det_div_minorGcd_unit_mul (U : GL m ℤ) (A : Matrix m n ℤ) :
    √(((U : Matrix m m ℤ) * A * ((U : Matrix m m ℤ) * A)ᵀ).det : ℝ) /
        (((U : Matrix m m ℤ) * A).minorGcd : ℝ) =
      √((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ) :=
  sqrt_det_div_minorGcd_mul_left (isUnits_det_units U).ne_zero A

end Int

/-! ### Examples -/

-- The row `[2, 2]` has independent rows, Gram determinant `8` and minor gcd `2`, so the quotient
-- `√8 / 2 = √2` is that of the row `[1, 1]`.
example : minorGcd !![(2 : ℤ), 2] = 2 := by
  have h (e : Fin 1 ↪ Fin 2) : (!![(2 : ℤ), 2].submatrix id e).det = 2 := by
    rw [det_unique, submatrix_apply]
    generalize e default = j
    fin_cases j <;> rfl
  refine dvd_antisymm_of_normalize_eq (normalize_minorGcd _) (by decide)
    (h ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩ ▸ minorGcd_dvd _ _) ?_
  exact dvd_minorGcd_iff.2 fun e ↦ (h e).symm ▸ dvd_rfl

example : (!![(2 : ℤ), 2] * !![(2 : ℤ), 2]ᵀ).det = 8 := by
  simp [det_unique, vecMul, dotProduct, Fin.sum_univ_two]

-- The shear `!![1, 1; 0, 1]` moves `!![1, 0, -1; 0, 1, -1]` to `!![1, 1, -2; 0, 1, -1]`. Both
-- have minor gcd `1` and Gram determinant `3`, while the largest entry grows from `1` to `2`.
example : minorGcd !![(1 : ℤ), 0, -1; 0, 1, -1] = 1 := by
  exact Int.eq_one_of_dvd_one (minorGcd_nonneg _)
    (by simpa [det_fin_two] using minorGcd_dvd !![(1 : ℤ), 0, -1; 0, 1, -1] ⟨![0, 1], by decide⟩)

example : (!![(1 : ℤ), 0, -1; 0, 1, -1] * !![(1 : ℤ), 0, -1; 0, 1, -1]ᵀ).det = 3 := by
  simp [det_fin_two, vecMul, dotProduct, Fin.sum_univ_three]

example : !![(1 : ℤ), 1; 0, 1] * !![(1 : ℤ), 0, -1; 0, 1, -1] = !![1, 1, -2; 0, 1, -1] := by
  simp

example : minorGcd !![(1 : ℤ), 1, -2; 0, 1, -1] = 1 := by
  exact Int.eq_one_of_dvd_one (minorGcd_nonneg _)
    (by simpa [det_fin_two] using minorGcd_dvd !![(1 : ℤ), 1, -2; 0, 1, -1] ⟨![0, 1], by decide⟩)

example : (!![(1 : ℤ), 1, -2; 0, 1, -1] * !![(1 : ℤ), 1, -2; 0, 1, -1]ᵀ).det = 3 := by
  simp [det_fin_two, vecMul, dotProduct, Fin.sum_univ_three]

end Matrix
