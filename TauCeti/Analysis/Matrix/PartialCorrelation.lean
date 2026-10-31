/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.Star.Real
import TauCeti.LinearAlgebra.Matrix.Triangular
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Fin

/-!
# Cholesky construction from partial correlations

Strictly lower coordinates in `(-1, 1)` determine a lower-triangular matrix with positive
diagonal and unit-length rows. Its Gram matrix is therefore positive definite with unit
diagonal. The determinant factors as the product of `1 - zᵢⱼ²`. These formulas are the
algebraic part of the partial-correlation change of variables for correlation matrices.
The unit-diagonal and determinant identities also hold on the closed cube.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open scoped BigOperators Matrix ContDiff Matrix.Norms.Elementwise

namespace TauCeti

/-- The strictly lower positions `(i, j)`, `j < i`, of a `p × p` matrix. A unit-diagonal
symmetric matrix, in particular a correlation matrix, is determined by its entries there. -/
abbrev strictLowerTriangle (p : ℕ) := {ij : Fin p × Fin p // ij.2 < ij.1}

variable {p : ℕ}

private def partialCorrelationRow (z : strictLowerTriangle p → ℝ) (i j : Fin p) : ℝ :=
  if h : j < i then z ⟨(i, j), h⟩ else 0

/-- The triangular factor associated to partial correlations `z`. Below the diagonal its
`(i,j)` entry is `zᵢⱼ ∏ k<j, √(1-zᵢₖ²)`; the diagonal is `∏ k<i, √(1-zᵢₖ²)` and entries
above it are zero. Square roots retain their usual totalization outside the closed cube. -/
def partialCorrelationCholesky (z : strictLowerTriangle p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j ↦ (if j < i then partialCorrelationRow z i j else if i = j then 1 else 0) *
    ∏ k ∈ Finset.Iio j, Real.sqrt (1 - partialCorrelationRow z i k ^ 2)

/-- The Gram matrix associated to partial correlations. On the open cube it is a
positive-definite correlation matrix. -/
def partialCorrelationGram (z : strictLowerTriangle p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  partialCorrelationCholesky z * (partialCorrelationCholesky z)ᵀ

/-- The partial-correlation Gram matrix is the triangular factor times its transpose. -/
theorem partialCorrelationGram_def (z : strictLowerTriangle p → ℝ) :
    partialCorrelationGram z =
      partialCorrelationCholesky z * (partialCorrelationCholesky z)ᵀ := (rfl)

/-- Zero partial correlations give the identity triangular factor. -/
@[simp]
theorem partialCorrelationCholesky_zero :
    partialCorrelationCholesky (0 : strictLowerTriangle p → ℝ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [partialCorrelationCholesky, partialCorrelationRow]
  · simp [partialCorrelationCholesky, partialCorrelationRow, h, Matrix.one_apply_ne h]

/-- Zero partial correlations give the identity correlation matrix. -/
@[simp]
theorem partialCorrelationGram_zero :
    partialCorrelationGram (0 : strictLowerTriangle p → ℝ) = 1 := by
  simp [partialCorrelationGram_def]

/-- Above the diagonal the partial-correlation Cholesky factor is zero. -/
@[simp]
theorem partialCorrelationCholesky_apply_of_lt (z : strictLowerTriangle p → ℝ)
    {i j : Fin p} (h : i < j) : partialCorrelationCholesky z i j = 0 := by
  simp [partialCorrelationCholesky, not_lt_of_gt h, h.ne]

private theorem prod_partialCorrelationRow (z : strictLowerTriangle p → ℝ) (f : ℝ → ℝ)
    (i j : Fin p) (h : j ≤ i) :
    (∏ k ∈ Finset.Iio j, f (partialCorrelationRow z i k)) =
      ∏ ij : strictLowerTriangle p with ij.1.1 = i ∧ ij.1.2 < j, f (z ij) := by
  apply Finset.prod_bij (fun k hk ↦ (⟨(i, k), (Finset.mem_Iio.1 hk).trans_le h⟩ :
    strictLowerTriangle p))
  · intro k hk
    simp [Finset.mem_Iio.1 hk]
  · intro a _ b _ hab
    exact congrArg (fun ij : strictLowerTriangle p ↦ ij.1.2) hab
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    exact ⟨ij.1.2, Finset.mem_Iio.2 hij.2, Subtype.ext (Prod.ext hij.1.symm rfl)⟩
  · intro k hk
    simp [partialCorrelationRow, (Finset.mem_Iio.1 hk).trans_le h]

private theorem row_filter (i : Fin p) :
    (Finset.univ.filter fun ij : strictLowerTriangle p ↦ ij.1.1 = i ∧ ij.1.2 < i) =
      Finset.univ.filter (fun ij : strictLowerTriangle p ↦ ij.1.1 = i) := by
  ext ij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
  intro h
  exact h ▸ ij.2

/-- The entry below the diagonal is the partial correlation times the preceding square-root
residual factors in the same row. -/
@[simp]
theorem partialCorrelationCholesky_apply_of_gt (z : strictLowerTriangle p → ℝ)
    {i j : Fin p} (h : j < i) :
    partialCorrelationCholesky z i j = z ⟨(i, j), h⟩ *
      ∏ ij : strictLowerTriangle p with ij.1.1 = i ∧ ij.1.2 < j,
        Real.sqrt (1 - z ij ^ 2) := by
  simp only [partialCorrelationCholesky, h, ↓reduceIte]
  rw [prod_partialCorrelationRow z (fun x ↦ Real.sqrt (1 - x ^ 2)) i j h.le]
  simp [partialCorrelationRow, h]

/-- The diagonal entry is the product of all square-root residual factors in that row. -/
@[simp]
theorem partialCorrelationCholesky_apply_self (z : strictLowerTriangle p → ℝ) (i : Fin p) :
    partialCorrelationCholesky z i i =
      ∏ ij : strictLowerTriangle p with ij.1.1 = i, Real.sqrt (1 - z ij ^ 2) := by
  simp only [partialCorrelationCholesky, lt_self_iff_false, ↓reduceIte, one_mul]
  rw [prod_partialCorrelationRow z (fun x ↦ Real.sqrt (1 - x ^ 2)) i i le_rfl, row_filter]

/-- The partial-correlation factor is lower triangular. -/
theorem isLowerTriangular_partialCorrelationCholesky (z : strictLowerTriangle p → ℝ) :
    (partialCorrelationCholesky z).IsLowerTriangular :=
  fun _ _ h ↦ partialCorrelationCholesky_apply_of_lt z h

private theorem row_sq_lt_one {z : strictLowerTriangle p → ℝ}
    (hz : ∀ ij, |z ij| < 1) (i j : Fin p) : partialCorrelationRow z i j ^ 2 < 1 := by
  by_cases h : j < i
  · simpa [partialCorrelationRow, h] using (sq_lt_one_iff_abs_lt_one _).2 (hz ⟨(i, j), h⟩)
  · simp [partialCorrelationRow, h]

private theorem row_sq_le_one {z : strictLowerTriangle p → ℝ}
    (hz : ∀ ij, |z ij| ≤ 1) (i j : Fin p) : partialCorrelationRow z i j ^ 2 ≤ 1 := by
  by_cases h : j < i
  · simpa [partialCorrelationRow, h] using (sq_le_one_iff_abs_le_one _).2 (hz ⟨(i, j), h⟩)
  · simp [partialCorrelationRow, h]

/-- On the open cube, the diagonal entries of the triangular factor are positive. -/
theorem partialCorrelationCholesky_diag_pos {z : strictLowerTriangle p → ℝ}
    (hz : ∀ ij, |z ij| < 1) (i : Fin p) : 0 < partialCorrelationCholesky z i i := by
  simp only [partialCorrelationCholesky, lt_self_iff_false, ↓reduceIte, one_mul]
  exact Finset.prod_pos fun j _ ↦ Real.sqrt_pos.2 (sub_pos.2 (row_sq_lt_one hz i j))

private theorem cholesky_sq {z : strictLowerTriangle p → ℝ}
    (hz : ∀ ij, |z ij| ≤ 1) (i j : Fin p) :
    partialCorrelationCholesky z i j ^ 2 =
      (if j < i then partialCorrelationRow z i j ^ 2 else if i = j then 1 else 0) *
        ∏ k ∈ Finset.Iio j, (1 - partialCorrelationRow z i k ^ 2) := by
  simp only [partialCorrelationCholesky, mul_pow, ← Finset.prod_pow]
  have hprod : (∏ k ∈ Finset.Iio j, Real.sqrt (1 - partialCorrelationRow z i k ^ 2) ^ 2) =
      ∏ k ∈ Finset.Iio j, (1 - partialCorrelationRow z i k ^ 2) := by
    apply Finset.prod_congr rfl
    intro k _
    exact Real.sq_sqrt (sub_nonneg.2 (row_sq_le_one hz i k))
  rw [hprod]
  split_ifs <;> simp

/-- Every row of the partial-correlation Cholesky factor has squared norm one on the
closed cube, including at boundary coordinates equal to `±1`. -/
theorem sum_sq_partialCorrelationCholesky {z : strictLowerTriangle p → ℝ}
    (hz : ∀ ij, |z ij| ≤ 1) (i : Fin p) :
    ∑ j, partialCorrelationCholesky z i j ^ 2 = 1 := by
  have hsum : (∑ j, partialCorrelationCholesky z i j ^ 2) =
      ∑ j ∈ Finset.Iic i, partialCorrelationCholesky z i j ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj ↦ ?_
    simp only [Finset.mem_Iic, not_le] at hj
    simp [partialCorrelationCholesky_apply_of_lt z hj]
  rw [hsum, Finset.Iic_eq_cons_Iio, Finset.sum_cons]
  simp only [cholesky_sq hz, lt_self_iff_false, ↓reduceIte, one_mul]
  have htel := Finset.prod_one_sub_ordered (Finset.Iio i)
    (fun j ↦ partialCorrelationRow z i j ^ 2)
  have hfilter (j : Fin p) (hj : j ∈ Finset.Iio i) :
      {k ∈ Finset.Iio i | k < j} = Finset.Iio j := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Iio]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.trans (Finset.mem_Iio.1 hj), h⟩⟩
  have hterms : (∑ j ∈ Finset.Iio i,
      (if j < i then partialCorrelationRow z i j ^ 2 else if i = j then 1 else 0) *
        ∏ k ∈ Finset.Iio j, (1 - partialCorrelationRow z i k ^ 2)) =
      ∑ j ∈ Finset.Iio i, partialCorrelationRow z i j ^ 2 *
        ∏ k ∈ Finset.Iio i with k < j, (1 - partialCorrelationRow z i k ^ 2) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [ite_eq_left (Finset.mem_Iio.1 hj), hfilter j hj]
  rw [hterms, htel]
  ring

/-- The partial-correlation Gram matrix has unit diagonal on the closed cube. -/
@[simp]
theorem partialCorrelationGram_apply_self {z : strictLowerTriangle p → ℝ}
    (hz : ∀ ij, |z ij| ≤ 1) (i : Fin p) : partialCorrelationGram z i i = 1 := by
  simpa [partialCorrelationGram, Matrix.mul_apply, Matrix.transpose_apply, pow_two] using
    sum_sq_partialCorrelationCholesky hz i

/-- A partial-correlation Gram matrix is positive semidefinite for arbitrary coordinates. -/
theorem posSemidef_partialCorrelationGram (z : strictLowerTriangle p → ℝ) :
    (partialCorrelationGram z).PosSemidef := by
  simpa [partialCorrelationGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (partialCorrelationCholesky z)

/-- Coordinates strictly between `-1` and `1` give a positive-definite correlation matrix. -/
theorem posDef_partialCorrelationGram {z : strictLowerTriangle p → ℝ}
    (hz : ∀ ij, |z ij| < 1) : (partialCorrelationGram z).PosDef := by
  have hdet : IsUnit (partialCorrelationCholesky z).det := by
    rw [Matrix.det_of_isLowerTriangular _ (isLowerTriangular_partialCorrelationCholesky z),
      isUnit_iff_ne_zero]
    exact (Finset.prod_pos fun i _ ↦ partialCorrelationCholesky_diag_pos hz i).ne'
  simpa only [partialCorrelationGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.mul_conjTranspose_self (partialCorrelationCholesky z)
      (Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet))

/-- On the closed cube the Gram determinant is the product of the residual variances
`1 - zᵢⱼ²`. This includes the empty product in dimensions zero and one. -/
theorem det_partialCorrelationGram {z : strictLowerTriangle p → ℝ}
    (hz : ∀ ij, |z ij| ≤ 1) :
    (partialCorrelationGram z).det = ∏ ij, (1 - z ij ^ 2) := by
  rw [partialCorrelationGram, Matrix.det_mul, Matrix.det_transpose, ← pow_two,
    Matrix.det_of_isLowerTriangular _ (isLowerTriangular_partialCorrelationCholesky z),
    ← Finset.prod_pow]
  simp only [cholesky_sq hz, lt_self_iff_false, ↓reduceIte, one_mul]
  have hrow (i : Fin p) :
      (∏ k ∈ Finset.Iio i, (1 - partialCorrelationRow z i k ^ 2)) =
        ∏ ij : strictLowerTriangle p with ij.1.1 = i, (1 - z ij ^ 2) := by
    rw [prod_partialCorrelationRow z (fun x ↦ 1 - x ^ 2) i i le_rfl, row_filter]
  simp_rw [hrow]
  exact Finset.prod_fiberwise Finset.univ (fun ij : strictLowerTriangle p ↦ ij.1.1)
    (fun ij ↦ 1 - z ij ^ 2)

/-- The triangular construction is injective on the open partial-correlation cube. -/
theorem injOn_partialCorrelationCholesky :
    Set.InjOn (partialCorrelationCholesky (p := p)) {z | ∀ ij, |z ij| < 1} := by
  intro z hz w hw heq
  have hrows : ∀ n, ∀ j : Fin p, j.val = n → ∀ i,
      partialCorrelationRow z i j = partialCorrelationRow w i j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj i
      by_cases hji : j < i
      · have hprod : (∏ k ∈ Finset.Iio j, Real.sqrt (1 - partialCorrelationRow z i k ^ 2)) =
            ∏ k ∈ Finset.Iio j, Real.sqrt (1 - partialCorrelationRow w i k ^ 2) := by
          apply Finset.prod_congr rfl
          intro k hk
          rw [ih k.val (hj ▸ Fin.lt_def.1 (Finset.mem_Iio.1 hk)) k rfl i]
        have hentry := congrArg (fun L : Matrix (Fin p) (Fin p) ℝ ↦ L i j) heq
        simp only [partialCorrelationCholesky, hji, ↓reduceIte] at hentry
        rw [hprod] at hentry
        exact mul_right_cancel₀ (Finset.prod_pos fun k _ ↦
          Real.sqrt_pos.2 (sub_pos.2 (row_sq_lt_one hw i k))).ne' hentry
      · simp [partialCorrelationRow, hji]
  funext ij
  simpa [partialCorrelationRow, ij.2] using hrows ij.1.2.val ij.1.2 rfl ij.1.1

/-- Distinct partial correlations in the open cube give distinct correlation matrices. -/
theorem injOn_partialCorrelationGram :
    Set.InjOn (partialCorrelationGram (p := p)) {z | ∀ ij, |z ij| < 1} := by
  intro z hz w hw heq
  apply injOn_partialCorrelationCholesky hz hw
  exact (isLowerTriangular_partialCorrelationCholesky z).eq_of_mul_transpose_self_eq
    (isLowerTriangular_partialCorrelationCholesky w)
    (partialCorrelationCholesky_diag_pos hz) (partialCorrelationCholesky_diag_pos hw) heq

private theorem continuous_partialCorrelationRow (i j : Fin p) :
    Continuous (fun z : strictLowerTriangle p → ℝ ↦ partialCorrelationRow z i j) := by
  unfold partialCorrelationRow
  split_ifs <;> fun_prop

/-- The triangular construction is continuous even outside the closed cube, using the
continuous totalized real square root. -/
@[fun_prop]
theorem continuous_partialCorrelationCholesky :
    Continuous (partialCorrelationCholesky (p := p)) := by
  unfold partialCorrelationCholesky
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply Continuous.mul
  · split_ifs <;> first | exact continuous_partialCorrelationRow i j | fun_prop
  · exact continuous_finsetProd _ fun k _ ↦
      (continuous_const.sub ((continuous_partialCorrelationRow i k).pow 2)).sqrt

/-- The Gram construction is continuous on the entire coordinate space. -/
@[fun_prop]
theorem continuous_partialCorrelationGram : Continuous (partialCorrelationGram (p := p)) := by
  unfold partialCorrelationGram
  exact continuous_partialCorrelationCholesky.matrix_mul
    continuous_partialCorrelationCholesky.matrix_transpose

private theorem contDiff_partialCorrelationRow (i j : Fin p) :
    ContDiff ℝ ∞ (fun z : strictLowerTriangle p → ℝ ↦ partialCorrelationRow z i j) := by
  unfold partialCorrelationRow
  split_ifs <;> fun_prop

/-- The triangular construction is smooth on the open partial-correlation cube. -/
theorem contDiffOn_partialCorrelationCholesky :
    ContDiffOn ℝ ∞ (partialCorrelationCholesky (p := p)) {z | ∀ ij, |z ij| < 1} := by
  unfold partialCorrelationCholesky
  apply contDiffOn_pi.2
  intro i
  apply contDiffOn_pi.2
  intro j
  apply ContDiffOn.mul
  · split_ifs <;> first | exact (contDiff_partialCorrelationRow i j).contDiffOn | fun_prop
  · apply contDiffOn_prod
    intro k _
    apply ContDiffOn.sqrt
    · exact contDiffOn_const.sub ((contDiff_partialCorrelationRow i k).contDiffOn.pow 2)
    · intro z hz
      exact (sub_pos.2 (row_sq_lt_one hz i k)).ne'

/-- The positive-definite correlation matrix construction is smooth on the open cube. -/
theorem contDiffOn_partialCorrelationGram :
    ContDiffOn ℝ ∞ (partialCorrelationGram (p := p)) {z | ∀ ij, |z ij| < 1} := by
  apply contDiffOn_pi.2
  intro i
  apply contDiffOn_pi.2
  intro j
  simp only [partialCorrelationGram, Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiffOn.sum
  intro k _
  exact ((contDiffOn_pi.1 (contDiffOn_pi.1 contDiffOn_partialCorrelationCholesky i)) k).mul
    ((contDiffOn_pi.1 (contDiffOn_pi.1 contDiffOn_partialCorrelationCholesky j)) k)

end TauCeti
