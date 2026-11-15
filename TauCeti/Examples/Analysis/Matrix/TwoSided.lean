/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.TwoSided
public import TauCeti.Analysis.Matrix.DiagonalIntertwining
public import TauCeti.Analysis.Normed.Operator.RowCompact
public import TauCeti.RingTheory.PowerSeries.Entire.Basic

/-!
# An entire minor series without row compactness

For a scalar `ϖ` with `0 < ‖ϖ‖ < 1`, the matrix `A i j = ϖ ^ (2 * i - j)`
(natural subtraction) acts boundedly on `C₀(ℕ, K)`. Every row contains an entry equal to one,
so its operator is not row compact. Its transpose does not act on `C₀` at all: the zeroth
column of the transpose is the constant family one.

Nevertheless the two-sided estimate with weights `w i = 2 * i`, `w' j = j` makes all its
principal-minor sums convergent and its minor series entire. The matrix
`B i j = ϖ ^ max i (j - i)` gives a row-compact realization of the same series. Indeed,
`A i j * ϖ ^ j = ϖ ^ i * B i j`, so diagonal cancellation identifies all principal minors.
This comparison does not claim bounded conjugacy or equality of operator spectra.

These examples distinguish the hypotheses for a convergent matrix minor series, an operator
on `C₀`, and a row-compact operator. They apply in particular to `ϖ = p` over `ℚ_p`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§3–5, for the row criterion and minor series.
-/

public section

open Filter Topology
open scoped ZeroAtInfty Matrix

namespace TauCeti.TwoSidedExample

variable {K : Type*} [NormedField K]

/-- For a topologically nilpotent scalar, a bounded matrix with null columns but non-null
uniform row norms. Natural subtraction implements the exponent `max (2i - j) 0`. -/
def matrix (ϖ : K) : Matrix ℕ ℕ K := fun i j ↦ ϖ ^ (2 * i - j)

/-- The matrix diagonally intertwined with `matrix ϖ`, with decaying rows when `‖ϖ‖ < 1`. -/
def compactMatrix (ϖ : K) : Matrix ℕ ℕ K := fun i j ↦ ϖ ^ max i (j - i)

@[simp]
theorem matrix_apply (ϖ : K) (i j : ℕ) : matrix ϖ i j = ϖ ^ (2 * i - j) := (rfl)

@[simp]
theorem compactMatrix_apply (ϖ : K) (i j : ℕ) :
    compactMatrix ϖ i j = ϖ ^ max i (j - i) := (rfl)

/-- All entries of the original matrix lie in the closed unit ball. -/
theorem norm_matrix_le_one {ϖ : K} (hϖ : ‖ϖ‖ ≤ 1) (i j : ℕ) :
    ‖matrix ϖ i j‖ ≤ 1 := by
  simpa using (pow_le_one₀ (n := 2 * i - j) (norm_nonneg ϖ) hϖ)

/-- Each column of the original matrix tends to zero. -/
theorem tendsto_matrix_column {ϖ : K} (hϖ : ‖ϖ‖ < 1) (j : ℕ) :
    Tendsto (fun i ↦ matrix ϖ i j) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  have hindex : Tendsto (fun i : ℕ ↦ 2 * i - j) atTop atTop :=
    (tendsto_sub_atTop_nat j).comp (tendsto_atTop_mono
      (fun i ↦ Nat.le_mul_of_pos_left i (by decide : 0 < 2)) tendsto_id)
  simpa only [matrix_apply, Function.comp_def] using
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ).comp hindex

variable [IsUltrametricDist K] [CompleteSpace K]

/-- The matrix `ϖ ^ max(2i-j,0)` as a bounded operator on `c₀`. -/
noncomputable def operator (ϖ : K) (hϖ : ‖ϖ‖ < 1) : C₀(ℕ, K) →L[K] C₀(ℕ, K) :=
  (matrix ϖ).toZeroAtInftyCLM (tendsto_matrix_column hϖ)
    ⟨1, norm_matrix_le_one hϖ.le⟩

@[simp]
theorem matrixCoeff_operator (ϖ : K) (hϖ : ‖ϖ‖ < 1) :
    (operator ϖ hϖ).matrixCoeff = matrix ϖ := by
  simp [operator]

/-- Every row of the bounded realization has norm one, not just a nonzero lower bound. -/
@[simp]
theorem rowNorm_operator (ϖ : K) (hϖ : ‖ϖ‖ < 1) (i : ℕ) :
    (operator ϖ hϖ).rowNorm i = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.rowNorm_le_of_forall_le zero_le_one fun j ↦ by
      simpa using norm_matrix_le_one hϖ.le i j
  · have h := ContinuousLinearMap.norm_matrixCoeff_le_rowNorm_of_le
      (u := operator ϖ hϖ) (i := i) (C := 1)
      (fun j ↦ by simpa using norm_matrix_le_one hϖ.le i j) (2 * i)
    simpa using h

/-- Boundedness and null columns do not imply row compactness, even when the minor series
is entire. -/
theorem not_isRowCompact_operator (ϖ : K) (hϖ : ‖ϖ‖ < 1) :
    ¬(operator ϖ hϖ).IsRowCompact := by
  intro h
  have hlim := h.tendsto_rowNorm
  rw [funext (rowNorm_operator ϖ hϖ)] at hlim
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)

omit [CompleteSpace K] in
/-- The transpose has no continuous linear realization on `c₀`, since its zeroth column
is the constant family one. -/
theorem not_exists_matrixCoeff_transpose (ϖ : K) :
    ¬∃ v : C₀(ℕ, K) →L[K] C₀(ℕ, K), v.matrixCoeff = (matrix ϖ)ᵀ := by
  rintro ⟨v, hv⟩
  have hlim : Tendsto (fun _ : ℕ ↦ (1 : K)) cofinite (𝓝 0) := by
    simpa [hv, Matrix.transpose_apply] using v.tendsto_matrixCoeff_cofinite 0
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The entries satisfy the two-sided estimate with weight difference `2i - j`. -/
theorem norm_matrix_le_zpow {ϖ : K} (hϖ₀ : ϖ ≠ 0) (hϖ₁ : ‖ϖ‖ ≤ 1) (i j : ℕ) :
    ‖matrix ϖ i j‖ ≤ ‖ϖ‖ ^ ((2 * i : ℤ) - j) := by
  rw [matrix_apply, norm_pow, ← zpow_natCast]
  exact zpow_le_zpow_right_of_le_one₀ (norm_pos_iff.mpr hϖ₀) hϖ₁ (by omega)

private theorem tendsto_weight_difference :
    Tendsto (fun i : ℕ ↦ (2 * i : ℤ) - i) cofinite atTop := by
  simpa [Nat.cofinite_eq_atTop, two_mul] using
    (tendsto_natCast_atTop_atTop : Tendsto (fun i : ℕ ↦ (i : ℤ)) atTop atTop)

/-- The principal-minor sums converge despite failure of row compactness. -/
theorem summable_principalMinor_matrix {ϖ : K} (hϖ₀ : ϖ ≠ 0) (hϖ₁ : ‖ϖ‖ < 1) (n : ℕ) :
    Summable fun s : {s : Finset ℕ // s.card = n} ↦ (matrix ϖ).principalMinor s :=
  Matrix.summable_principalMinor_of_zpow (norm_pos_iff.mpr hϖ₀) hϖ₁
    (norm_matrix_le_zpow hϖ₀ hϖ₁.le) tendsto_weight_difference n

omit [CompleteSpace K] in
/-- The original bounded, non-row-compact operator has an entire matrix minor series. -/
theorem isEntire_charPowerSeries_matrix {ϖ : K} (hϖ₀ : ϖ ≠ 0) (hϖ₁ : ‖ϖ‖ < 1) :
    (matrix ϖ).charPowerSeries.IsEntire :=
  PowerSeries.isEntire_iff.mpr fun r ↦ Matrix.isRestricted_charPowerSeries_of_zpow
    (norm_pos_iff.mpr hϖ₀) hϖ₁ (norm_matrix_le_zpow hϖ₀ hϖ₁.le) tendsto_weight_difference r

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- A geometric row bound for the second matrix. -/
theorem norm_compactMatrix_le {ϖ : K} (hϖ : ‖ϖ‖ ≤ 1) (i j : ℕ) :
    ‖compactMatrix ϖ i j‖ ≤ ‖ϖ‖ ^ i := by
  rw [compactMatrix_apply, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) hϖ (le_max_left _ _)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The row-decaying matrix has null columns as well. -/
theorem tendsto_compactMatrix_column {ϖ : K} (hϖ : ‖ϖ‖ < 1) (j : ℕ) :
    Tendsto (fun i ↦ compactMatrix ϖ i j) cofinite (𝓝 0) := by
  apply squeeze_zero_norm (fun i ↦ norm_compactMatrix_le hϖ.le i j)
  simpa [Nat.cofinite_eq_atTop] using
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg ϖ) hϖ

/-- The explicit compact realization of the same principal-minor series. -/
noncomputable def compactOperator (ϖ : K) (hϖ : ‖ϖ‖ < 1) : C₀(ℕ, K) →L[K] C₀(ℕ, K) :=
  (compactMatrix ϖ).toZeroAtInftyCLM (tendsto_compactMatrix_column hϖ)
    ⟨1, fun i j ↦ (norm_compactMatrix_le hϖ.le i j).trans
      (pow_le_one₀ (norm_nonneg ϖ) hϖ.le)⟩

@[simp]
theorem matrixCoeff_compactOperator (ϖ : K) (hϖ : ‖ϖ‖ < 1) :
    (compactOperator ϖ hϖ).matrixCoeff = compactMatrix ϖ := by
  simp [compactOperator]

/-- The second realization is row compact, unlike the original one. -/
theorem isRowCompact_compactOperator (ϖ : K) (hϖ : ‖ϖ‖ < 1) :
    (compactOperator ϖ hϖ).IsRowCompact := by
  apply ContinuousLinearMap.isRowCompact_of_norm_matrixCoeff_le
    (r := fun i ↦ ‖ϖ‖ ^ i)
  · simpa [Nat.cofinite_eq_atTop] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg ϖ) hϖ
  · simpa using norm_compactMatrix_le hϖ.le

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The intertwining diagonal is `d i = ϖ ^ i`; no inverse bound is asserted. -/
theorem diagonal_intertwining (ϖ : K) (i j : ℕ) :
    matrix ϖ i j * ϖ ^ j = ϖ ^ i * compactMatrix ϖ i j := by
  simp only [matrix_apply, compactMatrix_apply, ← pow_add]
  congr 1
  omega

/-- Diagonal cancellation identifies the entire minor series with the Fredholm series
of the explicit row-compact realization. -/
theorem charPowerSeries_matrix_eq_compactOperator {ϖ : K} (hϖ₀ : ϖ ≠ 0)
    (hϖ₁ : ‖ϖ‖ < 1) :
    (matrix ϖ).charPowerSeries = (compactOperator ϖ hϖ₁).matrixCoeff.charPowerSeries := by
  rw [matrixCoeff_compactOperator]
  exact Matrix.charPowerSeries_eq_of_diagonal_intertwining
    (fun i ↦ IsRegular.of_ne_zero (pow_ne_zero i hϖ₀)) (diagonal_intertwining ϖ)

end TauCeti.TwoSidedExample
