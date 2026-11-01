/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Analysis.Matrix.SampleSecondMoment

/-!
# Sample covariance matrices

The sample covariance matrix `X Xᴴ / n` of a `p × n` data matrix `X`, whose `n` columns are the
samples.

## Main declarations

* `Matrix.sampleCovariance`: the sample covariance matrix `X Xᴴ / n`.
* `Matrix.sampleCovariance_apply`: its entries.
* `Matrix.sampleCovariance_eq_sampleSecondMoment`: it is the empirical second-moment matrix
  (`TauCeti.sampleSecondMoment`) of the columns of `X`.
* `Matrix.isHermitian_sampleCovariance`: the sample covariance matrix is Hermitian.
* `Matrix.posSemidef_sampleCovariance`: the sample covariance matrix is positive semidefinite.
-/

public section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {p n : Type*} [Fintype n]

/-- The sample covariance matrix `X Xᴴ / n` of a `p × n` data matrix `X`, with the `n` columns
as samples. When `n` is empty it is `0`. -/
def sampleCovariance (X : Matrix p n 𝕜) : Matrix p p 𝕜 :=
  (1 / (Fintype.card n : ℝ)) • (X * Xᴴ)

theorem sampleCovariance_def (X : Matrix p n 𝕜) :
    sampleCovariance X = (1 / (Fintype.card n : ℝ)) • (X * Xᴴ) :=
  (rfl)

/-- The `(i, j)` entry of the sample covariance matrix. -/
@[simp]
theorem sampleCovariance_apply (X : Matrix p n 𝕜) (i j : p) :
    sampleCovariance X i j = (1 / (Fintype.card n : ℝ)) • ∑ k, X i k * star (X j k) := by
  simp [sampleCovariance_def, Matrix.mul_apply]

/-- The sample covariance matrix of `X` is the empirical second-moment matrix of its columns. -/
theorem sampleCovariance_eq_sampleSecondMoment (X : Matrix p n 𝕜) :
    sampleCovariance X = TauCeti.sampleSecondMoment (fun k i ↦ X i k) := by
  ext i j
  simp [TauCeti.finiteMean_eq_inv_smul_sum, RCLike.real_smul_eq_coe_mul]

/-- The sample covariance matrix is Hermitian. -/
theorem isHermitian_sampleCovariance (X : Matrix p n 𝕜) : (sampleCovariance X).IsHermitian := by
  rw [sampleCovariance_eq_sampleSecondMoment]
  exact TauCeti.isHermitian_sampleSecondMoment _

/-- The sample covariance matrix is positive semidefinite. -/
theorem posSemidef_sampleCovariance [Finite p] (X : Matrix p n 𝕜) :
    (sampleCovariance X).PosSemidef := by
  rw [sampleCovariance_eq_sampleSecondMoment]
  exact TauCeti.posSemidef_sampleSecondMoment _

/-- The sample covariance of the `1 × 2` data matrix `(1, i)` is `(1 + 1) / 2 = 1`. -/
example : sampleCovariance !![(1 : ℂ), Complex.I] = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp
  norm_num

end Matrix
