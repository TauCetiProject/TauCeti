/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Basic

/-!
# Sample covariance matrices

The sample covariance matrix `X Xᴴ / n` of a `p × n` data matrix `X`, whose `n` columns are the
samples.

## Main declarations

* `TauCeti.Probability.sampleCovariance`: the sample covariance matrix `X Xᴴ / n`.
* `TauCeti.Probability.isHermitian_sampleCovariance`: the sample covariance matrix is Hermitian.
* `TauCeti.Probability.posSemidef_sampleCovariance`: the sample covariance matrix is positive
  semidefinite.
-/

public section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace TauCeti

namespace Probability

variable {𝕜 : Type*} [RCLike 𝕜] {p n : Type*} [Fintype n]

/-- The sample covariance matrix `X Xᴴ / n` of a `p × n` data matrix `X`, with the `n` columns
as samples. When `n` is empty it is `0`. -/
def sampleCovariance (X : Matrix p n 𝕜) : Matrix p p 𝕜 :=
  (1 / (Fintype.card n : ℝ)) • (X * Xᴴ)

/-- The sample covariance matrix is Hermitian. -/
theorem isHermitian_sampleCovariance (X : Matrix p n 𝕜) : (sampleCovariance X).IsHermitian :=
  (isHermitian_mul_conjTranspose_self X).smul (.all _)

/-- The sample covariance matrix is positive semidefinite. -/
theorem posSemidef_sampleCovariance [Finite p] (X : Matrix p n 𝕜) :
    (sampleCovariance X).PosSemidef :=
  have := Fintype.ofFinite p
  (posSemidef_self_mul_conjTranspose X).smul (by positivity)

/-- The sample covariance of the `1 × 2` data matrix `(1, i)` is `(1 + 1) / 2 = 1`. -/
example : sampleCovariance !![(1 : ℂ), Complex.I] = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp only [sampleCovariance, Matrix.smul_apply]
  simp [Matrix.mul_apply]
  norm_num

end Probability

end TauCeti
