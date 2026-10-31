/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Sample covariance matrices

The sample covariance matrix of a complex data matrix and its Hermitian property.
-/

public section

noncomputable section

namespace Matrix

/-- The sample covariance matrix `S = XX*/n` of a `p × n` data matrix `X`. -/
def sampleCovariance {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℂ) :
    Matrix (Fin p) (Fin p) ℂ :=
  ((n : ℝ)⁻¹ : ℝ) • (X * Xᴴ)

/-- A sample covariance matrix is Hermitian. -/
theorem sampleCovariance_isHermitian {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℂ) :
    (sampleCovariance X).IsHermitian :=
  (isHermitian_mul_conjTranspose_self X).smul (IsSelfAdjoint.all _)

end Matrix
