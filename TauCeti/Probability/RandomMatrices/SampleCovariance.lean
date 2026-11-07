/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Sample covariance matrices

The sample covariance matrix of a rectangular data matrix is its row Gram matrix, normalized by
the number of samples.
-/

public section
noncomputable section

namespace TauCeti.Probability

open Matrix

/-- The sample covariance matrix of `X`, whose columns are the observations. -/
def sampleCovariance {p q : Type*} [Fintype q] {𝕜 : Type*}
    [RCLike 𝕜] (X : Matrix p q 𝕜) : Matrix p p 𝕜 :=
  (Fintype.card q : 𝕜)⁻¹ • (X * Xᴴ)

/-- A sample covariance matrix is Hermitian. -/
theorem sampleCovariance_isHermitian {p q : Type*} [Fintype q]
    {𝕜 : Type*} [RCLike 𝕜] (X : Matrix p q 𝕜) :
    (sampleCovariance X).IsHermitian := by
  apply (Matrix.isHermitian_mul_conjTranspose_self X).smul
  simp [IsSelfAdjoint]

end TauCeti.Probability
