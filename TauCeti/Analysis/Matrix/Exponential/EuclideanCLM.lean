/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# The exponential of a matrix as an operator on Euclidean space

The operator `Matrix.toEuclideanCLM (exp M)` of the exponential of a square matrix `M` over `ℝ` or
`ℂ` is the exponential of the operator `Matrix.toEuclideanCLM M`
(`Matrix.toEuclideanCLM_exp`): `Matrix.toEuclideanCLM` is a continuous algebra homomorphism, so
it commutes with the exponential series.

## Main results

* `Matrix.toEuclideanCLM_exp`: `toEuclideanCLM (exp M) = exp (toEuclideanCLM M)`.
-/

public section

open NormedSpace

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The operator of a matrix exponential.** The operator on Euclidean space of the exponential
of a square matrix is the exponential of its operator. -/
theorem toEuclideanCLM_exp (M : Matrix n n 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) (exp M) = exp (toEuclideanCLM (n := n) (𝕜 := 𝕜) M) := by
  open scoped Matrix.Norms.L2Operator in
  let +nondep : NormedAlgebra ℚ (Matrix n n 𝕜) := .restrictScalars ℚ 𝕜 _
  exact map_exp _ continuous_toEuclideanCLM M

end Matrix
