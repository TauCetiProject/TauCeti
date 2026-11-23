/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# Fixed vectors of the exponential of a small matrix

For a square matrix `a` over `ℝ` or `ℂ` whose operator norm `‖a‖` is less than `log 2`, the
vectors fixed by `exp a` are the kernel of `a`. This is the matrix form of
`ContinuousLinearMap.exp_apply_eq_self_iff`, read through `Matrix.toEuclideanCLM`.

The norm is the operator norm `Matrix.Norms.L2Operator` for the Euclidean norm.

## Main results

* `Matrix.exp_mulVec_eq_self_iff`: if `‖a‖ < log 2`, then `exp a *ᵥ v = v ↔ a *ᵥ v = 0`.
-/

public section

open NormedSpace

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] [DecidableEq m]

open scoped Matrix.Norms.L2Operator in
/-- **The fixed vectors of a small matrix exponential are the kernel.** For `‖a‖ < log 2`, the
vectors fixed by `exp a` are the kernel of `a`. This is `ContinuousLinearMap.exp_apply_eq_self_iff`
read through `Matrix.toEuclideanCLM`. -/
theorem exp_mulVec_eq_self_iff {a : Matrix m m 𝕜} (ha : ‖a‖ < Real.log 2) {v : m → 𝕜} :
    exp a *ᵥ v = v ↔ a *ᵥ v = 0 := by
  have h := ContinuousLinearMap.exp_apply_eq_self_iff (𝕜 := 𝕜)
    (B := toEuclideanCLM (n := m) (𝕜 := 𝕜) a) (x := WithLp.toLp 2 v)
    (by rwa [← cstar_norm_def])
  let +nondep : NormedAlgebra ℚ (Matrix m m 𝕜) := .restrictScalars ℚ 𝕜 _
  rw [← NormedSpace.map_exp _ continuous_toEuclideanCLM, toEuclideanCLM_toLp, toEuclideanCLM_toLp,
    ← WithLp.toLp_zero 2, (WithLp.toLp_injective 2).eq_iff, (WithLp.toLp_injective 2).eq_iff] at h
  exact h

end Matrix
