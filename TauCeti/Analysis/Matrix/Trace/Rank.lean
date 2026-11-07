/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.OpNorm
public import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Rank-sensitive trace bounds for matrices

The absolute value of the trace of an arbitrary real or complex matrix is at most its rank
times its Euclidean operator norm. No normality is required. This gives dimension-independent
trace estimates for low-rank differences, in particular differences of Hermitian resolvents.

The estimate is transported from
`ContinuousLinearMap.norm_traceCLM_le_finrank_range_mul` through `Matrix.toEuclideanCLM`.
-/

public section

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

open scoped Matrix.Norms.L2Operator

/-- The absolute trace is bounded by rank times Euclidean operator norm, including for
nonnormal matrices and empty index types. -/
theorem norm_trace_le_rank_mul_l2_opNorm (A : Matrix n n 𝕜) :
    ‖A.trace‖ ≤ (A.rank : ℝ) * ‖A‖ := by
  have h := (toEuclideanCLM (𝕜 := 𝕜) A).norm_traceCLM_le_finrank_range_mul
  rw [TauCeti.traceCLM_apply, coe_toEuclideanCLM_eq_toEuclideanLin,
    ← rank_eq_finrank_range_toEuclideanLin, toEuclideanLin_eq_toLin_orthonormal,
    trace_toLin_eq, l2_opNorm_toEuclideanCLM] at h
  exact h

end Matrix
