/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Rank bounds for changes to sample covariance data

Changing the data matrix by rank `r` changes its sample covariance by rank at most `2r`.
In particular, subtracting any common vector from the columns gives a rank-two change.
Empirical centering is sharper: the covariance correction is the outer product of the
empirical mean, so has rank at most one. These bounds need neither moment nor norm estimates
and allow empty samples.

## References

* Z. Bai, J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices* (2010),
  §3.3 and Theorem A.43.
-/

public section

namespace Matrix

variable {𝕜 p n : Type*} [RCLike 𝕜] [Fintype p] [Fintype n]

/-- The sample covariance rank inequality, normalized by the number of samples even when
that number is zero. -/
theorem rank_sampleCovariance_sub_le (X Y : Matrix p n 𝕜) :
    (sampleCovariance X - sampleCovariance Y).rank ≤ 2 * (X - Y).rank := by
  classical
  rw [sampleCovariance_def, sampleCovariance_def, ← smul_sub, ← smul_one_mul]
  exact (rank_mul_le_right _ _).trans
    (rank_mul_conjTranspose_self_sub_mul_conjTranspose_self_le X Y)

/-- Subtracting an arbitrary common vector from the columns changes the sample covariance
by rank at most two. No bound on the center is required. -/
theorem rank_sampleCovariance_sub_const_le_two (X : Matrix p n 𝕜) (u : p → 𝕜) :
    (sampleCovariance X - sampleCovariance (of fun i j ↦ X i j - u i)).rank ≤ 2 := by
  have hdiff : X - of (fun i j ↦ X i j - u i) = vecMulVec u (fun _ : n ↦ 1) := by
    ext i j
    simp [vecMulVec_apply]
  exact (rank_sampleCovariance_sub_le _ _).trans (by
    rw [hdiff]
    exact Nat.mul_le_mul_left 2 (rank_vecMulVec_le _ _))

/-- Empirical centering changes the sample covariance by rank at most one. -/
theorem rank_sampleCovariance_sub_colMean_le_one (X : Matrix p n 𝕜) :
    (sampleCovariance X - sampleCovariance
      (of fun i j ↦ X i j - (TauCeti.finiteMean 𝕜 X.col) i)).rank ≤ 1 := by
  rw [sampleCovariance_sub_colMean, sub_sub_cancel]
  exact rank_vecMulVec_le _ _

end Matrix
