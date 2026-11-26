/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Rank bounds for changes to sample covariance data

Changing the data matrix by rank `r` changes its sample covariance by rank at most `2r`.
In particular, subtracting any common vector from the columns gives a rank-two change.
Empirical centering is sharper: the covariance correction is the outer product of the
empirical mean, so has rank at most one. These bounds need neither moment nor norm estimates
and allow empty samples. The rank of the data also bounds the mass at zero of the sample
covariance spectrum.

## References

* Z. Bai, J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices* (2010),
  §3.3 and Theorem A.43.
-/

public section

namespace Matrix

open MeasureTheory

section Rank

variable {𝕜 p n : Type*} [RCLike 𝕜] [Finite p] [Fintype n]

open scoped ComplexOrder in
/-- The sample covariance matrix has the same rank as the sample data matrix. -/
@[simp]
theorem rank_sampleCovariance (X : Matrix p n 𝕜) :
    (sampleCovariance X).rank = X.rank := by
  cases isEmpty_or_nonempty n
  · have hX : X.rank = 0 := Nat.eq_zero_of_le_zero (by simpa using X.rank_le_card_width)
    simp [sampleCovariance_def, hX]
  have hcard : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hscale : ((1 / (Fintype.card n : ℝ) : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (one_div_ne_zero hcard)
  rw [sampleCovariance_def, RCLike.real_smul_eq_coe_smul (K := 𝕜),
    rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hscale),
    rank_self_mul_conjTranspose]

/-- The sample covariance rank inequality, normalized by the number of samples even when
that number is zero. -/
theorem rank_sampleCovariance_sub_le (X Y : Matrix p n 𝕜) :
    (sampleCovariance X - sampleCovariance Y).rank ≤ 2 * (X - Y).rank := by
  classical
  have := Fintype.ofFinite p
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

end Rank

/-- At least the positive part of the excess row fraction of a rectangular sample is at zero
in its sample covariance spectral measure. This includes samples with no columns. -/
theorem ofReal_sub_div_le_spectralMeasure_sampleCovariance_singleton_zero
    {p n 𝕜 : Type*} [Fintype p] [DecidableEq p] [Nonempty p] [Fintype n] [RCLike 𝕜]
    (X : Matrix p n 𝕜) :
    ENNReal.ofReal (((Fintype.card p : ℝ) - Fintype.card n) / Fintype.card p) ≤
      ((sampleCovariance X).spectralMeasure (isHermitian_sampleCovariance _) : Measure ℝ) {0} := by
  set μ := ((sampleCovariance X).spectralMeasure (isHermitian_sampleCovariance _) : Measure ℝ)
  have hr : X.rank ≤ Fintype.card p := X.rank_le_card_height
  have hr' : (X.rank : ℝ) ≤ Fintype.card n := by exact_mod_cast X.rank_le_card_width
  -- Express the mass as a real number before comparing it to the signed dimension bound.
  have hμ : (μ {0}).toReal = ((Fintype.card p : ℝ) - X.rank) / Fintype.card p := by
    simp only [μ, spectralMeasure_apply_singleton_zero, rank_sampleCovariance,
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_sub hr]
    rw [div_eq_inv_mul]
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {0}), hμ]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    (sub_le_sub_left hr' _) (Nat.cast_nonneg _))

end Matrix
