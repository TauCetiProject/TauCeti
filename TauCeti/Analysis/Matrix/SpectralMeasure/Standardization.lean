/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Analysis.Matrix.SampleCovariance.Rank
public import TauCeti.Analysis.Matrix.SpectralMeasure.Scaling
public import TauCeti.Analysis.Matrix.SpectralMeasure.WeakConvergence

/-!
# Standardization of sample covariance spectral laws

Subtracting a common vector from every data column changes the sample covariance by rank at
most two. Subtracting the empirical column mean gives the sharper rank-one correction. Thus
both operations preserve every weak spectral limit as the row dimension tends to infinity,
regardless of the size of the subtracted vector. Combining this with a rescaling tending to
one justifies centering and variance normalization in global sample covariance laws.

The data may be real or complex, row and column dimensions may vary independently, and empty
column types are permitted. The limiting law may have atoms. The statements are deterministic
and apply pointwise to random data, even for data-dependent centers and rescaling factors.

## References

* Z. Bai, J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices* (2010),
  §3.3 and Theorem A.43.
-/

public section

open MeasureTheory Filter Topology

namespace Matrix

section DistributionFunction

variable {𝕜 p n : Type*} [RCLike 𝕜] [Fintype p] [Fintype n]
  [DecidableEq p] [Nonempty p]

/-- Common-column centering changes every value of the spectral distribution function by
at most `2 / p`, independently of the center and of the number of samples. -/
theorem abs_spectralMeasure_sampleCovariance_sub_const_Iic_le
    (X : Matrix p n 𝕜) (u : p → 𝕜) (t : ℝ) :
    |(spectralMeasure (sampleCovariance X) (isHermitian_sampleCovariance X) : Measure ℝ).real
        (Set.Iic t) -
      (spectralMeasure (sampleCovariance (of fun i j ↦ X i j - u i))
        (isHermitian_sampleCovariance _) : Measure ℝ).real (Set.Iic t)| ≤
      2 / Fintype.card p := by
  refine ((isHermitian_sampleCovariance X).abs_spectralMeasure_Iic_sub_le_rank_div_card
    (isHermitian_sampleCovariance _) t).trans ?_
  exact div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (rank_sampleCovariance_sub_const_le_two X u)) (by positivity)

/-- Empirical centering changes every value of the spectral distribution function by at
most `1 / p`, including for an empty sample. -/
theorem abs_spectralMeasure_sampleCovariance_sub_colMean_Iic_le
    (X : Matrix p n 𝕜) (t : ℝ) :
    |(spectralMeasure (sampleCovariance X) (isHermitian_sampleCovariance X) : Measure ℝ).real
        (Set.Iic t) -
      (spectralMeasure (sampleCovariance
        (of fun i j ↦ X i j - (TauCeti.finiteMean 𝕜 X.col) i))
        (isHermitian_sampleCovariance _) : Measure ℝ).real (Set.Iic t)| ≤
      1 / Fintype.card p := by
  refine ((isHermitian_sampleCovariance X).abs_spectralMeasure_Iic_sub_le_rank_div_card
    (isHermitian_sampleCovariance _) t).trans ?_
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast rank_sampleCovariance_sub_colMean_le_one X) (by positivity)

end DistributionFunction

section Convergence

variable {ι 𝕜 : Type*} [RCLike 𝕜] {p n : ι → Type*}
  [∀ i, Fintype (p i)] [∀ i, DecidableEq (p i)] [∀ i, Nonempty (p i)]
  [∀ i, Fintype (n i)] {l : Filter ι} [l.IsCountablyGenerated]
  {μ : ProbabilityMeasure ℝ}

/-- Low-rank changes to rectangular data preserve the weak limits of the sample covariance
spectral measures. The rank is compared with the row dimension. -/
theorem tendsto_spectralMeasure_sampleCovariance_iff_of_rank_sub_div_card_tendsto_zero
    (X Y : (i : ι) → Matrix (p i) (n i) 𝕜)
    (hrank : Tendsto (fun i ↦ ((X i - Y i).rank : ℝ) / Fintype.card (p i)) l (𝓝 0)) :
    Tendsto (fun i ↦ (sampleCovariance (X i)).spectralMeasure
      (isHermitian_sampleCovariance _)) l (𝓝 μ) ↔
    Tendsto (fun i ↦ (sampleCovariance (Y i)).spectralMeasure
      (isHermitian_sampleCovariance _)) l (𝓝 μ) := by
  apply tendsto_spectralMeasure_iff_of_rank_sub_div_card_tendsto_zero
  refine squeeze_zero (fun _ ↦ by positivity) (fun i ↦ ?_)
    (by simpa using hrank.const_mul 2)
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast rank_sampleCovariance_sub_le (X i) (Y i)) (by positivity)

/-- Common-column centering preserves every weak covariance spectral limit as the row
dimension grows. The centers may be unbounded and need not converge. -/
theorem tendsto_spectralMeasure_sampleCovariance_sub_const_iff
    (X : (i : ι) → Matrix (p i) (n i) 𝕜) (u : (i : ι) → p i → 𝕜)
    (hdim : Tendsto (fun i ↦ Fintype.card (p i)) l atTop) :
    Tendsto (fun i ↦ (sampleCovariance (of fun r s ↦ X i r s - u i r)).spectralMeasure
      (isHermitian_sampleCovariance _)) l (𝓝 μ) ↔
    Tendsto (fun i ↦ (sampleCovariance (X i)).spectralMeasure
      (isHermitian_sampleCovariance _)) l (𝓝 μ) := by
  symm
  apply tendsto_spectralMeasure_iff_of_rank_sub_div_card_tendsto_zero
  refine squeeze_zero (fun _ ↦ by positivity) (fun i ↦ ?_)
    ((tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp hdim)
  exact div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (rank_sampleCovariance_sub_const_le_two (X i) (u i))) (by positivity)

/-- Centering by any common column vector and rescaling by factors whose squares tend to
one preserve weak covariance spectral convergence in both directions. In particular this
removes the variance normalization of truncated entries. Zero factors at initial indices
and arbitrary changes of sample size are allowed. -/
theorem tendsto_spectralMeasure_sampleCovariance_standardize_iff
    (X : (i : ι) → Matrix (p i) (n i) 𝕜) (u : (i : ι) → p i → 𝕜)
    (hdim : Tendsto (fun i ↦ Fintype.card (p i)) l atTop)
    {c : ι → ℝ} (hc : Tendsto (fun i ↦ c i ^ 2) l (𝓝 1)) :
    Tendsto (fun i ↦ (sampleCovariance (c i • of (fun r s ↦ X i r s - u i r))).spectralMeasure
      (isHermitian_sampleCovariance _)) l (𝓝 μ) ↔
    Tendsto (fun i ↦ (sampleCovariance (X i)).spectralMeasure
      (isHermitian_sampleCovariance _)) l (𝓝 μ) := by
  simp_rw [sampleCovariance_smul]
  exact (tendsto_spectralMeasure_smul_iff _ (fun _ ↦ isHermitian_sampleCovariance _) hc).trans
    (tendsto_spectralMeasure_sampleCovariance_sub_const_iff X u hdim)

end Convergence

end Matrix
