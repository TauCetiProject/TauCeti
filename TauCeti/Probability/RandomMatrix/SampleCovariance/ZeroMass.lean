/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SampleCovariance.Rank
public import TauCeti.Probability.Distributions.MarchenkoPastur.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# The zero atom of sample covariance spectra

The rank of the data matrix determines the mass of the covariance spectrum at zero.
At a Marchenko–Pastur limit the dimension bound on rank and the closed-set
Portmanteau bound give convergence of the mass at zero, including when it is nonzero.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), §2.2.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped NNReal Topology

namespace TauCeti.Probability

open Matrix

/-- If the sample covariance spectra have a weak Marchenko–Pastur limit and the aspect ratios
tend to its parameter, their exact masses at zero converge to its atom. This also holds when
the limiting aspect ratio is zero or one. -/
theorem tendsto_spectralMeasure_sampleCovariance_singleton_zero
    {ι 𝕜 : Type*} [RCLike 𝕜] {l : Filter ι} {p n : ι → ℕ}
    [∀ i, NeZero (p i)]
    (X : (i : ι) → Matrix (Fin (p i)) (Fin (n i)) 𝕜)
    {y : ℝ≥0} (hy : Tendsto (fun i ↦ (p i : ℝ≥0) / n i) l (𝓝 y))
    (h : Tendsto (fun i ↦ (sampleCovariance (X i)).spectralMeasure
      (isHermitian_sampleCovariance _)) l (𝓝 (marchenkoPastur y).toProbabilityMeasure)) :
    Tendsto (fun i ↦ ((sampleCovariance (X i)).spectralMeasure
      (isHermitian_sampleCovariance _) : Measure ℝ) {0}) l (𝓝 (marchenkoPastur y {0})) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  refine tendsto_of_le_liminf_of_limsup_le ?_
    (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h isClosed_singleton)
  by_cases hy₀ : y = 0
  · simp [hy₀]
  have hy' : Tendsto (fun i ↦ (p i : ℝ) / n i) l (𝓝 (y : ℝ)) := by
    simpa only [Function.comp_def, NNReal.coe_div, NNReal.coe_natCast] using
      (NNReal.continuous_coe.tendsto y).comp hy
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((hy'.sub_const 1).div hy' (by exact_mod_cast hy₀))
  rw [marchenkoPastur_singleton_zero, ← hlim.liminf_eq]
  refine liminf_le_liminf (.of_forall fun i ↦ ?_)
  have hp : (p i : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (p i)
  by_cases hn : n i = 0
  · simp [Pi.div_apply, hn]
  have hn' : (n i : ℝ) ≠ 0 := by exact_mod_cast hn
  have he : ((p i : ℝ) / n i - 1) / ((p i : ℝ) / n i) = ((p i : ℝ) - n i) / p i := by
    field_simp
  simpa only [Function.comp_def, Pi.div_apply, Fintype.card_fin, he] using
    ofReal_sub_div_le_spectralMeasure_sampleCovariance_singleton_zero (X i)

end TauCeti.Probability
