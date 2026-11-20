/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SampleCovariance.Rank
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
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

namespace Matrix

/-- At least the positive part of the excess row fraction of a rectangular sample is at zero
in its sample covariance spectral measure. This includes samples with no columns. -/
theorem ofReal_sub_div_le_spectralMeasure_sampleCovariance_singleton_zero
    {p n 𝕜 : Type*} [Fintype p] [DecidableEq p] [Nonempty p] [Fintype n] [RCLike 𝕜]
    (X : Matrix p n 𝕜) :
    ENNReal.ofReal (((Fintype.card p : ℝ) - Fintype.card n) / Fintype.card p) ≤
      ((sampleCovariance X).spectralMeasure (isHermitian_sampleCovariance _) : Measure ℝ) {0} := by
  let μ : Measure ℝ := (sampleCovariance X).spectralMeasure (isHermitian_sampleCovariance _)
  have hr : X.rank ≤ Fintype.card p := X.rank_le_card_height
  have hr' : (X.rank : ℝ) ≤ Fintype.card n := by exact_mod_cast X.rank_le_card_width
  -- Express the mass as a real number before comparing it to the signed dimension bound.
  have hμ : (μ {0}).toReal = ((Fintype.card p : ℝ) - X.rank) / Fintype.card p := by
    simp only [μ, spectralMeasure_apply_singleton_zero, rank_sampleCovariance,
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_sub hr]
    rw [div_eq_inv_mul]
  suffices ENNReal.ofReal (((Fintype.card p : ℝ) - Fintype.card n) / Fintype.card p) ≤ μ {0}
    from this
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {0}), hμ]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    (sub_le_sub_left hr' _) (Nat.cast_nonneg _))

end Matrix

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
