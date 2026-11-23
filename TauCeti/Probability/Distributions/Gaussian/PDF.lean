/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.Probability.Distributions.Gaussian.Basic
/-!
# Density API for the real Gaussian distribution

This file connects nondegenerate real Gaussian laws to `HasPDF` and identifies `pdf` at every
variance, including the singular zero-variance boundary. It also computes the logarithm of the
density, and bounds the mass of an interval `[x - δ, x + δ]` from below by its length times the
density at its point farthest from the mean; this is the local estimate behind lower bounds for
Gaussian probabilities of small balls, as in large deviations of Gaussian laws with vanishing
variance.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real
namespace TauCeti.Probability
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
/-- A variable with a nondegenerate Gaussian law has a density.

`v ≠ 0` is required, not merely convenient: `gaussianReal m 0` is `Measure.dirac m`, which is
singular with respect to `volume`. -/
theorem hasPDF_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX : HasLaw X (gaussianReal m v) P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_gaussianPDF m v).aemeasurable
    (by rwa [gaussianReal_of_var_ne_zero _ hv] at hX)
/-- The density of a Gaussian law is `gaussianPDF`, at **every** variance. -/
theorem pdf_eq_gaussianPDF_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal m v) P) : pdf X P =ᵐ[volume] gaussianPDF m v := by
  rw [pdf_def, hX.map_eq]
  exact rnDeriv_gaussianReal m v
/-- The logarithm of the Gaussian density is
`log (gaussianPDFReal m w y) = -log (2πw) / 2 - (y - m)² / (2w)`. At `w = 0` both sides are `0`,
since `Real.log 0 = 0` and division by `0` gives `0`. -/
theorem log_gaussianPDFReal (m : ℝ) (w : ℝ≥0) (y : ℝ) :
    Real.log (gaussianPDFReal m w y) = -Real.log (2 * π * w) / 2 - (y - m) ^ 2 / (2 * w) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [gaussianPDFReal_zero_var]
  rw [gaussianPDFReal_def, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_inv,
    Real.log_sqrt (by positivity), Real.log_exp]
  ring
/-- The mass of `gaussianReal m w` on `[x - δ, x + δ]` is at least the length `2δ` of the interval
times the Gaussian density at distance `|x - m| + δ` from the mean, written with the centred
density `gaussianPDFReal 0 w`. -/
theorem ofReal_mul_le_gaussianReal_Icc (m x : ℝ) (w : ℝ≥0) (δ : ℝ) :
    ENNReal.ofReal (gaussianPDFReal 0 w (|x - m| + δ) * (2 * δ)) ≤
      gaussianReal m w (Set.Icc (x - δ) (x + δ)) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [gaussianPDFReal_zero_var]
  have hvol : volume (Set.Icc (x - δ) (x + δ)) = ENNReal.ofReal (2 * δ) := by
    rw [Real.volume_Icc]
    ring_nf
  rw [gaussianReal_of_var_ne_zero m hw, withDensity_apply _ measurableSet_Icc,
    ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), ← hvol, ← setLIntegral_const]
  refine setLIntegral_mono (measurable_gaussianPDF m w) fun y hy => ?_
  rw [← Real.closedBall_eq_Icc] at hy
  have hy' : |y - m| ≤ |x - m| + δ := by
    calc |y - m| ≤ |y - x| + |x - m| := abs_sub_le y x m
      _ ≤ δ + |x - m| := by
        gcongr
        exact Real.dist_eq y x ▸ Metric.mem_closedBall.1 hy
      _ = |x - m| + δ := add_comm _ _
  -- Centre the density; by evenness it depends only on `|y - m|`, where it is decreasing.
  have hpdf : gaussianPDFReal m w y = gaussianPDFReal 0 w |y - m| := by
    rw [← zero_add m, ← gaussianPDFReal_sub, zero_add]
    rcases abs_choice (y - m) with h | h
    · rw [h]
    · rw [h, gaussianPDFReal_zero_neg]
  simp only [gaussianPDF_def, hpdf]
  exact ENNReal.ofReal_le_ofReal
    (antitoneOn_gaussianPDFReal 0 w (abs_nonneg _) ((abs_nonneg _).trans hy') hy')
end TauCeti.Probability
