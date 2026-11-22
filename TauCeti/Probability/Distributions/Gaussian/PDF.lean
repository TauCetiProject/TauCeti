/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.Distributions.Gaussian.Real
/-!
# Density API for the real Gaussian distribution

This file connects nondegenerate real Gaussian laws to `HasPDF` and identifies `pdf` at every
variance, including the singular zero-variance boundary. It also bounds the mass of an interval
`[x - δ, x + δ]` from below by its length times the density at its point farthest from the mean;
this is the local estimate behind lower bounds for Gaussian probabilities of small balls, as in
large deviations of Gaussian laws with vanishing variance.
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
/-- The mass of `gaussianReal m w` on `[x - δ, x + δ]` is at least the length `2δ` of the interval
times the Gaussian density at distance `|x - m| + δ` from the mean. -/
theorem ofReal_mul_le_gaussianReal_Icc (m x : ℝ) (w : ℝ≥0) (δ : ℝ) :
    ENNReal.ofReal ((√(2 * π * w))⁻¹ * Real.exp (-(|x - m| + δ) ^ 2 / (2 * w)) * (2 * δ)) ≤
      gaussianReal m w (Set.Icc (x - δ) (x + δ)) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hvol : volume (Set.Icc (x - δ) (x + δ)) = ENNReal.ofReal (2 * δ) := by
    rw [Real.volume_Icc]
    ring_nf
  rw [gaussianReal_of_var_ne_zero m hw, withDensity_apply _ measurableSet_Icc, ENNReal.ofReal_mul
    (by positivity), ← hvol, ← setLIntegral_const]
  refine setLIntegral_mono (measurable_gaussianPDF m w) fun y hy => ?_
  rw [gaussianPDF_def, gaussianPDFReal_def]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
    (by positivity))
  rw [← Real.closedBall_eq_Icc] at hy
  have hy' : |y - m| ≤ |x - m| + δ := by
    calc |y - m| ≤ |y - x| + |x - m| := abs_sub_le y x m
      _ ≤ δ + |x - m| := by
        gcongr
        exact Real.dist_eq y x ▸ Metric.mem_closedBall.1 hy
      _ = |x - m| + δ := add_comm _ _
  have hsq : (y - m) ^ 2 ≤ (|x - m| + δ) ^ 2 := by
    rw [← sq_abs (y - m)]
    exact pow_le_pow_left₀ (abs_nonneg _) hy' 2
  exact div_le_div_of_nonneg_right (neg_le_neg hsq) (by positivity)
end TauCeti.Probability
