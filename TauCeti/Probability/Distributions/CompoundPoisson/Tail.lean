/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CompoundPoisson.Basic
public import TauCeti.MeasureTheory.Group.Convolution.Tail

/-!
# Power-law tails of compound Poisson laws

A compound Poisson sum inherits a finite power-law right-tail constant from its jump law,
multiplied by the Poisson rate. Reflection gives the corresponding left-tail statement.
The jumps can have either sign, and no moment or opposite-tail assumption is imposed.
In particular the theorem applies to finite-intensity large-jump components of stable laws.

The underlying random-sum theorem uses a polynomial union bound and the finite moments
of the Poisson count, including rate zero.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology ENNReal NNReal

namespace TauCeti.Probability

/-- A power-law right-tail constant of the jump distribution is multiplied by the rate
under compound Poisson summation, including rate zero and zero tail constants. -/
theorem tendsto_rpow_mul_compoundPoissonMeasure_real_Ioi
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (r : ℝ≥0) {α C : ℝ} (hα : 0 < α)
    (hμ : Tendsto (fun x : ℝ ↦ x ^ α * μ.real (Ioi x)) atTop (𝓝 C)) :
    Tendsto (fun x : ℝ ↦ x ^ α * (compoundPoissonMeasure r μ).real (Ioi x)) atTop
      (𝓝 ((r : ℝ) * C)) := by
  simpa only [compoundPoissonMeasure_def, integral_natCast_poissonMeasure] using
    Measure.tendsto_rpow_mul_bind_convolutionPower_real_Ioi hα hμ
      (integrable_natCast_rpow_poissonMeasure r (by linarith : 0 ≤ α + 1))

/-- A power-law left-tail constant of the jump distribution is multiplied by the rate
under compound Poisson summation, without a right-tail or moment assumption. -/
theorem tendsto_rpow_mul_compoundPoissonMeasure_real_Iio_neg
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (r : ℝ≥0) {α C : ℝ} (hα : 0 < α)
    (hμ : Tendsto (fun x : ℝ ↦ x ^ α * μ.real (Iio (-x))) atTop (𝓝 C)) :
    Tendsto (fun x : ℝ ↦ x ^ α * (compoundPoissonMeasure r μ).real (Iio (-x))) atTop
      (𝓝 ((r : ℝ) * C)) := by
  have h := tendsto_rpow_mul_compoundPoissonMeasure_real_Ioi
    (μ := μ.map (fun y ↦ -y)) r hα (by simpa only [Measure.map_neg_real_Ioi] using hμ)
  rw [← map_neg_compoundPoissonMeasure] at h
  simpa only [Measure.map_neg_real_Ioi] using h

end TauCeti.Probability
