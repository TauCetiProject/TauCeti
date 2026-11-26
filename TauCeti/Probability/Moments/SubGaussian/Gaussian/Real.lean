/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Centred real Gaussian variables are sub-Gaussian

A real random variable with law `gaussianReal 0 v` is sub-Gaussian with variance proxy `v`: its
moment-generating function is exactly `exp (v * t ^ 2 / 2)`.

## Main results

* `ProbabilityTheory.HasLaw.hasSubgaussianMGF`

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §2.5.
-/

public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- A random variable with centred Gaussian law `gaussianReal 0 v` is `v`-sub-Gaussian. -/
theorem HasLaw.hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ := by
  rw [← HasSubgaussianMGF.id_map_iff hX.aemeasurable, hX.map_eq]
  exact ⟨integrable_exp_mul_gaussianReal, fun t ↦ by simp [mgf_id_gaussianReal]⟩

end ProbabilityTheory
