/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecificLimits.Multiplicative
public import TauCeti.Probability.Distributions.Poisson.Basic

/-!
# Poisson laws from microscopic probabilities

A convolution semigroup of probability laws on `ℕ` is Poisson if its one-occurrence
probability is `λh + o(h)` and its multiple-occurrence probability is `o(h)` at zero.
We state these conditions as limits of probabilities divided by positive elapsed time.
The proof bounds the error in the probability-generating function by the multiple-occurrence
probability and subdivides time using the convolution law.

## References

* Vincent Tassion, *Applied Stochastic Processes*, ETH Zürich, Spring 2025, Chapter 6,
  microscopic characterization of the Poisson process.
-/

public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace TauCeti.Probability

/-- The microscopic one- and multiple-occurrence probabilities determine a convolution
semigroup on `ℕ`: its time-`t` law is Poisson with parameter `λt`. Zero rate is allowed. -/
theorem eq_poissonMeasure_of_small_time (μ : ℝ≥0 → Measure ℕ)
    [∀ t, IsProbabilityMeasure (μ t)] (r : ℝ≥0)
    (h0 : μ 0 = Measure.dirac 0)
    (hadd : ∀ s t, μ (s + t) = μ s ∗ μ t)
    (h1 : Tendsto (fun h : ℝ≥0 ↦ (μ h).real {1} / h) (𝓝[>] 0) (𝓝 (r : ℝ)))
    (h2 : Tendsto (fun h : ℝ≥0 ↦ (μ h).real (Set.Ici 2) / h) (𝓝[>] 0) (𝓝 0))
    (t : ℝ≥0) : μ t = poissonMeasure (r * t) := by
  apply measure_eq_of_pgf_eqOn
  intro z hz
  have hzabs : |z| ≤ 1 := (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)
  have herr : Tendsto (fun h : ℝ≥0 ↦
      (pgf id (μ h) z - 1 - (z - 1) * (μ h).real {1}) / h) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using h2.const_mul 2)
    filter_upwards with h
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h.coe_nonneg]
    simpa [mul_div_assoc] using div_le_div_of_nonneg_right
      ((μ h).abs_pgf_sub_one_sub_mul_le hzabs) h.coe_nonneg
  have hslope : Tendsto (fun h : ℝ≥0 ↦ (pgf id (μ h) z - 1) / h)
      (𝓝[>] 0) (𝓝 ((z - 1) * r)) := by
    convert herr.add (h1.const_mul (z - 1)) using 1
    · ext h
      ring
    · simp
  have hexp := eq_exp_mul_of_add_eq_mul_of_tendsto_div
    (f := fun s ↦ pgf id (μ s) z)
    (by simp [h0, pgf_def])
    (fun s u ↦ by rw [hadd, Measure.pgf_conv_of_abs_le_one _ _ hzabs]) hslope t
  rw [hexp, pgf_poissonMeasure]
  congr 1
  push_cast
  ring

end TauCeti.Probability
