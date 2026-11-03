/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Portmanteau
import TauCeti.Probability.Moments.Variance

/-!
# Weak limits from vanishing second moments

Probability measures `μ i` converge weakly to `ν` if every bounded Lipschitz test function can be
replaced, under `μ i`, by a function with the same integral as under `ν`, up to a pointwise error
whose second moment tends to zero. This turns quantitative second-moment estimates into weak
limits, without needing a common probability space for the measures.

The main special case is concentration at a point: probability measures converge weakly to a
Dirac mass if their mean squared distance from that point tends to zero.

The proof uses Mathlib's bounded Lipschitz characterization of weak convergence and bounds a first
moment by the square root of the second, which is the nonnegativity of the variance.
-/

public section

open Filter MeasureTheory Topology
open scoped NNReal

namespace MeasureTheory.ProbabilityMeasure

/-- Probability measures `μ i` converge weakly to `ν` if each bounded `K`-Lipschitz function `f`
is within `K * d i` of a `μ i`-integrable function whose `μ i`-integral is the `ν`-integral of
`f`, and the second moments of the errors `d i` under `μ i` tend to zero. -/
theorem tendsto_of_lipschitz_approx_of_integral_sq_tendsto_zero {E ι : Type*}
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {L : Filter ι} [L.IsCountablyGenerated] {μ : ι → ProbabilityMeasure E}
    {ν : ProbabilityMeasure E} {d : ι → E → ℝ}
    (hmem : ∀ i, MemLp (d i) 2 (μ i : Measure E))
    (hlim : Tendsto (fun i ↦ ∫ y, d i y ^ 2 ∂(μ i : Measure E)) L (𝓝 0))
    (happrox : ∀ (f : E → ℝ) (K : ℝ≥0), (∃ C, ∀ x y, dist (f x) (f y) ≤ C) →
      LipschitzWith K f → ∀ i, ∃ h : E → ℝ, Integrable h (μ i : Measure E) ∧
        ∫ y, h y ∂(μ i : Measure E) = ∫ y, f y ∂(ν : Measure E) ∧
        ∀ᵐ y ∂(μ i : Measure E), |f y - h y| ≤ K * d i y) :
    Tendsto μ L (𝓝 ν) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.2
  rintro f hbound ⟨K, hK⟩
  let g : BoundedContinuousFunction E ℝ := ⟨⟨f, hK.continuous⟩, hbound⟩
  have hdist (i : ι) :
      dist (∫ y, f y ∂(μ i : Measure E)) (∫ y, f y ∂(ν : Measure E)) ≤
        K * √(∫ y, d i y ^ 2 ∂(μ i : Measure E)) := by
    obtain ⟨h, hh, hint, hle⟩ := happrox f K hbound hK i
    have hf : Integrable f (μ i : Measure E) := g.integrable _
    calc
      _ = ‖∫ y, (f y - h y) ∂(μ i : Measure E)‖ := by
        rw [integral_sub hf hh, hint, Real.dist_eq, Real.norm_eq_abs]
      _ ≤ ∫ y, K * d i y ∂(μ i : Measure E) :=
        norm_integral_le_of_norm_le (((hmem i).integrable (by norm_num)).const_mul (K : ℝ))
          (hle.mono fun y hy ↦ by rwa [Real.norm_eq_abs])
      _ ≤ K * √(∫ y, d i y ^ 2 ∂(μ i : Measure E)) := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (integral_le_sqrt_integral_sq (hmem i)) K.coe_nonneg
  have hzero : Tendsto (fun i ↦ K * √(∫ y, d i y ^ 2 ∂(μ i : Measure E))) L (𝓝 0) := by
    simpa using hlim.sqrt.const_mul (K : ℝ)
  exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg) hdist hzero)

/-- Vanishing mean squared distance from a point implies weak convergence to its Dirac mass. -/
theorem tendsto_dirac_of_integral_dist_sq_tendsto_zero {E ι : Type*}
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {L : Filter ι} [L.IsCountablyGenerated] {μ : ι → ProbabilityMeasure E} {x : E}
    (hmem : ∀ i, MemLp (fun y ↦ dist y x) 2 (μ i : Measure E))
    (hlim : Tendsto (fun i ↦ ∫ y, dist y x ^ 2 ∂(μ i : Measure E)) L (𝓝 0)) :
    Tendsto μ L (𝓝 (⟨Measure.dirac x, inferInstance⟩ : ProbabilityMeasure E)) := by
  refine tendsto_of_lipschitz_approx_of_integral_sq_tendsto_zero hmem hlim
    fun f K _ hK i ↦ ⟨fun _ ↦ f x, integrable_const _, ?_, ae_of_all _ fun y ↦ ?_⟩
  · simp [integral_dirac' _ _ hK.continuous.stronglyMeasurable]
  · simpa [Real.dist_eq] using hK.dist_le_mul y x

end MeasureTheory.ProbabilityMeasure
