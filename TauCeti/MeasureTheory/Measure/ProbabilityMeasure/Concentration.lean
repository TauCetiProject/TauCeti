/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Concentration at a point from a vanishing second moment

Probability measures converge weakly to a Dirac mass if their mean squared distance from
that point tends to zero. This turns quantitative second-moment estimates into weak limits,
without needing a common probability space for the measures.

The proof uses Mathlib's bounded Lipschitz characterization of weak convergence and Hölder's
inequality to bound the first distance moment by the square root of the second.
-/

public section

open Filter MeasureTheory Topology

namespace MeasureTheory.ProbabilityMeasure

/-- Vanishing mean squared distance from a point implies weak convergence to its Dirac mass. -/
theorem tendsto_dirac_of_integral_dist_sq_tendsto_zero {E ι : Type*}
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {L : Filter ι} [L.IsCountablyGenerated] {μ : ι → ProbabilityMeasure E} {x : E}
    (hmem : ∀ i, MemLp (fun y ↦ dist y x) 2 (μ i : Measure E))
    (hlim : Tendsto (fun i ↦ ∫ y, dist y x ^ 2 ∂(μ i : Measure E)) L (𝓝 0)) :
    Tendsto μ L (𝓝 (⟨Measure.dirac x, inferInstance⟩ : ProbabilityMeasure E)) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.2
  rintro f hbound ⟨K, hK⟩
  let g : BoundedContinuousFunction E ℝ := ⟨⟨f, hK.continuous⟩, hbound⟩
  have hf (i : ι) : Integrable f (μ i : Measure E) :=
    g.integrable (μ := (μ i : Measure E))
  have hfirst (i : ι) :
      ∫ y, dist y x ∂(μ i : Measure E) ≤
        Real.sqrt (∫ y, dist y x ^ 2 ∂(μ i : Measure E)) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ fun y ↦ dist_nonneg (x := y) (y := x))
      (ae_of_all _ fun _ ↦ (zero_le_one : (0 : ℝ) ≤ 1))
      (by simpa using hmem i)
      (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : E ↦ (1 : ℝ)) 2 (μ i)))
    simpa only [mul_one, Real.one_rpow, integral_const, probReal_univ, one_smul,
      one_mul, one_pow, Real.rpow_two, ← one_div, ← Real.sqrt_eq_rpow,
      Real.sqrt_one] using h
  have hdist (i : ι) :
      dist (∫ y, f y ∂(μ i : Measure E)) (f x) ≤
        K * Real.sqrt (∫ y, dist y x ^ 2 ∂(μ i : Measure E)) := by
    calc
      _ = ‖∫ y, (f y - f x) ∂(μ i : Measure E)‖ := by
        rw [integral_sub (hf i) (integrable_const _), integral_const,
          probReal_univ, one_smul, Real.dist_eq, Real.norm_eq_abs]
      _ ≤ ∫ y, K * dist y x ∂(μ i : Measure E) :=
        norm_integral_le_of_norm_le (((hmem i).integrable (by norm_num)).const_mul (K : ℝ))
          (ae_of_all _ fun y ↦ by simpa [Real.dist_eq, Real.norm_eq_abs] using hK.dist_le_mul y x)
      _ ≤ K * Real.sqrt (∫ y, dist y x ^ 2 ∂(μ i : Measure E)) := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hfirst i) K.coe_nonneg
  have hzero : Tendsto (fun i ↦ K * Real.sqrt
      (∫ y, dist y x ^ 2 ∂(μ i : Measure E))) L (𝓝 0) := by
    simpa using hlim.sqrt.const_mul (K : ℝ)
  simpa only [ProbabilityMeasure.coe_mk, integral_dirac' _ _ hK.continuous.stronglyMeasurable] using
    (tendsto_iff_dist_tendsto_zero.2
      (squeeze_zero (fun _ ↦ dist_nonneg) hdist hzero))

end MeasureTheory.ProbabilityMeasure
