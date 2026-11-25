/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import TauCeti.Probability.Moments.PaleyZygmund
import TauCeti.Probability.Moments.SubGaussian.Basic
import TauCeti.Probability.Moments.SubGaussian.ExponentialMoments

/-!
# Anti-concentration of sub-Gaussian random variables

A sub-Gaussian random variable `X` with variance proxy `c` and second moment `E X² ≥ 1` is not
concentrated near any point: for every `v` and every radius `|r| ≤ 1`,

`P(|X - v| ≤ r) ≤ 1 - (1 - r²)² / (256 √2 c²)`

(`ProbabilityTheory.HasSubgaussianMGF.measureReal_abs_sub_le_le_one_sub_div`). It combines the
fourth-moment bound `E X⁴ ≤ 32 √2 c²`
(`ProbabilityTheory.HasSubgaussianMGF.integral_pow_four_le`) with the Paley–Zygmund
anti-concentration bound `MeasureTheory.MemLp.measureReal_abs_sub_le_le_one_sub_div`. With the
radius `r = 1 / 2` it shows that the law of `2 X` gives mass at most `1 - 9 / (4096 √2 c²)` to
every open interval of length `2`
(`ProbabilityTheory.HasSubgaussianMGF.measureReal_map_two_mul_ball_le`). This is the hypothesis on
the entries of small-ball estimates through the least common denominator.

## References

* M. Rudelson and R. Vershynin, *The smallest singular value of a random rectangular matrix*,
  Communications on Pure and Applied Mathematics 62 (2009), Lemma 3.2 of the preprint
  arXiv:0802.3956v4.
-/

public section

open MeasureTheory Metric
open scoped NNReal

namespace ProbabilityTheory.HasSubgaussianMGF

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
  {c : ℝ≥0}

/-- **Anti-concentration of sub-Gaussian variables.** A sub-Gaussian random variable with
variance proxy `c` and second moment at least `1` puts mass at most
`1 - (1 - r²)² / (256 √2 c²)` in every closed interval `[v - r, v + r]` of radius `|r| ≤ 1`. -/
theorem measureReal_abs_sub_le_le_one_sub_div (h : HasSubgaussianMGF X c μ)
    (hvar : 1 ≤ ∫ ω, X ω ^ 2 ∂μ) (v : ℝ) {r : ℝ} (hr : |r| ≤ 1) :
    μ.real {ω | |X ω - v| ≤ r} ≤ 1 - (1 - r ^ 2) ^ 2 / (256 * √2 * (c : ℝ) ^ 2) := by
  have h4 := (h.memLp 4).measureReal_abs_sub_le_le_one_sub_div h.integral_eq_zero hvar
    h.integral_pow_four_le v hr
  rwa [(by ring : 8 * (32 * √2 * (c : ℝ) ^ 2) = 256 * √2 * (c : ℝ) ^ 2)] at h4

/-- **Concentration of the law of `2 X`.** For a sub-Gaussian random variable `X` with variance
proxy `c` and second moment at least `1`, the law of `2 X` gives mass at most
`1 - 9 / (4096 √2 c²)` to every open interval of length `2`. -/
theorem measureReal_map_two_mul_ball_le (h : HasSubgaussianMGF X c μ)
    (hvar : 1 ≤ ∫ ω, X ω ^ 2 ∂μ) (v : ℝ) :
    (μ.map fun ω ↦ 2 * X ω).real (ball v 1) ≤ 1 - 9 / (4096 * √2 * (c : ℝ) ^ 2) := by
  have hlaw := (hasLaw_map (h.aemeasurable.const_mul 2)).measureReal_eq (p := (· ∈ ball v 1))
    measurableSet_ball
  rw [Set.ofPred_mem_eq] at hlaw
  rw [← hlaw]
  -- `|2 X - v| < 1` forces `|X - v / 2| ≤ 1 / 2`.
  refine (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)).trans
    ((h.measureReal_abs_sub_le_le_one_sub_div hvar (v / 2) (r := 1 / 2) (by norm_num)).trans
      (le_of_eq (by norm_num [div_div]; ring)))
  simp only [Set.mem_ofPred_eq, mem_ball, Real.dist_eq] at hω ⊢
  rw [abs_le]
  constructor <;> linarith [(abs_lt.1 hω).1, (abs_lt.1 hω).2]

end ProbabilityTheory.HasSubgaussianMGF
