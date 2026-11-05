/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecificLimits.Multiplicative
public import TauCeti.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Integration

/-!
# Poisson marginals from microscopic increment probabilities

A convolution semigroup of probability laws on `ℕ` is Poisson if its one-occurrence
probability is `λh + o(h)` and its multiple-occurrence probability is `o(h)` at zero.
We state these conditions as limits of probabilities divided by positive elapsed time.
The proof bounds the error in the probability-generating function by the multiple-occurrence
probability and subdivides time using the convolution law.

For a nondecreasing process, stationary increments independent of the current count give
such a semigroup. Consequently the microscopic conditions determine every marginal law,
without a canonical sample space, moment assumptions, or sample-path continuity. This result
does not by itself assert independence of arbitrary collections of increments or simplicity
of paths; those need the corresponding process hypotheses.

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

/-- A nondecreasing natural-valued process starting at zero has Poisson marginals if its
increments are stationary and independent of the current count and satisfy the microscopic
one- and multiple-occurrence limits. Full independence of all increments is not needed for
this marginal conclusion. -/
theorem hasLaw_poissonMeasure_of_small_time {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : ℝ≥0 → Ω → ℕ}
    (hN : ∀ t, Measurable (N t)) (h0 : N 0 =ᵐ[P] fun _ ↦ 0)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun t ↦ N t ω))
    (hind : ∀ s t, IndepFun (N s) (fun ω ↦ N (s + t) ω - N s ω) P)
    (hstat : ∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P)
    (r : ℝ≥0)
    (h1 : Tendsto (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} / h)
      (𝓝[>] 0) (𝓝 (r : ℝ)))
    (h2 : Tendsto (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω} / h)
      (𝓝[>] 0) (𝓝 0)) (t : ℝ≥0) :
    HasLaw (N t) (poissonMeasure (r * t)) P := by
  have (s : ℝ≥0) : IsProbabilityMeasure (P.map (N s)) :=
    (Measure.isProbabilityMeasure_map_iff (hN s).aemeasurable).mpr inferInstance
  have hzero : P.map (N 0) = Measure.dirac 0 := by
    rw [Measure.map_congr h0]
    simp
  have hadd (s u : ℝ≥0) : P.map (N (s + u)) = P.map (N s) ∗ P.map (N u) := by
    have hae : N s + (fun ω ↦ N (s + u) ω - N s ω) =ᵐ[P] N (s + u) := by
      filter_upwards [hmono] with ω hω
      exact Nat.add_sub_of_le (hω (le_add_right le_rfl))
    calc
      P.map (N (s + u)) = P.map (N s + (fun ω ↦ N (s + u) ω - N s ω)) :=
        Measure.map_congr hae.symm
      _ = P.map (N s) ∗ P.map (fun ω ↦ N (s + u) ω - N s ω) :=
        (hind s u).map_add_eq_map_conv_map₀ (hN s).aemeasurable
          ((hN (s + u)).sub (hN s)).aemeasurable
      _ = P.map (N s) ∗ P.map (N u) := by rw [(hstat s u).map_eq]
  have hlaw := eq_poissonMeasure_of_small_time (fun s ↦ P.map (N s)) r hzero hadd
    (by simpa only [map_measureReal_apply (hN _) (measurableSet_singleton 1),
      Set.preimage, Set.mem_singleton_iff] using h1)
    (by simpa only [map_measureReal_apply (hN _) measurableSet_Ici,
      Set.preimage, Set.mem_Ici] using h2) t
  exact ⟨(hN t).aemeasurable, hlaw⟩

end TauCeti.Probability
