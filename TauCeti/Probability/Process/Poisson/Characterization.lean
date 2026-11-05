/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Characterization
public import Mathlib.Probability.Independence.Integration

/-!
# Poisson marginals from microscopic increment probabilities

For a nondecreasing process, stationary increments independent of the current count give
a convolution semigroup of probability laws on `ℕ`. Applying
`eq_poissonMeasure_of_small_time`, the microscopic conditions determine every marginal law,
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

/-- A nondecreasing natural-valued process starting at zero has Poisson marginals if its
increments are stationary and independent of the current count and satisfy the microscopic
one- and multiple-occurrence limits. Full independence of all increments is not needed for
this marginal conclusion. -/
theorem hasLaw_poissonMeasure_of_small_time {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : ℝ≥0 → Ω → ℕ}
    (h0 : N 0 =ᵐ[P] fun _ ↦ 0)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun t ↦ N t ω))
    (hind : ∀ s t, IndepFun (N s) (fun ω ↦ N (s + t) ω - N s ω) P)
    (hstat : ∀ s t, IdentDistrib (fun ω ↦ N (s + t) ω - N s ω) (N t) P P)
    (r : ℝ≥0)
    (h1 : Tendsto (fun h : ℝ≥0 ↦ P.real {ω | N h ω = 1} / h)
      (𝓝[>] 0) (𝓝 (r : ℝ)))
    (h2 : Tendsto (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω} / h)
      (𝓝[>] 0) (𝓝 0)) (t : ℝ≥0) :
    HasLaw (N t) (poissonMeasure (r * t)) P := by
  have hN (s : ℝ≥0) : AEMeasurable (N s) P := (hstat 0 s).aemeasurable_snd
  have (s : ℝ≥0) : IsProbabilityMeasure (P.map (N s)) :=
    (Measure.isProbabilityMeasure_map_iff (hN s)).mpr inferInstance
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
        (hind s u).map_add_eq_map_conv_map₀ (hN s) (hstat s u).aemeasurable_fst
      _ = P.map (N s) ∗ P.map (N u) := by rw [(hstat s u).map_eq]
  have hlaw := eq_poissonMeasure_of_small_time (fun s ↦ P.map (N s)) r hzero hadd
    (by simpa only [map_measureReal_apply_of_aemeasurable (hN _) (measurableSet_singleton 1),
      Set.preimage, Set.mem_singleton_iff] using h1)
    (by simpa only [map_measureReal_apply_of_aemeasurable (hN _) measurableSet_Ici,
      Set.preimage, Set.mem_Ici] using h2) t
  exact ⟨hN t, hlaw⟩

end TauCeti.Probability
