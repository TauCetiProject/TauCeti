/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Weak density of finite-moment laws

The inclusion of `P_p(X)` into probability measures has weakly dense range, including at
`p = ∞`. Mathlib's `StronglyMeasurable.approx` approximates the identity by simple functions;
`tendstoInDistribution_of_ae_tendsto` then gives finite-range pushforwards converging weakly
to any probability law. This does not assert density for the Wasserstein
topology: finite-range laws need not be dense for `W_∞`.

Together with separability of `P_1(X)`, this gives separability of the weak probability-measure
space without imposing any moment condition on its laws.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti.WassersteinSpace

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X] [MeasurableSingletonClass X] {p : ℝ≥0∞}

/-- Finite-moment probability laws are weakly dense, for every Wasserstein exponent, including
infinity. No moment hypothesis on the law being approximated is required. -/
theorem denseRange_toProbabilityMeasure :
    DenseRange (toProbabilityMeasure : WassersteinSpace p X → ProbabilityMeasure X) := by
  intro μ
  have : Nonempty X := nonempty_of_isProbabilityMeasure (μ := (μ : Measure X))
  let x₀ : X := Classical.choice ‹Nonempty X›
  let f : ℕ → SimpleFunc X X := stronglyMeasurable_id.approx
  have hf (n : ℕ) : HasFiniteMoment p ((μ : Measure X).map (f n)) := by
    apply hasFiniteMoment_of_ae_mem_finset x₀ (s := (f n).range)
    simpa only [← SimpleFunc.coe_range, Finset.mem_coe] using
      ae_map_mem_range (μ := (μ : Measure X))
        ((f n).finite_range.measurableSet) (f n).measurable.aemeasurable
  let ν (n : ℕ) : WassersteinSpace p X :=
    mk (μ.map (f n)) (hf n)
  have hlim : Tendsto (fun n ↦ toProbabilityMeasure (ν n)) atTop (𝓝 μ) := by
    have h := (tendstoInDistribution_of_ae_tendsto (μ' := (μ : Measure X))
      (fun n ↦ (f n).measurable.aemeasurable) aemeasurable_id
      (.of_forall stronglyMeasurable_id.tendsto_approx)).tendsto
    have heq (n : ℕ) : toProbabilityMeasure (ν n) = μ.map (f n) := coe_mk _ _
    simp_rw [heq]
    have hμ : (⟨(μ : Measure X), inferInstance⟩ : ProbabilityMeasure X) = μ :=
      ProbabilityMeasure.toMeasure_injective (by simp)
    simpa only [ProbabilityMeasure.map, Measure.map_id, hμ] using h
  exact mem_closure_of_tendsto hlim
    (.of_forall fun n ↦ mem_range_self (f := toProbabilityMeasure) (ν n))

end TauCeti.WassersteinSpace
