/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Excess.CountBound
public import TauCeti.Analysis.SpecificLimits.LatticeIncrements

/-!
# Excess escape from vanishing renewal increments

Vanishing renewal-function increments force the probability of a bounded excess
to tend to zero. It suffices to know vanishing successive increments on any fixed
positive grid: monotonicity extends this input to all real observation times and
all bounded windows. In particular, the infinite-mean lattice Blackwell limit
supplies the required input without restricting observation times to the lattice.

These are implications from increment limits, not unconditional renewal limit
theorems. They allow atoms at zero and do not require a finite interarrival mean.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition, Wiley, 1971, Chapter XI.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- If the renewal-function increment over a window of length `x` tends to zero,
the probability of an excess at most `x` tends to zero. No finite-mean assumption
is needed, and genuine zero-time arrivals are allowed. -/
theorem tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) (x : ℝ≥0)
    (hlim : Tendsto (fun t ↦ ((P.map (T 0)).renewalFunction (t + x)).toReal -
      ((P.map (T 0)).renewalFunction t).toReal) atTop (𝓝 0)) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) :=
  squeeze_zero (fun _ ↦ measureReal_nonneg)
    (fun t ↦ measureReal_renewalExcess_le_le_renewalFunction_sub hT hindep hid hzero t x) hlim

/-- Vanishing successive renewal increments on one positive grid imply excess escape
at all real observation times, for every bounded excess threshold. The increment
hypothesis is exactly the zero-rate lattice Blackwell limit. -/
theorem tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub_lattice
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) {a : ℝ≥0} (ha : 0 < a)
    (hlim : Tendsto (fun n : ℕ ↦ ((P.map (T 0)).renewalFunction (a * (n + 1))).toReal -
      ((P.map (T 0)).renewalFunction (a * n)).toReal) atTop (𝓝 0)) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) := by
  have := hindep.isProbabilityMeasure
  have hF : (P.map (T 0)) {0} < 1 := by
    rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)]
  have hm : Monotone (fun t ↦ ((P.map (T 0)).renewalFunction t).toReal) := by
    intro s t hst
    exact ENNReal.toReal_mono (Measure.renewalFunction_lt_top _ hF t).ne
      (Measure.monotone_renewalFunction _ hst)
  exact tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub
    hT hindep hid hzero x (hm.tendsto_sub_add_of_tendsto_sub_lattice ha hlim x)

end TauCeti.Probability
