/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Excess.CountBound
public import TauCeti.Probability.Renewal.InfiniteMean
import TauCeti.Analysis.SpecificLimits.LatticeIncrements
import TauCeti.MeasureTheory.Integral.Lebesgue.Support
import TauCeti.Probability.Independence.Basic

/-!
# Excess escape from vanishing renewal increments and infinite mean

Vanishing renewal-function increments force the probability of a bounded excess
to tend to zero. It suffices to know vanishing successive increments on any fixed
positive grid: monotonicity extends this input to all real observation times and
all bounded windows.

Combining this transfer with the vanishing fixed-window renewal increments for
infinite-mean interarrival laws (`TauCeti.Probability.Renewal.InfiniteMean`) gives
unconditional excess-life escape: whenever `∫⁻ u, u ∂F = ∞`, regardless of whether
`F` is lattice or nonlattice, `P(E_t ≤ x) → 0` and `P(x < E_t) → 1` for every finite
threshold `x` as `t → ∞` through all nonnegative real observation times. Genuine
atoms at zero are allowed throughout.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition, Wiley, 1971, Chapter XI.
* V. Tassion, *Applied Stochastic Processes*, ETH Zürich lecture notes (2025), Chapter 6.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- For i.i.d. nonnegative increments with `P {ω | T 0 ω = 0} < 1`, if the renewal-function
increment over a window of length `x` tends to zero, then the probability of an excess at most `x`
tends to zero. No finite-mean or strict increment-measurability assumption is needed, and genuine
zero-time arrivals are allowed. -/
theorem tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) (x : ℝ≥0)
    (hlim : Tendsto (fun t ↦ ((P.map (T 0)).renewalFunction (t + x)).toReal -
      ((P.map (T 0)).renewalFunction t).toReal) atTop (𝓝 0)) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) := by
  have hF : (P.map (T 0)) {0} < 1 := by
    rwa [Measure.map_apply_of_aemeasurable (hid 0).aemeasurable_fst (measurableSet_singleton 0)]
  exact squeeze_zero (fun _ ↦ measureReal_nonneg)
    (fun t ↦ measureReal_renewalExcess_le_le_renewalFunction_sub hindep hid hF t x) hlim

/-- For i.i.d. nonnegative increments with `P {ω | T 0 ω = 0} < 1`, vanishing successive renewal
increments on one positive grid imply excess escape at all real observation times, for every
bounded excess threshold. The increment hypothesis is exactly the zero-rate lattice Blackwell
limit. -/
theorem tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub_lattice
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) {a : ℝ≥0} (ha : 0 < a)
    (hlim : Tendsto (fun n : ℕ ↦ ((P.map (T 0)).renewalFunction (a * (n + 1))).toReal -
      ((P.map (T 0)).renewalFunction (a * n)).toReal) atTop (𝓝 0)) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) := by
  have := hindep.isProbabilityMeasure
  have hF : (P.map (T 0)) {0} < 1 := by
    rwa [Measure.map_apply_of_aemeasurable (hid 0).aemeasurable_fst (measurableSet_singleton 0)]
  exact tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub
    hindep hid hzero x
    (((P.map (T 0)).monotone_toReal_renewalFunction hF).tendsto_sub_add_of_tendsto_sub_lattice
      ha hlim x)

/-- **Infinite-mean excess-life escape.** For i.i.d. nonnegative increments of infinite
extended mean, lattice or nonlattice, the probability that the excess life is at most `x`
tends to zero as `t → ∞` through all nonnegative real observation times. -/
theorem tendsto_measureReal_renewalExcess_le_of_mean_eq_top
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) := by
  have := hindep.isProbabilityMeasure
  have hF := (P.map (T 0)).measure_singleton_zero_lt_one_of_mean_eq_top hmean
  have hzero : P {ω | T 0 ω = 0} < 1 := by
    rwa [Measure.map_apply_of_aemeasurable (hid 0).aemeasurable_fst
      (measurableSet_singleton 0)] at hF
  exact tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub
    hindep hid hzero x
    ((P.map (T 0)).tendsto_renewalFunction_add_sub_of_mean_eq_top hmean x)

/-- **Infinite-mean excess-tail escape.** For i.i.d. nonnegative increments of infinite
extended mean, lattice or nonlattice, the probability that the excess life exceeds any
fixed bound `x` tends to one as `t → ∞`. -/
theorem tendsto_measureReal_lt_renewalExcess_of_mean_eq_top
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop (𝓝 1) := by
  have := hindep.isProbabilityMeasure
  simp_rw [measureReal_lt_renewalExcess_eq_one_sub fun n ↦ (hid n).aemeasurable_fst]
  simpa only [sub_zero] using tendsto_const_nhds.sub
    (tendsto_measureReal_renewalExcess_le_of_mean_eq_top hindep hid hmean x)

end TauCeti.Probability
