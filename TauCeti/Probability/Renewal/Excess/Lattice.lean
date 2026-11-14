/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Excess.Escape
public import TauCeti.Probability.Renewal.Lattice.InfiniteMean

/-!
# Excess-life escape for infinite-mean lattice renewals

For i.i.d. nonnegative lattice increments of infinite extended mean, the probability
that the excess life lies in any fixed bounded interval tends to zero. The conclusion
holds as the observation time tends to infinity through all nonnegative real times,
not just along lattice points. Genuine zero increments and their arrival clusters are
retained, and the process can be realized on any measurable probability space.

The result combines vanishing fixed-window renewal increments with the bound of the
excess distribution function by the expected number of arrivals in that window.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability

/-- **Infinite-mean lattice excess escape.** For i.i.d. lattice increments of infinite
extended mean, the excess eventually exceeds any fixed bound in probability. Observation
times are arbitrary, and zero increments are allowed. -/
theorem tendsto_measureReal_renewalExcess_le_of_isLattice_of_mean_eq_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hlattice : (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) := by
  have := hindep.isProbabilityMeasure
  have hF := (P.map (T 0)).measure_singleton_lt_one_of_lintegral_pos
    (f := fun u ↦ (u : ℝ≥0∞)) (a := 0) (by simp) (hmean ▸ ENNReal.zero_lt_top)
  have hzero : P {ω | T 0 ω = 0} < 1 := by
    rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)] at hF
  exact tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub
    hT hindep hid hzero x
    (hlattice.tendsto_renewalFunction_add_sub_of_mean_eq_top hmean x)

end TauCeti.Probability
