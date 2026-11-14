/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Blackwell
public import TauCeti.Probability.Renewal.Excess.Limit
public import TauCeti.Probability.Renewal.Excess.Lattice

/-!
# The limiting excess-life theorem

For i.i.d. nonnegative increments with nonlattice law and finite extended mean, the
excess life converges to the equilibrium excess-life distribution. Its distribution
function is the integrated interarrival tail divided by the mean, and its density
and normalization are given by `MeasureTheory.Measure.equilibriumExcessLaw`.
The distributional conclusion holds along any countably generated filter of observation
times tending to infinity and for any realization of the limiting law.

With infinite extended mean, the probability of any bounded excess tends to zero,
whether the increment law is lattice or nonlattice. This is escape to infinity in
probability, not convergence in distribution to the zero measure.

All results allow atoms at zero and arbitrary measurable sample spaces. The finite-mean
limit uses the key renewal theorem on the nonincreasing tail forcing, not on the
possibly nonmonotone difference of interarrival distribution functions.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI, the limiting excess-life theorem.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- **The limiting excess-life distribution function.** For nonlattice i.i.d. increments
with finite extended mean, the probability of an excess at most `x` tends to the
normalized integrated interarrival tail. The formula includes `x = 0` and allows
zero increments; nonlatticeness implies that the extended mean is positive. -/
theorem tendsto_measureReal_renewalExcess_le_of_not_isLattice
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0))⁻¹).toReal *
        ∫ s in Ioc 0 (x : ℝ), (P.map (T 0)).real {u | s < (u : ℝ)})) := by
  have := hindep.isProbabilityMeasure
  have hzero : P {ω | T 0 ω = 0} < 1 := by
    simpa only [Measure.map_apply (hT 0) (measurableSet_singleton 0), preimage_singleton] using
      Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL
  rw [← Measure.equilibriumExcessLaw_real_Iic]
  exact tendsto_measureReal_renewalExcess_le_of_tendsto_measureReal_Ioc
    hT hindep hid hzero hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **The limiting excess-life law.** For nonlattice i.i.d. increments with finite
extended mean, the real-valued excess converges in distribution to any realization
of the equilibrium excess-life probability law. Observation times may tend to infinity
along any countably generated filter. -/
theorem tendstoInDistribution_renewalExcess_of_not_isLattice
    [IsProbabilityMeasure P]
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z (P.map (T 0)).equilibriumExcessLaw Q)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {t : ι → ℝ≥0}
    (ht : Tendsto t l atTop) :
    TendstoInDistribution (fun i ω ↦ (renewalExcess T (t i) ω : ℝ)) l
      Z (fun _ ↦ P) Q := by
  have hzero : P {ω | T 0 ω = 0} < 1 := by
    simpa only [Measure.map_apply (hT 0) (measurableSet_singleton 0), preimage_singleton] using
      Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL
  exact tendstoInDistribution_renewalExcess_of_tendsto_measureReal_Ioc
    hT hindep hid hzero hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) hZ ht

/-- **Infinite-mean excess escape.** For i.i.d. nonnegative increments of infinite
extended mean, the probability that the excess is at most any fixed threshold tends
to zero. No lattice or nonlattice hypothesis is needed, and observation times range
over the entire nonnegative half-line. -/
theorem tendsto_measureReal_renewalExcess_le_of_mean_eq_top
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) := by
  by_cases hL : (P.map (T 0)).IsLattice
  · exact tendsto_measureReal_renewalExcess_le_of_isLattice_of_mean_eq_top
      hT hindep hid hL hmean x
  · have := hindep.isProbabilityMeasure
    have hzero : P {ω | T 0 ω = 0} < 1 := by
      simpa only [Measure.map_apply (hT 0) (measurableSet_singleton 0), preimage_singleton] using
        Measure.measure_singleton_zero_lt_one_of_not_isLattice hL
    apply tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub
      hT hindep hid hzero x
    simpa only [hmean, ENNReal.inv_top, ENNReal.toReal_zero, zero_mul] using
      (P.map (T 0)).tendsto_renewalFunction_add_sub hL x

end TauCeti.Probability
