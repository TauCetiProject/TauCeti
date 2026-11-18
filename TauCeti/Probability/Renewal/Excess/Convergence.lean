/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Excess.Basic
public import TauCeti.Probability.Renewal.Equilibrium
public import TauCeti.Probability.Renewal.Lattice.Basic
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cdf
import TauCeti.Probability.Renewal.Blackwell
import TauCeti.Probability.Renewal.InfiniteMean
import TauCeti.Probability.Renewal.Excess.Escape
import TauCeti.Probability.Renewal.Excess.Limit

/-!
# The limiting excess-life theorem

For an ordinary renewal process with independent, identically distributed nonnegative
increments, the asymptotic behavior of the excess life `renewalExcess T t` as `t → ∞`
is governed by the extended interarrival mean and lattice structure:

* **Infinite mean (lattice or nonlattice):** When `(∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞`,
  the probability that the excess is at most `x` tends to `0` for every finite `x : ℝ≥0`,
  and the upper tail `P.real {ω | x < renewalExcess T t ω}` tends to `1`, along all
  nonnegative real observation times.
* **Nonlattice distribution function (all means):** When `P.map (T 0)` is nonlattice,
  `P.real {ω | renewalExcess T t ω ≤ x}` converges to
  `(P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ))` without any finite-mean
  hypothesis: for finite mean this is the integrated interarrival survival function divided
  by the mean (`MeasureTheory.Measure.equilibriumExcessLaw_real_Iic` and
  `MeasureTheory.Measure.equilibriumExcessLaw_map_real_Iic`), while for infinite mean both
  sides vanish.
* **Nonlattice finite-mean convergence in distribution:** When `P.map (T 0)` is nonlattice
  with finite extended mean, `(P.map (T 0)).equilibriumExcessLaw` is a probability measure;
  the upper tail, cumulative distribution function on all of `ℝ`, and law of the real-valued
  excess converge to it. By contrast, for infinite mean the upper tail tends to `1` while
  `equilibriumExcessLaw` is zero.

Genuine atoms of the increment law at zero are allowed throughout; nondegeneracy
(`P {ω | T 0 ω = 0} < 1`) follows automatically from either infinite mean or nonlatticeness.

## Main statements

* `TauCeti.Probability.tendsto_measureReal_renewalExcess_le_of_mean_eq_top`,
  `TauCeti.Probability.tendsto_measureReal_lt_renewalExcess_of_mean_eq_top` — unconditional
  infinite-mean excess-life escape for arbitrary (lattice or nonlattice) interarrival laws.
* `TauCeti.Probability.tendsto_measureReal_renewalExcess_le` — nonlattice convergence of
  `P.real {ω | renewalExcess T t ω ≤ x}` to the equilibrium excess distribution function,
  uniformly across finite and infinite interarrival means.
* `TauCeti.Probability.tendsto_measureReal_lt_renewalExcess`,
  `TauCeti.Probability.tendsto_cdf_renewalExcess`,
  `TauCeti.Probability.tendstoInDistribution_renewalExcess` — finite-mean nonlattice
  convergence of the excess tail, real CDF, and distribution.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI, the limiting excess-life theorem.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- **Infinite-mean excess-life escape.** For i.i.d. nonnegative increments of infinite extended
mean, whether lattice or nonlattice, the probability that the excess life is at most any fixed
threshold tends to zero as the observation time tends to infinity through all nonnegative reals.
Genuine zero increments are allowed. -/
theorem tendsto_measureReal_renewalExcess_le_of_mean_eq_top
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) := by
  have := hindep.isProbabilityMeasure
  have hF := (P.map (T 0)).measure_singleton_zero_lt_one_of_mean_eq_top hmean
  have hzero : P {ω | T 0 ω = 0} < 1 := by
    rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)] at hF
  exact tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub
    hT hindep hid hzero x
    ((P.map (T 0)).tendsto_renewalFunction_add_sub_of_mean_eq_top hmean x)

/-- **Infinite-mean excess-life tail limit.** For i.i.d. nonnegative increments of infinite
extended mean, whether lattice or nonlattice, the excess eventually exceeds every fixed threshold
with probability tending to one. -/
theorem tendsto_measureReal_lt_renewalExcess_of_mean_eq_top
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop (𝓝 1) := by
  have := hindep.isProbabilityMeasure
  simp_rw [measureReal_lt_renewalExcess_eq_one_sub hT]
  simpa only [sub_zero] using tendsto_const_nhds.sub
    (tendsto_measureReal_renewalExcess_le_of_mean_eq_top hT hindep hid hmean x)

private lemma measure_eq_zero_lt_one_of_not_isLattice
    (hT₀ : Measurable (T 0)) (hindep : iIndepFun T P)
    (hNL : ¬ (P.map (T 0)).IsLattice) :
    P {ω | T 0 ω = 0} < 1 := by
  have := hindep.isProbabilityMeasure
  have hF := Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL
  rwa [Measure.map_apply hT₀ (measurableSet_singleton 0)] at hF

/-- **The nonlattice excess-life limit theorem.** For i.i.d. nonlattice increments, the
probability that the excess life is at most `x` converges to the real mass of `(-∞, x]` under
the equilibrium excess-life measure `(P.map (T 0)).equilibriumExcessLaw`, evaluated by
`MeasureTheory.Measure.equilibriumExcessLaw_real_Iic` and
`MeasureTheory.Measure.equilibriumExcessLaw_map_real_Iic` as the integrated survival function
divided by the extended mean. No finite-mean assumption is needed: infinite mean gives limit zero
on both sides. -/
theorem tendsto_measureReal_renewalExcess_le
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)))) := by
  by_cases hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞
  · simpa [hmean] using
      tendsto_measureReal_renewalExcess_le_of_mean_eq_top hT hindep hid hmean x
  · have := hindep.isProbabilityMeasure
    exact tendsto_measureReal_renewalExcess_le_of_tendsto_measureReal_Ioc
      hT hindep hid (measure_eq_zero_lt_one_of_not_isLattice (hT 0) hindep hNL)
      hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **The nonlattice excess-life tail theorem.** For i.i.d. nonlattice increments of finite
extended mean, the upper tail of the excess life converges to the upper tail of the equilibrium
excess-life distribution. Finiteness of the mean is essential here: for infinite mean the upper
tail tends to `1` while `equilibriumExcessLaw` is zero. -/
theorem tendsto_measureReal_lt_renewalExcess
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  exact tendsto_measureReal_lt_renewalExcess_of_tendsto_measureReal_Ioc
    hT hindep hid (measure_eq_zero_lt_one_of_not_isLattice (hT 0) hindep hNL)
    hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Nonlattice excess-life CDF convergence.** For i.i.d. nonlattice increments of finite
extended mean, the cumulative distribution function of the real-valued excess converges at every
real threshold (including zero and negative thresholds) to the cumulative distribution function
of `(P.map (T 0)).equilibriumExcessLaw`. -/
theorem tendsto_cdf_renewalExcess
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞) (x : ℝ) :
    Tendsto (fun t ↦ cdf (P.map (fun ω ↦ (renewalExcess T t ω : ℝ))) x) atTop
      (𝓝 (cdf (P.map (T 0)).equilibriumExcessLaw x)) := by
  have := hindep.isProbabilityMeasure
  exact tendsto_cdf_renewalExcess_of_tendsto_measureReal_Ioc
    hT hindep hid (measure_eq_zero_lt_one_of_not_isLattice (hT 0) hindep hNL)
    hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Convergence in distribution of the excess life.** For i.i.d. nonlattice increments of
finite extended mean, the real-valued excess `renewalExcess T t` converges in distribution as
`t → ∞` in `ℝ≥0` to any random variable `Z` having law `(P.map (T 0)).equilibriumExcessLaw`.
Precomposing with `MeasureTheory.TendstoInDistribution.comp_tendsto` gives convergence along any
filter of observation times tending to `atTop`, without requiring countable generation of that
filter. -/
theorem tendstoInDistribution_renewalExcess
    [IsProbabilityMeasure P]
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Z : Ω' → ℝ} (hZ : HasLaw Z (P.map (T 0)).equilibriumExcessLaw Q) :
    TendstoInDistribution (fun (t : ℝ≥0) ω ↦ (renewalExcess T t ω : ℝ)) atTop
      Z (fun _ ↦ P) Q :=
  tendstoInDistribution_renewalExcess_of_tendsto_measureReal_Ioc
    hT hindep hid (measure_eq_zero_lt_one_of_not_isLattice (hT 0) hindep hNL)
    hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) hZ tendsto_id

end TauCeti.Probability
