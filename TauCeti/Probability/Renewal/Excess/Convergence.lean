/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Blackwell
public import TauCeti.Probability.Renewal.Excess.Lattice
public import TauCeti.Probability.Renewal.Excess.Limit

/-!
# The limiting excess-life distribution and infinite-mean excess escape

Let `T 0, T 1, …` be independent, identically distributed nonnegative interarrival times on a
probability space `(Ω, P)` with common law `F = P.map (T 0)`, and let
`renewalExcess T t` be the residual waiting time from observation time `t : ℝ≥0` until the next
arrival. Genuine zero increments and their arrival clusters are permitted.

This file establishes the unconditional asymptotic behavior of `renewalExcess T t` as `t → ∞`:

* **Normalization dichotomy**
  (`MeasureTheory.Measure.isProbabilityMeasure_equilibriumExcessLaw_iff_of_not_isLattice`): for any
  nonlattice measure `F` on `ℝ≥0`, the candidate limiting measure `F.equilibriumExcessLaw` on `ℝ`
  (with density `F((s, ∞)) / μ` on `(0, ∞)` where `μ = ∫⁻ u, (u : ℝ≥0∞) ∂F`) has total mass one if
  and only if `μ ≠ ∞`, and vanishes when `μ = ∞`.
* **Infinite-mean excess escape**
  (`TauCeti.Probability.tendsto_measureReal_renewalExcess_le_of_mean_eq_top`,
  `TauCeti.Probability.tendsto_measureReal_lt_renewalExcess_of_mean_eq_top`,
  `TauCeti.Probability.tendsto_cdf_renewalExcess_of_mean_eq_top`): whenever `μ = ∞`, whether `F` is
  lattice or nonlattice, `P.real {ω | renewalExcess T t ω ≤ x} → 0` and
  `P.real {ω | x < renewalExcess T t ω} → 1` for every `x : ℝ≥0`, and the cumulative distribution
  function of `(renewalExcess T t : Ω → ℝ)` tends to `0` at every `x : ℝ`.
* **Nonlattice excess-life convergence**
  (`TauCeti.Probability.tendsto_measureReal_renewalExcess_le`,
  `TauCeti.Probability.tendsto_measureReal_lt_renewalExcess`,
  `TauCeti.Probability.tendsto_cdf_renewalExcess`,
  `TauCeti.Probability.tendstoInDistribution_renewalExcess`): when `F` is nonlattice,
  `P.real {ω | renewalExcess T t ω ≤ x}` converges to `F.equilibriumExcessLaw.real (Iic (x : ℝ))`
  for every `x : ℝ≥0`, covering both finite mean (integrated-tail probability limit via
  `MeasureTheory.Measure.equilibriumExcessLaw_real_Iic`) and infinite mean (zero limit). Under
  `μ ≠ ∞`, the survival probabilities, real cumulative distribution functions, and distributions
  converge to `F.equilibriumExcessLaw`; precomposing with
  `MeasureTheory.TendstoInDistribution.comp_tendsto` specializes distributional convergence along
  any time family tending to `atTop`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition, Wiley, 1971, Chapter XI, §4.
* Vincent Tassion, *Applied Stochastic Processes*, lecture notes, ETH Zürich, 2025, Chapter 6.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

/-- For any nonlattice measure `F` on `ℝ≥0`, the equilibrium excess-life measure
`F.equilibriumExcessLaw` is a probability measure if and only if the extended first moment of `F`
is finite: nonlattice support rules out concentration at zero, so the first moment is automatically
nonzero. -/
theorem isProbabilityMeasure_equilibriumExcessLaw_iff_of_not_isLattice
    (F : Measure ℝ≥0) (hNL : ¬ F.IsLattice) :
    IsProbabilityMeasure F.equilibriumExcessLaw ↔ (∫⁻ u, (u : ℝ≥0∞) ∂F) ≠ ∞ := by
  rw [F.isProbabilityMeasure_equilibriumExcessLaw_iff, and_iff_right_iff_imp]
  intro _ hz
  refine hNL (F.isLattice_iff.2 ⟨1, zero_lt_one, ?_⟩)
  filter_upwards [(lintegral_eq_zero_iff measurable_coe_nnreal_ennreal).1 hz] with u hu
  exact ⟨0, by simpa using hu.symm⟩

end MeasureTheory.Measure

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- **Infinite-mean excess escape.** For i.i.d. nonnegative interarrival times of infinite extended
mean, whether lattice or nonlattice, the probability that the excess life at time `t` is at most
`x` converges to `0` as `t → ∞`. Zero increments are allowed. -/
theorem tendsto_measureReal_renewalExcess_le_of_mean_eq_top
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) := by
  by_cases hlattice : (P.map (T 0)).IsLattice
  · exact tendsto_measureReal_renewalExcess_le_of_isLattice_of_mean_eq_top
      hT hindep hid hlattice hmean x
  · have := hindep.isProbabilityMeasure
    have hF := Measure.measure_singleton_zero_lt_one_of_not_isLattice hlattice
    have hzero : P {ω | T 0 ω = 0} < 1 := by
      rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)] at hF
    have hlim := (P.map (T 0)).tendsto_renewalFunction_add_sub hlattice x
    rw [hmean, ENNReal.inv_top, ENNReal.toReal_zero, zero_mul] at hlim
    exact tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub
      hT hindep hid hzero x hlim

/-- **Infinite-mean excess survival limit.** For i.i.d. nonnegative interarrival times of infinite
extended mean, whether lattice or nonlattice, the probability that the excess life at time `t`
exceeds `x` converges to `1` as `t → ∞`. Zero increments are allowed. -/
theorem tendsto_measureReal_lt_renewalExcess_of_mean_eq_top
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop (𝓝 1) := by
  have := hindep.isProbabilityMeasure
  have hcompl (t : ℝ≥0) : P.real {ω | x < renewalExcess T t ω} =
      1 - P.real {ω | renewalExcess T t ω ≤ x} := by
    rw [← probReal_compl_eq_one_sub
      (measurableSet_le (measurable_renewalExcess hT t) measurable_const)]
    congr 1
    ext ω
    simp
  simp_rw [hcompl]
  simpa only [sub_zero] using tendsto_const_nhds.sub
    (tendsto_measureReal_renewalExcess_le_of_mean_eq_top hT hindep hid hmean x)

/-- For i.i.d. nonnegative interarrival times of infinite extended mean, whether lattice or
nonlattice, the cumulative distribution function of the real-valued excess at time `t` converges to
`0` at every real threshold `x` as `t → ∞`. -/
theorem tendsto_cdf_renewalExcess_of_mean_eq_top
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ) :
    Tendsto (fun t ↦ cdf (P.map (fun ω ↦ (renewalExcess T t ω : ℝ))) x) atTop (𝓝 0) := by
  have := hindep.isProbabilityMeasure
  refine squeeze_zero (fun _ ↦ cdf_nonneg _ x) (fun t ↦ ?_)
    (tendsto_measureReal_renewalExcess_le_of_mean_eq_top hT hindep hid hmean x.toNNReal)
  rw [Measure.cdf_map P _ (measurable_renewalExcess hT t).coe_nnreal_real.aemeasurable]
  exact measureReal_mono fun ω hω ↦ by
    simpa only [mem_ofPred_eq, Real.toNNReal_coe] using Real.toNNReal_mono hω

/-- **Limiting excess-life tail.** For i.i.d. nonnegative interarrival times with nonlattice law of
finite extended mean, the excess survival probability `P.real {ω | x < renewalExcess T t ω}`
converges as `t → ∞` to the equilibrium excess tail
`(P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ))`. Finiteness of the mean is required: when
the mean is infinite, the survival probability tends to `1` whereas `equilibriumExcessLaw` is `0`.
Zero increments are allowed. -/
theorem tendsto_measureReal_lt_renewalExcess
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  have hF := Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL
  have hzero : P {ω | T 0 ω = 0} < 1 := by
    rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)] at hF
  exact tendsto_measureReal_lt_renewalExcess_of_tendsto_measureReal_Ioc
    hT hindep hid hzero hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Limiting excess-life distribution function.** For i.i.d. nonnegative interarrival times with
nonlattice law, `P.real {ω | renewalExcess T t ω ≤ x}` converges as `t → ∞` to
`(P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ))` for every `x : ℝ≥0`. No finite-mean
assumption is needed: when the mean is finite this limit is the normalized integrated interarrival
tail (`MeasureTheory.Measure.equilibriumExcessLaw_real_Iic`), and when the mean is infinite both
sides vanish (`MeasureTheory.Measure.equilibriumExcessLaw_eq_zero_of_mean_eq_top`). Zero increments
are allowed. -/
theorem tendsto_measureReal_renewalExcess_le
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)))) := by
  by_cases hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞
  · simpa only [Measure.equilibriumExcessLaw_eq_zero_of_mean_eq_top _ hmean,
      measureReal_zero, Pi.zero_apply] using
      tendsto_measureReal_renewalExcess_le_of_mean_eq_top hT hindep hid hmean x
  · have := hindep.isProbabilityMeasure
    have hF := Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL
    have hzero : P {ω | T 0 ω = 0} < 1 := by
      rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)] at hF
    exact tendsto_measureReal_renewalExcess_le_of_tendsto_measureReal_Ioc
      hT hindep hid hzero hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Limiting excess-life CDF.** For i.i.d. nonnegative interarrival times with nonlattice law of
finite extended mean, the cumulative distribution function of the real-valued excess converges
pointwise at every `x : ℝ` to `cdf (P.map (T 0)).equilibriumExcessLaw x` as `t → ∞`. Finiteness of
the mean is required because `ProbabilityTheory.cdf 0` defaults to the unit step at `0` rather than
the identically zero limit of `tendsto_cdf_renewalExcess_of_mean_eq_top`. -/
theorem tendsto_cdf_renewalExcess
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞) (x : ℝ) :
    Tendsto (fun t ↦ cdf (P.map (fun ω ↦ (renewalExcess T t ω : ℝ))) x) atTop
      (𝓝 (cdf (P.map (T 0)).equilibriumExcessLaw x)) := by
  have := hindep.isProbabilityMeasure
  have hF := Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL
  have hzero : P {ω | T 0 ω = 0} < 1 := by
    rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)] at hF
  exact tendsto_cdf_renewalExcess_of_tendsto_measureReal_Ioc
    hT hindep hid hzero hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Limiting excess-life theorem in distribution.** For i.i.d. nonnegative interarrival times with
nonlattice law of finite extended mean, the real-valued excess `(renewalExcess T t ω : ℝ)`
converges in distribution along `atTop : Filter ℝ≥0` to any random variable `Z` having law
`(P.map (T 0)).equilibriumExcessLaw`. Precomposing with
`MeasureTheory.TendstoInDistribution.comp_tendsto` yields convergence along any family of
observation times tending to `atTop`. Zero increments are allowed. -/
theorem tendstoInDistribution_renewalExcess
    [IsProbabilityMeasure P]
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Z : Ω' → ℝ} (hZ : HasLaw Z (P.map (T 0)).equilibriumExcessLaw Q) :
    TendstoInDistribution (fun (t : ℝ≥0) ω ↦ (renewalExcess T t ω : ℝ)) atTop
      Z (fun _ ↦ P) Q := by
  have hF := Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL
  have hzero : P {ω | T 0 ω = 0} < 1 := by
    rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)] at hF
  exact tendstoInDistribution_renewalExcess_of_tendsto_measureReal_Ioc
    hT hindep hid hzero hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL)
    hZ tendsto_id

end TauCeti.Probability
