/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.CDF
public import TauCeti.Probability.Renewal.Equilibrium
public import TauCeti.Probability.Renewal.Excess.Basic
public import TauCeti.Probability.Renewal.Lattice.Basic
import TauCeti.MeasureTheory.Function.TendstoInDistribution
import TauCeti.Probability.Renewal.Blackwell
import TauCeti.Probability.Renewal.Excess.InfiniteMean
import TauCeti.Probability.Renewal.Excess.Limit

/-!
# The limiting excess-life law for nonlattice renewal processes

For independent, identically distributed nonnegative increments whose common law
`F = P.map (T 0)` is nonlattice, the distribution function of the excess life
`E t = renewalExcess T t` converges at every `x : ℝ≥0` to the equilibrium excess-life
measure:

```text
P(E t ≤ x) ⟶ F.equilibriumExcessLaw.real (Iic x)
           = (𝔼[T 0])⁻¹ · ∫_{(0, x]} P(s < T 0) ds.
```

Because `F.equilibriumExcessLaw = 0` when `F` has infinite mean while `P(E t ≤ x) → 0` by
infinite-mean excess escape, the sublevel limit holds for **every** nonlattice interarrival law,
without assuming finite mean.

The limiting measure `F.equilibriumExcessLaw` is a probability measure if and only if `F` has
finite extended mean
(`MeasureTheory.Measure.isProbabilityMeasure_equilibriumExcessLaw_iff_of_not_isLattice`).
Under finite mean, the excess survival probabilities converge to the equilibrium tail, the
cumulative distribution function of `(E t : ℝ)` converges pointwise to `cdf F.equilibriumExcessLaw`
at every real threshold, and `(E t : ℝ)` converges in distribution as `t → ∞` to any realization
of `F.equilibriumExcessLaw` (both on `ℝ≥0` and on `ℝ`, and along any time family tending to `atTop`
via `MeasureTheory.TendstoInDistribution.comp_tendsto`). Atoms of `F` at zero are permitted, and no
separate measurability or `P(T 0 = 0) < 1` hypothesis is required.

## Main statements

* `MeasureTheory.Measure.isProbabilityMeasure_equilibriumExcessLaw_of_not_isLattice`,
  `MeasureTheory.Measure.isProbabilityMeasure_equilibriumExcessLaw_iff_of_not_isLattice`:
  for a nonlattice probability law, `F.equilibriumExcessLaw` has total mass one precisely when
  `F` has finite extended mean.
* `TauCeti.Probability.tendsto_measureReal_renewalExcess_le_of_not_isLattice`,
  `TauCeti.Probability.tendsto_measureReal_renewalExcess_le_integral_tail_of_not_isLattice`:
  convergence of `P(E t ≤ x)` to the normalized integrated interarrival tail, including infinite
  mean.
* `TauCeti.Probability.tendsto_measureReal_lt_renewalExcess_of_not_isLattice`: convergence of the
  excess survival probability `P(x < E t)` for finite-mean nonlattice laws.
* `TauCeti.Probability.tendsto_cdf_renewalExcess_of_not_isLattice`: pointwise convergence of the
  CDF of `(E t : ℝ)` at every real threshold for finite-mean nonlattice laws.
* `TauCeti.Probability.tendstoInDistribution_renewalExcess_of_not_isLattice`,
  `TauCeti.Probability.tendstoInDistribution_renewalExcess_toNNReal_of_not_isLattice`:
  **convergence in distribution of the excess life** to `F.equilibriumExcessLaw` on `ℝ≥0` and `ℝ`
  for finite-mean nonlattice laws.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §4, Theorem 2.
* Vincent Tassion, *Applied Stochastic Processes*, lecture notes, ETH Zürich, 2025, Chapter 6.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

/-- A nonlattice probability interarrival law of finite extended mean has a normalized equilibrium
excess-life probability distribution. -/
theorem isProbabilityMeasure_equilibriumExcessLaw_of_not_isLattice
    (F : Measure ℝ≥0) [IsProbabilityMeasure F] (hNL : ¬ F.IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) ≠ ∞) :
    IsProbabilityMeasure F.equilibriumExcessLaw :=
  F.isProbabilityMeasure_equilibriumExcessLaw_of_measure_singleton_lt_one
    (measure_singleton_zero_lt_one_of_not_isLattice hNL) hmean

/-- For a nonlattice probability interarrival law, the candidate equilibrium excess-life measure
has total mass one if and only if the extended mean is finite. -/
theorem isProbabilityMeasure_equilibriumExcessLaw_iff_of_not_isLattice
    (F : Measure ℝ≥0) [IsProbabilityMeasure F] (hNL : ¬ F.IsLattice) :
    IsProbabilityMeasure F.equilibriumExcessLaw ↔ (∫⁻ u, (u : ℝ≥0∞) ∂F) ≠ ∞ :=
  F.isProbabilityMeasure_equilibriumExcessLaw_iff_of_measure_singleton_lt_one
    (measure_singleton_zero_lt_one_of_not_isLattice hNL)

end MeasureTheory.Measure

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- **Limiting excess-life survival probability.** For i.i.d. nonlattice increments of finite
extended mean, `P(x < E t)` converges as `t → ∞` to the equilibrium excess tail. Finiteness of
the mean is essential here: for infinite mean, `P(x < E t) → 1`
(`tendsto_measureReal_lt_renewalExcess_of_mean_eq_top`) while `equilibriumExcessLaw = 0`. Zero
increments are permitted. -/
theorem tendsto_measureReal_lt_renewalExcess_of_not_isLattice
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  exact tendsto_measureReal_lt_renewalExcess_of_tendsto_measureReal_Ioc hindep hid
    (Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL) hmean
    ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Limiting excess-life distribution function.** For i.i.d. nonlattice increments, `P(E t ≤ x)`
converges as `t → ∞` to `(P.map (T 0)).equilibriumExcessLaw.real (Iic x)`. No finite-mean
assumption is required: when the extended mean is infinite, both sides vanish. -/
theorem tendsto_measureReal_renewalExcess_le_of_not_isLattice
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)))) := by
  by_cases hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞
  · simp only [Measure.equilibriumExcessLaw_eq_zero_of_mean_eq_top _ hmean, measureReal_zero]
    exact tendsto_measureReal_renewalExcess_le_of_mean_eq_top hindep hid hmean x
  · have := hindep.isProbabilityMeasure
    exact tendsto_measureReal_renewalExcess_le_of_tendsto_measureReal_Ioc hindep hid
      (Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL) hmean
      ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Limiting excess-life distribution function, integrated-tail form.** For i.i.d. nonlattice
increments, `P(E t ≤ x)` converges as `t → ∞` to the reciprocal extended mean times the
integrated interarrival tail `∫ s in Ioc 0 x, P.real {ω | s < T 0 ω}`. Infinite mean is
included, with both sides equal to zero. -/
theorem tendsto_measureReal_renewalExcess_le_integral_tail_of_not_isLattice
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 (((∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P)⁻¹).toReal *
        ∫ s in Ioc 0 (x : ℝ), P.real {ω | s < (T 0 ω : ℝ)})) := by
  have := hindep.isProbabilityMeasure
  have hT0 : AEMeasurable (T 0) P := (hid 0).aemeasurable_fst
  have hmean_eq : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P :=
    lintegral_map' measurable_coe_nnreal_ennreal.aemeasurable hT0
  have htail_eq (s : ℝ) :
      (P.map (T 0)).real {u | s < (u : ℝ)} = P.real {ω | s < (T 0 ω : ℝ)} := by
    rw [measureReal_def, Measure.map_apply_of_aemeasurable hT0
      (measurableSet_lt measurable_const measurable_coe_nnreal_real), ← measureReal_def,
      preimage_ofPred_eq]
  have hlim := tendsto_measureReal_renewalExcess_le_of_not_isLattice hindep hid hNL x
  rw [Measure.equilibriumExcessLaw_real_Iic, hmean_eq] at hlim
  simpa only [htail_eq] using hlim

/-- For i.i.d. nonlattice increments of finite extended mean, the cumulative distribution function
of the real-valued excess converges pointwise at every real threshold `x` to the CDF of
`(P.map (T 0)).equilibriumExcessLaw`. Finiteness of the mean is required: when the extended mean is
infinite, `(P.map (T 0)).equilibriumExcessLaw = 0` and `cdf 0` equals `1` on `[0, ∞)`, whereas the
excess CDFs tend to `0`. -/
theorem tendsto_cdf_renewalExcess_of_not_isLattice
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞) (x : ℝ) :
    Tendsto (fun t ↦ cdf (P.map (fun ω ↦ (renewalExcess T t ω : ℝ))) x) atTop
      (𝓝 (cdf (P.map (T 0)).equilibriumExcessLaw x)) := by
  have := hindep.isProbabilityMeasure
  exact tendsto_cdf_renewalExcess_of_tendsto_measureReal_Ioc hindep hid
    (Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL) hmean
    ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Convergence in distribution of the excess life.** For i.i.d. nonlattice increments of finite
extended mean, the real-valued excess `(renewalExcess T t ω : ℝ)` converges in distribution as
`t → ∞` in `ℝ≥0` to any random variable `Z` with law `(P.map (T 0)).equilibriumExcessLaw`.
Precomposing with `MeasureTheory.TendstoInDistribution.comp_tendsto` yields convergence along any
time family tending to `atTop`. -/
theorem tendstoInDistribution_renewalExcess_of_not_isLattice
    [IsProbabilityMeasure P]
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Z : Ω' → ℝ} (hZ : HasLaw Z (P.map (T 0)).equilibriumExcessLaw Q) :
    TendstoInDistribution (fun (t : ℝ≥0) ω ↦ (renewalExcess T t ω : ℝ)) atTop
      Z (fun _ ↦ P) Q :=
  tendstoInDistribution_renewalExcess_of_tendsto_measureReal_Ioc hindep hid
    (Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL) hmean
    ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) hZ tendsto_id

/-- **Convergence in distribution of the excess life on the real time axis.** For i.i.d.
nonlattice increments of finite extended mean, `(renewalExcess T t.toNNReal ω : ℝ)` converges in
distribution as `t → ∞` in `ℝ` to any random variable `Z` with law
`(P.map (T 0)).equilibriumExcessLaw`. -/
theorem tendstoInDistribution_renewalExcess_toNNReal_of_not_isLattice
    [IsProbabilityMeasure P]
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Z : Ω' → ℝ} (hZ : HasLaw Z (P.map (T 0)).equilibriumExcessLaw Q) :
    TendstoInDistribution (fun (t : ℝ) ω ↦ (renewalExcess T t.toNNReal ω : ℝ)) atTop
      Z (fun _ ↦ P) Q :=
  (tendstoInDistribution_renewalExcess_of_not_isLattice hindep hid hNL hmean hZ).comp_tendsto
    Real.tendsto_toNNReal_atTop

end TauCeti.Probability
