/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Blackwell
public import TauCeti.Probability.Renewal.Excess.InfiniteMean
public import TauCeti.Probability.Renewal.Excess.Limit

/-!
# The excess-life limit for nonlattice renewals

For i.i.d. nonnegative increments with a nonlattice law `F` of finite extended mean `μ`,
the excess life `E_t` converges in distribution, as `t → ∞`, to the equilibrium excess-life
law, whose density on the positive half-line is `s ↦ F(s, ∞) / μ`. In particular

  `P(E_t ≤ x) → μ⁻¹ * ∫ s in (0, x], F(s, ∞)`

for every `x ≥ 0`, and the right side is the distribution function of a probability
measure (`Measure.equilibriumExcessLaw_real_Iic`,
`Measure.isProbabilityMeasure_equilibriumExcessLaw_of_measure_singleton_lt_one`).

Zero increments are allowed: a nonlattice law is not concentrated at zero, and its genuine
zero-time arrivals are counted. The interval limits needed by the conditional statements
of `TauCeti.Probability.Renewal.Excess.Limit` are supplied by the nonlattice Blackwell
renewal theorem. For infinite mean the equilibrium measure is zero and the excess escapes
to infinity (`TauCeti.Probability.tendsto_measureReal_renewalExcess_le_of_mean_eq_top`), so
the distribution-function limit holds for every nonlattice law.

## Main statements

* `TauCeti.Probability.tendsto_measureReal_lt_renewalExcess_of_not_isLattice`: convergence of
  the excess tail, for finite mean.
* `TauCeti.Probability.tendsto_measureReal_renewalExcess_le_of_not_isLattice`: convergence of
  the excess distribution function at every nonnegative threshold, for any mean.
* `TauCeti.Probability.tendstoInDistribution_renewalExcess_of_not_isLattice`: convergence in
  distribution to any realization of the equilibrium excess-life law, which exists only for
  finite mean.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI, the limiting excess-life theorem.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- A nonlattice increment law is not almost surely zero. -/
private lemma measure_eq_zero_lt_one_of_not_isLattice (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hNL : ¬ (P.map (T 0)).IsLattice) :
    P {ω | T 0 ω = 0} < 1 := by
  have := hindep.isProbabilityMeasure
  have hF := Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL
  rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)] at hF

/-- **Excess-life tail limit.** For i.i.d. increments with a nonlattice law of finite
extended mean, the tail of the excess at every nonnegative threshold converges to the
tail of the equilibrium excess-life law. -/
theorem tendsto_measureReal_lt_renewalExcess_of_not_isLattice
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ)))) :=
  have := hindep.isProbabilityMeasure
  tendsto_measureReal_lt_renewalExcess_of_tendsto_measureReal_Ioc hT hindep hid
    (measure_eq_zero_lt_one_of_not_isLattice hT hindep hNL) hmean
    ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Excess-life limit.** For i.i.d. increments with a nonlattice law `F`, the distribution
function of the excess at every nonnegative threshold converges to that of the equilibrium
excess-life law. For finite mean `μ`, the limit is the normalized integrated tail
`μ⁻¹ * ∫ s in (0, x], F(s, ∞)` by `Measure.equilibriumExcessLaw_real_Iic`. For infinite mean
the equilibrium measure is zero, and the statement says that the excess escapes. -/
theorem tendsto_measureReal_renewalExcess_le_of_not_isLattice
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  by_cases hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞
  · simpa only [Measure.equilibriumExcessLaw_eq_zero_of_mean_eq_top _ hmean,
      measureReal_zero_apply] using
      tendsto_measureReal_renewalExcess_le_of_mean_eq_top hT hindep hid hmean x
  · exact tendsto_measureReal_renewalExcess_le_of_tendsto_measureReal_Ioc hT hindep hid
      (measure_eq_zero_lt_one_of_not_isLattice hT hindep hNL) hmean
      ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Excess-life limit in distribution.** For i.i.d. increments with a nonlattice law, the
real-valued excess converges in distribution to any realization of the equilibrium
excess-life law, along any countably generated filter of observation times tending to
infinity. Both processes may live on arbitrary probability spaces. The existence of such a
realization forces the interarrival mean to be finite. -/
theorem tendstoInDistribution_renewalExcess_of_not_isLattice
    [IsProbabilityMeasure P]
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Z : Ω' → ℝ} (hZ : HasLaw Z (P.map (T 0)).equilibriumExcessLaw Q)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {t : ι → ℝ≥0}
    (ht : Tendsto t l atTop) :
    TendstoInDistribution (fun i ω ↦ (renewalExcess T (t i) ω : ℝ)) l
      Z (fun _ ↦ P) Q :=
  have hmean := ((P.map (T 0)).isProbabilityMeasure_equilibriumExcessLaw_iff.1
    (hZ.isProbabilityMeasure_iff.1 ‹_›)).2
  tendstoInDistribution_renewalExcess_of_tendsto_measureReal_Ioc hT hindep hid
    (measure_eq_zero_lt_one_of_not_isLattice hT hindep hNL) hmean
    ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) hZ ht

end TauCeti.Probability
