/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Blackwell
public import TauCeti.Probability.Renewal.Equilibrium
public import TauCeti.Probability.Renewal.Excess.Escape
public import TauCeti.Probability.Renewal.IntervalLimit
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cdf
import TauCeti.MeasureTheory.Function.TendstoInDistribution
import TauCeti.MeasureTheory.Integral.Lebesgue.Support
import TauCeti.Probability.HasLaw

/-!
# Limiting distribution of the excess life

For a renewal process with i.i.d. nonnegative increments of common law `F`, the asymptotic
distribution of the excess life `E_t = S_{N_t + 1} - t` as `t → ∞` is governed by Blackwell
interval limits applied to the excess-tail representation `P(x < E_t) = (F((· + x, ∞)) ∗ U) t`
together with infinite-mean excess escape (`TauCeti.Probability.Renewal.Excess.Escape`):

* **Conditional transfer from interval limits**: whenever forward renewal-interval masses
  converge at rate `((∫⁻ u, u ∂F)⁻¹).toReal` and `F` has finite extended mean, the excess tail,
  distribution function, real cumulative distribution function, and law converge to
  `F.equilibriumExcessLaw`, whose density on `(0, ∞)` is `F((t, ∞)) / μ`. The interval limit is
  an explicit input there, and these results must not be applied to a lattice law merely because
  its mean is finite.
* **Nonlattice interarrival laws**: for every nonlattice law `F`, `P(E_t ≤ x)` converges to
  `F.equilibriumExcessLaw.real (Iic x) = μ⁻¹ * ∫ s in Ioc 0 x, F((s, ∞))` without any
  finiteness assumption on the mean `μ`. Moreover, `F.equilibriumExcessLaw` is a probability
  measure (has total mass one) if and only if `μ ≠ ∞`, in which case the excess tail, real
  cumulative distribution function, and distribution of `(E_t : ℝ)` converge to
  `F.equilibriumExcessLaw`.

Almost surely zero increments are allowed in the conditional tail limit, where both sides vanish:
the excess is then almost surely zero, and the equilibrium law, whose normalizing constant is the
inverse `0⁻¹ = ∞` of the zero mean, is the zero measure by the convention `∞ * 0 = 0` in `ℝ≥0∞`.
The conditional distribution function statements assume the increments are not almost surely
zero, and the conditional distributional statement derives this, and the finite positive mean,
from the existence of a realization of the equilibrium law; it holds along any filter of
observation times tending to infinity. A nonlattice probability law automatically satisfies
`F {0} < 1`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI, the limiting excess-life theorem.
* V. Tassion, *Applied Stochastic Processes*, ETH Zürich lecture notes (2025), Chapter 6.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- Renewal interval limits imply convergence of the excess tail to the equilibrium tail.
Only finiteness of the extended mean is required. If the increments are almost surely zero, the
excess is almost surely zero, so the left side is `0`. The right side is `0` only by convention:
with `F = P.map (T 0)`, the equilibrium density `(∫⁻ u, u ∂F)⁻¹ * F {u | t < u}` at `t > 0` is
`0⁻¹ * 0 = ∞ * 0 = 0` in `ℝ≥0∞`, so the equilibrium law is then the zero measure. -/
theorem tendsto_measureReal_lt_renewalExcess_of_tendsto_measureReal_Ioc
    (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    (hlim : ∀ d : ℝ≥0, Tendsto (fun t : ℝ≥0 ↦
      (P.map (T 0)).renewalMeasure.real (Ioc t (t + d))) atTop
        (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0))⁻¹).toReal * d))) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  simp_rw [measureReal_lt_renewalExcess hindep hid]
  rw [Measure.equilibriumExcessLaw_real_Ioi_eq_integral_tail_add]
  by_cases hzero : P {ω | T 0 ω = 0} < 1
  swap
  · simp [(hasLaw_dirac_of_prob_eq_one (hid 0).aemeasurable_fst
      (le_antisymm prob_le_one (not_lt.1 hzero))).map_eq]
  have hF : (P.map (T 0)) {0} < 1 := by
    rwa [Measure.map_apply_of_aemeasurable (hid 0).aemeasurable_fst (measurableSet_singleton 0)]
  have htail : Antitone (fun u : ℝ≥0 ↦ (P.map (T 0)).real (Ioi (u + x))) :=
    fun _ _ h ↦ measureReal_mono (Ioi_subset_Ioi (by gcongr))
  exact (P.map (T 0)).tendsto_renewalConv_of_tendsto_measureReal_Ioc hF hlim
    htail (fun _ ↦ measureReal_nonneg)
    ((P.map (T 0)).integrableOn_Ioi_measureReal_tail_add x hmean)

/-- Renewal interval limits imply convergence of the excess distribution function at every
nonnegative threshold to the equilibrium excess-life measure. No finite-mean assumption is
required: when the extended mean is infinite, both sides vanish. -/
theorem tendsto_measureReal_renewalExcess_le_of_tendsto_measureReal_Ioc
    (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    (hlim : ∀ d : ℝ≥0, Tendsto (fun t : ℝ≥0 ↦
      (P.map (T 0)).renewalMeasure.real (Ioc t (t + d))) atTop
        (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0))⁻¹).toReal * d))) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  have hT (n : ℕ) : AEMeasurable (T n) P := (hid n).aemeasurable_fst
  have hF : (P.map (T 0)) {0} < 1 := by
    rwa [Measure.map_apply_of_aemeasurable (hid 0).aemeasurable_fst (measurableSet_singleton 0)]
  have := ((P.map (T 0)).isProbabilityMeasure_equilibriumExcessLaw_iff_of_measure_singleton_lt_one
    hF).2 hmean
  simp_rw [measureReal_renewalExcess_le_eq_one_sub hT]
  have hcomp : (P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)) =
      1 - (P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ)) := by
    rw [← probReal_compl_eq_one_sub measurableSet_Ioi, compl_Ioi]
  rw [hcomp]
  exact tendsto_const_nhds.sub
    (tendsto_measureReal_lt_renewalExcess_of_tendsto_measureReal_Ioc
      hindep hid hmean hlim x)

/-- Renewal interval limits give convergence of the CDF of the real-valued excess at every
real threshold, including negative thresholds and zero. This also supplies the CDF input
for convergence in distribution to any realization of the equilibrium excess-life law. -/
theorem tendsto_cdf_renewalExcess_of_tendsto_measureReal_Ioc
    (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    (hlim : ∀ d : ℝ≥0, Tendsto (fun t : ℝ≥0 ↦
      (P.map (T 0)).renewalMeasure.real (Ioc t (t + d))) atTop
        (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0))⁻¹).toReal * d)))
    (x : ℝ) :
    Tendsto (fun t ↦ cdf (P.map (fun ω ↦ (renewalExcess T t ω : ℝ))) x) atTop
      (𝓝 (cdf (P.map (T 0)).equilibriumExcessLaw x)) := by
  have := hindep.isProbabilityMeasure
  have hT (n : ℕ) : AEMeasurable (T n) P := (hid n).aemeasurable_fst
  have hF : (P.map (T 0)) {0} < 1 := by
    rwa [Measure.map_apply_of_aemeasurable (hid 0).aemeasurable_fst (measurableSet_singleton 0)]
  have := ((P.map (T 0)).isProbabilityMeasure_equilibriumExcessLaw_iff_of_measure_singleton_lt_one
    hF).2 hmean
  simp_rw [Measure.cdf_map_coe_nnreal P (aemeasurable_renewalExcess hT _), cdf_eq_real]
  split_ifs with hx
  · simpa only [Real.coe_toNNReal x hx] using
      (tendsto_measureReal_renewalExcess_le_of_tendsto_measureReal_Ioc
        hindep hid hzero hmean hlim x.toNNReal)
  · have hz : (P.map (T 0)).equilibriumExcessLaw (Iic x) = 0 :=
      measure_mono_null (Iic_subset_Iic.2 (le_of_not_ge hx))
        (Measure.equilibriumExcessLaw_Iic_zero _)
    simp only [measureReal_def, hz, ENNReal.toReal_zero]
    exact tendsto_const_nhds

/-- The excess converges in distribution to any realization of the equilibrium law,
along any filter of observation times tending to infinity, provided the renewal interval limits
hold. Both processes may live on arbitrary probability spaces. The finite positive mean and the
nondegeneracy of the increments follow from `hZ`, because the equilibrium law is a probability
measure only in that case. -/
theorem tendstoInDistribution_renewalExcess_of_tendsto_measureReal_Ioc
    [IsProbabilityMeasure P]
    (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hlim : ∀ d : ℝ≥0, Tendsto (fun t : ℝ≥0 ↦
      (P.map (T 0)).renewalMeasure.real (Ioc t (t + d))) atTop
        (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0))⁻¹).toReal * d)))
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Z : Ω' → ℝ} (hZ : HasLaw Z (P.map (T 0)).equilibriumExcessLaw Q)
    {ι : Type*} {l : Filter ι} {t : ι → ℝ≥0}
    (ht : Tendsto t l atTop) :
    TendstoInDistribution (fun i ω ↦ (renewalExcess T (t i) ω : ℝ)) l
      Z (fun _ ↦ P) Q := by
  have hprob : IsProbabilityMeasure (P.map (T 0)).equilibriumExcessLaw := by
    rw [← hZ.map_eq]
    infer_instance
  obtain ⟨hne, hmean⟩ := (Measure.isProbabilityMeasure_equilibriumExcessLaw_iff _).1 hprob
  have hzero : P {ω | T 0 ω = 0} < 1 := by
    have := (P.map (T 0)).measure_singleton_lt_one_of_lintegral_pos
      (f := fun u ↦ (u : ℝ≥0∞)) (a := 0) (by simp) (pos_iff_ne_zero.2 hne)
    rwa [Measure.map_apply_of_aemeasurable (hid 0).aemeasurable_fst
      (measurableSet_singleton 0)] at this
  have htop : TendstoInDistribution (fun (s : ℝ≥0) ω ↦ (renewalExcess T s ω : ℝ)) atTop
      Z (fun _ ↦ P) Q := by
    refine TendstoInDistribution.of_tendsto_cdf
      (fun s ↦ measurable_coe_nnreal_real.comp_aemeasurable
        (aemeasurable_renewalExcess (fun n ↦ (hid n).aemeasurable_fst) s)) hZ.aemeasurable
      fun x ↦ ?_
    rw [hZ.map_eq]
    exact tendsto_cdf_renewalExcess_of_tendsto_measureReal_Ioc hindep hid hzero hmean hlim x
  exact htop.comp_tendsto ht

/-- **Limiting excess-life tail for nonlattice increments.** When the common increment law
is nonlattice and has finite extended mean, `P(x < E_t)` converges to the equilibrium
excess-life tail `(P.map (T 0)).equilibriumExcessLaw.real (Ioi x)`. Finiteness of the mean
is necessary: when the mean is infinite, `P(x < E_t) → 1` while `equilibriumExcessLaw = 0`. -/
theorem tendsto_measureReal_lt_renewalExcess
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  exact tendsto_measureReal_lt_renewalExcess_of_tendsto_measureReal_Ioc
    hindep hid hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Limiting excess-life distribution function for nonlattice increments.** For any
nonlattice increment law, `P(E_t ≤ x)` converges as `t → ∞` to
`(P.map (T 0)).equilibriumExcessLaw.real (Iic x)`. No finiteness assumption on the mean is
needed: when the extended mean is infinite, both the limit of `P(E_t ≤ x)` and
`equilibriumExcessLaw` are zero. -/
theorem tendsto_measureReal_renewalExcess_le
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  by_cases hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞
  · simp only [Measure.equilibriumExcessLaw_eq_zero_of_mean_eq_top _ hmean,
      measureReal_zero_apply]
    exact tendsto_measureReal_renewalExcess_le_of_mean_eq_top hindep hid hmean x
  · have hF := Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL
    have hzero : P {ω | T 0 ω = 0} < 1 := by
      rwa [Measure.map_apply_of_aemeasurable (hid 0).aemeasurable_fst
        (measurableSet_singleton 0)] at hF
    exact tendsto_measureReal_renewalExcess_le_of_tendsto_measureReal_Ioc
      hindep hid hzero hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Integrated-tail formula for the limiting excess-life distribution.** For any
nonlattice increment law, `P(E_t ≤ x)` converges to the reciprocal extended increment mean
times the integral over `(0, x]` of the increment tail `s ↦ P.real {ω | s < T 0 ω}`. -/
theorem tendsto_measureReal_renewalExcess_le_integral_tail
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 (((∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P)⁻¹).toReal *
        ∫ s in Ioc 0 (x : ℝ), P.real {ω | s < (T 0 ω : ℝ)})) := by
  have := hindep.isProbabilityMeasure
  rw [← Measure.equilibriumExcessLaw_map_real_Iic P (hid 0).aemeasurable_fst]
  exact tendsto_measureReal_renewalExcess_le hindep hid hNL x

/-- **Limiting cumulative distribution function of the excess life.** For a nonlattice
increment law of finite extended mean, the real-valued CDF of `(renewalExcess T t · : ℝ)`
converges pointwise on all of `ℝ` to `cdf (P.map (T 0)).equilibriumExcessLaw`. Finiteness
of the mean is required because `cdf` is only the distribution function of a probability
measure. -/
theorem tendsto_cdf_renewalExcess
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞) (x : ℝ) :
    Tendsto (fun t ↦ cdf (P.map (fun ω ↦ (renewalExcess T t ω : ℝ))) x) atTop
      (𝓝 (cdf (P.map (T 0)).equilibriumExcessLaw x)) := by
  have := hindep.isProbabilityMeasure
  have hF := Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL
  have hzero : P {ω | T 0 ω = 0} < 1 := by
    rwa [Measure.map_apply_of_aemeasurable (hid 0).aemeasurable_fst
      (measurableSet_singleton 0)] at hF
  exact tendsto_cdf_renewalExcess_of_tendsto_measureReal_Ioc
    hindep hid hzero hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Limiting distribution of the excess life.** For i.i.d. nonnegative increments whose
common law is nonlattice, the real-valued excess life `(renewalExcess T (t i) · : ℝ)`
converges in distribution, along any filter of observation times `t i` tending to infinity in
`ℝ≥0`, to any random variable `Z` with law `(P.map (T 0)).equilibriumExcessLaw`. Both processes
may live on arbitrary probability spaces. The existence of `Z` forces the extended mean to be
finite, since the equilibrium law is otherwise not a probability measure. -/
theorem tendstoInDistribution_renewalExcess
    [IsProbabilityMeasure P]
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Z : Ω' → ℝ} (hZ : HasLaw Z (P.map (T 0)).equilibriumExcessLaw Q)
    {ι : Type*} {l : Filter ι} {t : ι → ℝ≥0} (ht : Tendsto t l atTop) :
    TendstoInDistribution (fun i ω ↦ (renewalExcess T (t i) ω : ℝ)) l
      Z (fun _ ↦ P) Q :=
  tendstoInDistribution_renewalExcess_of_tendsto_measureReal_Ioc
    hindep hid ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) hZ ht

end TauCeti.Probability
