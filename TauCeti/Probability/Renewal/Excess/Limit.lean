/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Excess.Escape
public import TauCeti.Probability.Renewal.Equilibrium
public import TauCeti.Probability.Renewal.InfiniteMean
public import TauCeti.Probability.Renewal.IntervalLimit
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cdf

/-!
# Limiting distribution and escape of the excess life

For a renewal process with i.i.d. nonnegative increments of common law `F`, the asymptotic
behavior of the excess life `E_t = S_{N_t + 1} - t` as `t → ∞` is governed by Blackwell
interval limits applied to the excess-tail representation `P(x < E_t) = (F((· + x, ∞)) ∗ U) t`
and by the count bound `{E_t ≤ x} ⊆ {N_{t + x} - N_t ≥ 1}`:

* **Conditional transfer from interval limits**: whenever forward renewal-interval masses
  converge at rate `((∫⁻ u, u ∂F)⁻¹).toReal` and `F` has finite extended mean, the excess tail,
  distribution function, real cumulative distribution function, and law converge to
  `F.equilibriumExcessLaw`, whose density on `(0, ∞)` is `F((t, ∞)) / μ`.
* **Nonlattice interarrival laws**: for every nonlattice law `F`, `P(E_t ≤ x)` converges to
  `F.equilibriumExcessLaw.real (Iic x) = μ⁻¹ * ∫ s in Ioc 0 x, F((s, ∞))` without any
  finiteness assumption on the mean `μ`. Moreover, `F.equilibriumExcessLaw` is a probability
  measure (has total mass one) if and only if `μ ≠ ∞`, in which case the excess tail, real
  cumulative distribution function, and distribution of `(E_t : ℝ)` converge to
  `F.equilibriumExcessLaw`.
* **Infinite-mean escape (lattice or nonlattice)**: whenever `∫⁻ u, u ∂F = ∞`, regardless of
  whether `F` is lattice or nonlattice, `P(E_t ≤ x) → 0` and `P(x < E_t) → 1` for every finite
  threshold `x` as `t → ∞` through all nonnegative real observation times.

Zero increments are allowed throughout; both nonlattice hypotheses and infinite-mean hypotheses
automatically imply `F {0} < 1`.

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
Only finiteness of the extended mean is required; the positive mean follows from the
nondegeneracy assumption on the increments. -/
theorem tendsto_measureReal_lt_renewalExcess_of_tendsto_measureReal_Ioc
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    (hlim : ∀ d : ℝ≥0, Tendsto (fun t : ℝ≥0 ↦
      (P.map (T 0)).renewalMeasure.real (Ioc t (t + d))) atTop
        (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0))⁻¹).toReal * d))) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  have hF : (P.map (T 0)) {0} < 1 := by
    rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)]
  have htail : Antitone (fun u : ℝ≥0 ↦ (P.map (T 0)).real (Ioi (u + x))) :=
    fun _ _ h ↦ measureReal_mono (Ioi_subset_Ioi (by gcongr))
  simp_rw [measureReal_lt_renewalExcess hT hindep hid hzero]
  rw [Measure.equilibriumExcessLaw_real_Ioi_eq_integral_tail_add]
  exact (P.map (T 0)).tendsto_renewalConv_of_tendsto_measureReal_Ioc hF hlim
    htail (fun _ ↦ measureReal_nonneg)
    ((P.map (T 0)).integrableOn_Ioi_measureReal_tail_add x hmean)

/-- Renewal interval limits imply convergence of the excess distribution function at every
nonnegative threshold. The limiting measure is the normalized integrated interarrival tail. -/
theorem tendsto_measureReal_renewalExcess_le_of_tendsto_measureReal_Ioc
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    (hlim : ∀ d : ℝ≥0, Tendsto (fun t : ℝ≥0 ↦
      (P.map (T 0)).renewalMeasure.real (Ioc t (t + d))) atTop
        (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0))⁻¹).toReal * d))) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  have hF : (P.map (T 0)) {0} < 1 := by
    rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)]
  have := (P.map (T 0)).isProbabilityMeasure_equilibriumExcessLaw_of_measure_singleton_lt_one
    hF hmean
  have he (t : ℝ≥0) : P.real {ω | renewalExcess T t ω ≤ x} =
      1 - P.real {ω | x < renewalExcess T t ω} := by
    rw [← probReal_compl_eq_one_sub (measurableSet_lt measurable_const
      (measurable_renewalExcess hT t))]
    congr 1
    ext ω
    simp
  simp_rw [he]
  have hcomp : (P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)) =
      1 - (P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ)) := by
    rw [← probReal_compl_eq_one_sub measurableSet_Ioi, compl_Ioi]
  rw [hcomp]
  exact tendsto_const_nhds.sub
    (tendsto_measureReal_lt_renewalExcess_of_tendsto_measureReal_Ioc
      hT hindep hid hzero hmean hlim x)

/-- Renewal interval limits give convergence of the CDF of the real-valued excess at every
real threshold, including negative thresholds and zero. This also supplies the CDF input
for convergence in distribution to any realization of the equilibrium excess-life law. -/
theorem tendsto_cdf_renewalExcess_of_tendsto_measureReal_Ioc
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
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
  have hF : (P.map (T 0)) {0} < 1 := by
    rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)]
  have := (P.map (T 0)).isProbabilityMeasure_equilibriumExcessLaw_of_measure_singleton_lt_one
    hF hmean
  have hmeas (s : ℝ≥0) : Measurable (fun ω ↦ (renewalExcess T s ω : ℝ)) :=
    measurable_coe_nnreal_real.comp (measurable_renewalExcess hT s)
  simp_rw [Measure.cdf_map P _ (hmeas _).aemeasurable, cdf_eq_real]
  by_cases hx : 0 ≤ x
  · have he (s : ℝ≥0) : (fun ω ↦ (renewalExcess T s ω : ℝ)) ⁻¹' Iic x =
        {ω | renewalExcess T s ω ≤ x.toNNReal} := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_ofPred_eq, ← NNReal.coe_le_coe,
        Real.coe_toNNReal x hx]
    simp_rw [he]
    simpa only [Real.coe_toNNReal x hx] using
      (tendsto_measureReal_renewalExcess_le_of_tendsto_measureReal_Ioc
        hT hindep hid hzero hmean hlim x.toNNReal)
  · have hempty (s : ℝ≥0) : (fun ω ↦ (renewalExcess T s ω : ℝ)) ⁻¹' Iic x = ∅ := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge hx) (renewalExcess T s ω).coe_nonneg)
    have hz : (P.map (T 0)).equilibriumExcessLaw (Iic x) = 0 :=
      measure_mono_null (Iic_subset_Iic.2 (le_of_not_ge hx))
        (Measure.equilibriumExcessLaw_Iic_zero _)
    simp_rw [hempty, measureReal_empty, measureReal_def, hz, ENNReal.toReal_zero]
    exact tendsto_const_nhds

/-- The excess converges in distribution to any realization of the equilibrium law,
along any countably generated filter of observation times tending to infinity, provided
the renewal interval limits hold. Both processes may live on arbitrary probability spaces. -/
theorem tendstoInDistribution_renewalExcess_of_tendsto_measureReal_Ioc
    [IsProbabilityMeasure P]
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    (hlim : ∀ d : ℝ≥0, Tendsto (fun t : ℝ≥0 ↦
      (P.map (T 0)).renewalMeasure.real (Ioc t (t + d))) atTop
        (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0))⁻¹).toReal * d)))
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Z : Ω' → ℝ} (hZ : HasLaw Z (P.map (T 0)).equilibriumExcessLaw Q)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {t : ι → ℝ≥0}
    (ht : Tendsto t l atTop) :
    TendstoInDistribution (fun i ω ↦ (renewalExcess T (t i) ω : ℝ)) l
      Z (fun _ ↦ P) Q := by
  apply TendstoInDistribution.of_tendsto_cdf
    (fun i ↦ (measurable_coe_nnreal_real.comp
      (measurable_renewalExcess hT (t i))).aemeasurable) hZ.aemeasurable
  intro x
  rw [hZ.map_eq]
  exact (tendsto_cdf_renewalExcess_of_tendsto_measureReal_Ioc
    hT hindep hid hzero hmean hlim x).comp ht

/-- **Infinite-mean excess-life escape.** For i.i.d. nonnegative increments of infinite
extended mean, lattice or nonlattice, the probability that the excess life is at most `x`
tends to zero as `t → ∞` through all nonnegative real observation times. -/
theorem tendsto_measureReal_renewalExcess_le_of_mean_eq_top
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) := by
  have := hindep.isProbabilityMeasure
  have hF := (P.map (T 0)).measure_singleton_lt_one_of_lintegral_pos
    (f := fun u ↦ (u : ℝ≥0∞)) (a := 0) (by simp) (hmean ▸ ENNReal.zero_lt_top)
  have hzero : P {ω | T 0 ω = 0} < 1 := by
    rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)] at hF
  exact tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub
    hT hindep hid hzero x
    ((P.map (T 0)).tendsto_renewalFunction_add_sub_of_mean_eq_top hmean x)

/-- **Infinite-mean excess-tail escape.** For i.i.d. nonnegative increments of infinite
extended mean, lattice or nonlattice, the probability that the excess life exceeds any
fixed bound `x` tends to one as `t → ∞`. -/
theorem tendsto_measureReal_lt_renewalExcess_of_mean_eq_top
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop (𝓝 1) := by
  have := hindep.isProbabilityMeasure
  have he (t : ℝ≥0) : P.real {ω | x < renewalExcess T t ω} =
      1 - P.real {ω | renewalExcess T t ω ≤ x} := by
    rw [← probReal_compl_eq_one_sub
      (measurableSet_le (measurable_renewalExcess hT t) measurable_const)]
    congr 1
    ext ω
    simp
  simp_rw [he]
  simpa only [sub_zero] using tendsto_const_nhds.sub
    (tendsto_measureReal_renewalExcess_le_of_mean_eq_top hT hindep hid hmean x)

/-- **Limiting excess-life tail for nonlattice increments.** When the common increment law
is nonlattice and has finite extended mean, `P(x < E_t)` converges to the equilibrium
excess-life tail `(P.map (T 0)).equilibriumExcessLaw.real (Ioi x)`. Finiteness of the mean
is necessary: when the mean is infinite, `P(x < E_t) → 1` while `equilibriumExcessLaw = 0`. -/
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

/-- **Limiting excess-life distribution function for nonlattice increments.** For any
nonlattice increment law, `P(E_t ≤ x)` converges as `t → ∞` to
`(P.map (T 0)).equilibriumExcessLaw.real (Iic x)`. No finiteness assumption on the mean is
needed: when the extended mean is infinite, both the limit of `P(E_t ≤ x)` and
`equilibriumExcessLaw` are zero. -/
theorem tendsto_measureReal_renewalExcess_le
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  by_cases hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞
  · simp only [Measure.equilibriumExcessLaw_eq_zero_of_mean_eq_top _ hmean,
      measureReal_zero_apply]
    exact tendsto_measureReal_renewalExcess_le_of_mean_eq_top hT hindep hid hmean x
  · have hF := Measure.measure_singleton_zero_lt_one_of_not_isLattice hNL
    have hzero : P {ω | T 0 ω = 0} < 1 := by
      rwa [Measure.map_apply (hT 0) (measurableSet_singleton 0)] at hF
    exact tendsto_measureReal_renewalExcess_le_of_tendsto_measureReal_Ioc
      hT hindep hid hzero hmean ((P.map (T 0)).tendsto_renewalMeasure_real_Ioc hNL) x

/-- **Integrated-tail formula for the limiting excess-life distribution.** For any
nonlattice increment law, `P(E_t ≤ x)` converges to the reciprocal extended increment mean
times the integral over `(0, x]` of the increment tail `s ↦ P.real {ω | s < T 0 ω}`. -/
theorem tendsto_measureReal_renewalExcess_le_integral_tail
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hNL : ¬ (P.map (T 0)).IsLattice) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 (((∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P)⁻¹).toReal *
        ∫ s in Ioc 0 (x : ℝ), P.real {ω | s < (T 0 ω : ℝ)})) := by
  have := hindep.isProbabilityMeasure
  have htail (s : ℝ) : (P.map (T 0)).real {u | s < (u : ℝ)} =
      P.real {ω | s < (T 0 ω : ℝ)} :=
    map_measureReal_apply (hT 0)
      (measurableSet_lt measurable_const measurable_coe_nnreal_real)
  have heq : (P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)) =
      ((∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P)⁻¹).toReal *
        ∫ s in Ioc 0 (x : ℝ), P.real {ω | s < (T 0 ω : ℝ)} := by
    rw [Measure.equilibriumExcessLaw_real_Iic,
      lintegral_map measurable_coe_nnreal_ennreal (hT 0)]
    simp_rw [htail]
  rw [← heq]
  exact tendsto_measureReal_renewalExcess_le hT hindep hid hNL x

/-- **Limiting cumulative distribution function of the excess life.** For a nonlattice
increment law of finite extended mean, the real-valued CDF of `(renewalExcess T t · : ℝ)`
converges pointwise on all of `ℝ` to `cdf (P.map (T 0)).equilibriumExcessLaw`. Finiteness
of the mean is required because `cdf` is only the distribution function of a probability
measure. -/
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

/-- **Limiting distribution of the excess life.** For i.i.d. nonnegative increments whose
common law is nonlattice and has finite extended mean, the real-valued excess life
`(renewalExcess T t · : ℝ)` converges in distribution as `t → ∞` in `ℝ≥0` to any random
variable `Z` with law `(P.map (T 0)).equilibriumExcessLaw`. Precomposing via
`MeasureTheory.TendstoInDistribution.comp_tendsto` yields convergence along any family or
sequence of observation times tending to `atTop`. -/
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
