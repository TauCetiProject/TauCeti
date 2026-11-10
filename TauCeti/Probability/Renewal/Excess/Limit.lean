/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Excess.Basic
public import TauCeti.Probability.Renewal.Equilibrium
public import TauCeti.Probability.Renewal.IntervalLimit
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cdf

/-!
# Excess-life convergence from renewal interval limits

For finite-mean interarrival laws, Blackwell interval limits imply convergence of the
excess tail, distribution function, and law to the equilibrium excess-life distribution.

The interval limit is an explicit input. No nonlattice Blackwell theorem is asserted here,
and the result must not be applied to a lattice law merely because its mean is finite.
Zero increments are allowed. The distributional statement uses the real-valued excess
and any realization of the equilibrium law, along any countably generated filter of
observation times tending to infinity.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI, the limiting excess-life theorem.
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
  simp_rw [measureReal_lt_renewalExcess hindep hid]
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

end TauCeti.Probability
