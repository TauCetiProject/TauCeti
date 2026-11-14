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
Only finiteness of the extended mean and almost-everywhere measurability (via `IdentDistrib`) are
required; the positive mean follows from the nondegeneracy assumption on the law. -/
theorem tendsto_measureReal_lt_renewalExcess_of_tendsto_measureReal_Ioc
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : (P.map (T 0)) {0} < 1)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    (hlim : ∀ d : ℝ≥0, Tendsto (fun t : ℝ≥0 ↦
      (P.map (T 0)).renewalMeasure.real (Ioc t (t + d))) atTop
        (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0))⁻¹).toReal * d))) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  obtain ⟨T', hT', hindep', hid', hmap, hae⟩ :=
    exists_measurable_iIndepFun_renewalExcess_eq_ae hindep hid
  have hzero' : P {ω | T' 0 ω = 0} < 1 := by
    rwa [← hmap, Measure.map_apply (hT' 0) (measurableSet_singleton 0)] at hzero
  have hcongr (t : ℝ≥0) :
      P.real {ω | x < renewalExcess T t ω} = P.real {ω | x < renewalExcess T' t ω} := by
    simpa only [preimage_ofPred_eq] using
      measureReal_preimage_renewalExcess_of_ae_eq hae {u | x < u} t
  have htail : Antitone (fun u : ℝ≥0 ↦ (P.map (T 0)).real (Ioi (u + x))) :=
    fun _ _ h ↦ measureReal_mono (Ioi_subset_Ioi (by gcongr))
  simp_rw [hcongr, measureReal_lt_renewalExcess hT' hindep' hid' hzero', hmap]
  rw [Measure.equilibriumExcessLaw_real_Ioi_eq_integral_tail_add]
  exact (P.map (T 0)).tendsto_renewalConv_of_tendsto_measureReal_Ioc hzero hlim
    htail (fun _ ↦ measureReal_nonneg)
    ((P.map (T 0)).integrableOn_Ioi_measureReal_tail_add x hmean)

/-- Renewal interval limits imply convergence of the excess distribution function at every
nonnegative threshold. The limiting measure is the normalized integrated interarrival tail. -/
theorem tendsto_measureReal_renewalExcess_le_of_tendsto_measureReal_Ioc
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : (P.map (T 0)) {0} < 1)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    (hlim : ∀ d : ℝ≥0, Tendsto (fun t : ℝ≥0 ↦
      (P.map (T 0)).renewalMeasure.real (Ioc t (t + d))) atTop
        (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0))⁻¹).toReal * d))) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop
      (𝓝 ((P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)))) := by
  have := hindep.isProbabilityMeasure
  have := (P.map (T 0)).isProbabilityMeasure_equilibriumExcessLaw_of_measure_singleton_lt_one
    hzero hmean
  simp_rw [measureReal_renewalExcess_le_eq_one_sub (fun n ↦ (hid n).aemeasurable_fst) _ x]
  have hcomp : (P.map (T 0)).equilibriumExcessLaw.real (Iic (x : ℝ)) =
      1 - (P.map (T 0)).equilibriumExcessLaw.real (Ioi (x : ℝ)) := by
    rw [← probReal_compl_eq_one_sub measurableSet_Ioi, compl_Ioi]
  rw [hcomp]
  exact tendsto_const_nhds.sub
    (tendsto_measureReal_lt_renewalExcess_of_tendsto_measureReal_Ioc
      hindep hid hzero hmean hlim x)

/-- Renewal interval limits give convergence of the CDF of the real-valued excess at every
real threshold, including negative thresholds and zero. This also supplies the CDF input
for convergence in distribution to any realization of the equilibrium excess-life law. -/
theorem tendsto_cdf_renewalExcess_of_tendsto_measureReal_Ioc
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : (P.map (T 0)) {0} < 1)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) ≠ ∞)
    (hlim : ∀ d : ℝ≥0, Tendsto (fun t : ℝ≥0 ↦
      (P.map (T 0)).renewalMeasure.real (Ioc t (t + d))) atTop
        (𝓝 (((∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0))⁻¹).toReal * d)))
    (x : ℝ) :
    Tendsto (fun t ↦ cdf (P.map (fun ω ↦ (renewalExcess T t ω : ℝ))) x) atTop
      (𝓝 (cdf (P.map (T 0)).equilibriumExcessLaw x)) := by
  have := hindep.isProbabilityMeasure
  have := (P.map (T 0)).isProbabilityMeasure_equilibriumExcessLaw_of_measure_singleton_lt_one
    hzero hmean
  have hT (n : ℕ) : AEMeasurable (T n) P := (hid n).aemeasurable_fst
  have hae (s : ℝ≥0) : AEMeasurable (fun ω ↦ (renewalExcess T s ω : ℝ)) P := by fun_prop
  simp_rw [Measure.cdf_map P _ (hae _), measureReal_preimage_coe_renewalExcess_Iic,
    cdf_eq_real]
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
along any countably generated filter of observation times tending to infinity, provided
the renewal interval limits hold. Both processes may live on arbitrary probability spaces. -/
theorem tendstoInDistribution_renewalExcess_of_tendsto_measureReal_Ioc
    [IsProbabilityMeasure P]
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : (P.map (T 0)) {0} < 1)
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
  have hT (n : ℕ) : AEMeasurable (T n) P := (hid n).aemeasurable_fst
  apply TendstoInDistribution.of_tendsto_cdf (fun i ↦ by fun_prop) hZ.aemeasurable
  intro x
  rw [hZ.map_eq]
  exact (tendsto_cdf_renewalExcess_of_tendsto_measureReal_Ioc
    hindep hid hzero hmean hlim x).comp ht

end TauCeti.Probability
