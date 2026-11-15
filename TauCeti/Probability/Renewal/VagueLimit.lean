/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Measure
public import TauCeti.MeasureTheory.Measure.Vague
public import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Interval masses of constant vague renewal limits

If translated renewal measures converge against continuous compactly supported tests to a
constant multiple of Lebesgue measure, then their backward-window masses converge to that
constant times the window length. This bridges vague limits and renewal-increment limits.
The windows are left-open and right-closed, so genuine arrivals at the observation time
are retained, even when the interarrival law has an atom at zero.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI.
-/

public section

open Filter Set Topology
open scoped ENNReal NNReal CompactlySupported

namespace MeasureTheory.Measure

/-- A constant vague limit of translated renewal measures gives the corresponding limit
for backward-window masses. Zero increments and infinite interarrival means are allowed. -/
theorem tendsto_renewalMeasure_Ioc_of_tendsto_integral_compactlySupported
    {ι : Type*} {l : Filter ι} (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hF : F {0} < 1) {t : ι → ℝ≥0} (ht : Tendsto t l atTop) (c : ℝ≥0)
    (h : ∀ f : C_c(ℝ, ℝ),
      Tendsto (fun i ↦ ∫ x, f x ∂F.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t i))
        l (𝓝 (∫ x, f x ∂(c • (volume : Measure ℝ))))) (u : ℝ≥0) :
    Tendsto (fun i ↦ F.renewalMeasure (Ioc (t i - u) (t i))) l (𝓝 (c * u : ℝ≥0∞)) := by
  by_cases hu : u = 0
  · simpa only [hu, tsub_zero, Ioc_self, measure_empty, ENNReal.coe_zero, mul_zero]
      using (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0∞)) l (𝓝 0))
  have hu' : -(u : ℝ) < 0 := neg_lt_zero.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hu))
  let := F.isLocallyFiniteMeasure_renewalMeasure hF
  have (i : ι) : IsFiniteMeasureOnCompacts
      (F.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t i)) :=
    F.renewalMeasure.isFiniteMeasureOnCompacts_map_of_isProperMap
      (((Homeomorph.subRight (t i : ℝ)).isClosedEmbedding.comp
        NNReal.isClosedEmbedding_coe).isProperMap)
  have hmass := tendsto_measure_of_null_frontier_of_tendsto_integral_compactlySupported h
    measurableSet_Ioc (by rw [closure_Ioc hu'.ne]; exact isCompact_Icc)
    (by rw [frontier_Ioc hu', smul_apply,
          ((Set.finite_singleton _).insert _).measure_zero (volume : Measure ℝ), smul_zero])
  have hlim : Tendsto
      (fun i ↦ F.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t i) (Ioc (-(u : ℝ)) 0))
      l (𝓝 (c * u : ℝ≥0∞)) := by
    simpa only [smul_apply, Real.volume_Ioc, sub_neg_eq_add, zero_add,
      ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul] using hmass
  apply hlim.congr'
  filter_upwards [ht.eventually (eventually_ge_atTop u)] with i hi
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioc]
  congr 1
  ext s
  simp only [mem_preimage, mem_Ioc, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe,
    NNReal.coe_sub hi]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

end MeasureTheory.Measure
