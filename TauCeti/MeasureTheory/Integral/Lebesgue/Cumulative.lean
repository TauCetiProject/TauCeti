/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Topology.Order.Cadlag
public import TauCeti.MeasureTheory.Measure.Interval
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Order.IsLUB

/-!
# Cumulative lower integrals: left continuity and budget truncation

Cumulative nonnegative integrals over open initial segments are left-continuous, even when
infinite. For an atomless measure the same holds for closed initial segments. No integrability
or measurability of the integrand is needed. In particular, accumulated square energy has
left-continuous extended-valued paths before any moment or local-integrability assumption.

Turning an integrand off wherever its cumulative mass exceeds a budget bounds its total
mass by that budget. This bound permits finite-energy truncations even for inputs whose
original cumulative mass becomes infinite.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace MeasureTheory.Measure

variable {ι : Type*} [LinearOrder ι] [DenselyOrdered ι] [TopologicalSpace ι]
  [OrderTopology ι] [FirstCountableTopology ι] [MeasurableSpace ι]

/-- The lower integral over an open initial segment is left-continuous, including at infinite
values. Neither finiteness nor measurability of the integrand is required. -/
theorem isLeftContinuous_setLIntegral_Iio (μ : Measure ι) (f : ι → ℝ≥0∞) :
    IsLeftContinuous (fun t ↦ ∫⁻ s in Iio t, f s ∂μ) := by
  intro t
  by_cases ht : ∃ a, a < t
  · obtain ⟨a, ha⟩ := ht
    obtain ⟨u, hu, hut, hlim⟩ := exists_seq_strictMono_tendsto' ha
    have hcover : (⋃ n, Iio (u n)) = Iio t :=
      (isLUB_of_tendsto_atTop hu.monotone hlim).iUnion_Iio_eq
    have hsup : (∫⁻ s in Iio t, f s ∂μ) = ⨆ n, ∫⁻ s in Iio (u n), f s ∂μ := by
      rw [← hcover, setLIntegral_iUnion_of_directed f]
      exact (monotone_Iio.comp hu.monotone).directed_le
    apply tendsto_order.2
    constructor
    · intro b hb
      dsimp only at hb
      rw [hsup, lt_iSup_iff] at hb
      obtain ⟨n, hn⟩ := hb
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (hut n).2)] with s hs
      exact hn.trans_le (lintegral_mono_set (Iio_subset_Iio hs.le))
    · intro b hb
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (lintegral_mono_set (Iio_subset_Iio hs.le)).trans_lt hb
  · have he : Iio t = (∅ : Set ι) :=
      Set.Iio_eq_empty_iff.2 fun s _ ↦ le_of_not_gt fun hs ↦ ht ⟨s, hs⟩
    simp [he, ContinuousWithinAt]

/-- For an atomless measure, the lower integral over a closed initial segment is
left-continuous, without a finiteness assumption. -/
theorem isLeftContinuous_setLIntegral_Iic (μ : Measure ι) [NullSingletonClass μ] (f : ι → ℝ≥0∞) :
    IsLeftContinuous (fun t ↦ ∫⁻ s in Iic t, f s ∂μ) := by
  simpa only [← restrict_Iio_eq_restrict_Iic] using
    isLeftContinuous_setLIntegral_Iio μ f

omit [DenselyOrdered ι] [FirstCountableTopology ι] in
/-- Truncating a nonnegative integrand when its accumulated mass exceeds `C` bounds its
total mass by `C`. The original accumulated mass may become infinite. -/
theorem lintegral_indicator_setLIntegral_Iic_le [OpensMeasurableSpace ι]
    [SecondCountableTopology ι] (μ : Measure ι) (f : ι → ℝ≥0∞) (C : ℝ≥0∞) :
    ∫⁻ t, {u | ∫⁻ v in Iic u, f v ∂μ ≤ C}.indicator f t ∂μ ≤ C := by
  let ν := μ.withDensity f
  have hν (t : ι) : ν (Iic t) = ∫⁻ v in Iic t, f v ∂μ :=
    withDensity_apply _ measurableSet_Iic
  have hmono : Monotone (fun t ↦ ν (Iic t)) :=
    fun _ _ h ↦ measure_mono (Iic_subset_Iic.mpr h)
  have hD : MeasurableSet {t | ν (Iic t) ≤ C} := hmono.measurable measurableSet_Iic
  have hbound := ν.measure_le_of_forall_measure_Iic_le
    (s := {t | ν (Iic t) ≤ C}) (C := C) (fun _ h ↦ h)
  rw [withDensity_apply f hD, ← lintegral_indicator hD] at hbound
  simpa only [hν] using hbound

end MeasureTheory.Measure
