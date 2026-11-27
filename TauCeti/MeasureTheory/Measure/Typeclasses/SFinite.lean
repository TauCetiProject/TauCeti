/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# σ-finiteness of restrictions to countable unions and σ-compact sets

A measure that is finite on compact sets is σ-finite on a σ-compact space
(`MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts`). This file records the relative
version: such a measure has σ-finite restriction to every σ-compact set, even when the measure
itself is not σ-finite. For instance, a Haar measure on a locally compact group that is not
σ-compact is not σ-finite, but its restriction to a σ-compact open subgroup is, so Fubini's
theorem applies there. No separation or measurability assumptions on the space are needed:
compact sets are replaced by their measurable envelopes.

## Main results

* `IsSigmaCompact.sigmaFinite_restrict`: a measure that is finite on compact sets has σ-finite
  restriction to every σ-compact set.
* `IsSigmaCompact.sigmaFinite_comap_subtype`: a measure that is finite on compact sets has σ-finite
  pullback `μ.comap (↑)` to every measurable σ-compact set.
* `Measure.sigmaFinite_restrict_iUnion`: the restriction to a countable union of finite-measure
  sets is sigma-finite.
* `TauCeti.ae_eq_of_forall_measure_inter_eq`: for a σ-finite measure, null measurable sets with the
  same intersections with all sets of finite measure are a.e. equal.
-/

public section

open Set MeasureTheory
open scoped ENNReal

/-- Restriction to a countable union of finite-measure sets is sigma-finite. -/
theorem MeasureTheory.Measure.sigmaFinite_restrict_iUnion {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : ℕ → Set α) (hfin : ∀ n, μ (s n) < ∞) :
    SigmaFinite (μ.restrict (⋃ n, s n)) := by
  -- Cover the supporting sets by measurable envelopes of the same finite measure.
  let T := fun n ↦ toMeasurable μ (s n)
  have hsT : ⋃ n, s n ⊆ ⋃ n, T n := iUnion_mono fun n ↦ subset_toMeasurable μ (s n)
  refine ⟨⟨⟨fun n ↦ T n ∪ (⋃ n, T n)ᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
  · have hmeas : MeasurableSet (T n ∪ (⋃ n, T n)ᶜ) :=
      (measurableSet_toMeasurable μ _).union (MeasurableSet.iUnion fun n ↦
        measurableSet_toMeasurable μ _).compl
    rw [Measure.restrict_apply hmeas, union_inter_distrib_right,
      (disjoint_compl_left.mono_right hsT).inter_eq, union_empty]
    exact (measure_mono inter_subset_left).trans_lt
      ((measure_toMeasurable (s n)).trans_lt (hfin n))
  · rw [← iUnion_union, union_compl_self]

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] {μ : Measure α}

/-- A measure that is finite on compact sets has σ-finite restriction to every σ-compact set. -/
theorem IsSigmaCompact.sigmaFinite_restrict [IsFiniteMeasureOnCompacts μ] {s : Set α}
    (hs : IsSigmaCompact s) : SigmaFinite (μ.restrict s) := by
  obtain ⟨K, hK, rfl⟩ := hs
  exact μ.sigmaFinite_restrict_iUnion K fun n ↦ (hK n).measure_lt_top

/-- A measure that is finite on compact sets has σ-finite pullback `μ.comap (↑)` to every measurable
σ-compact set. -/
theorem IsSigmaCompact.sigmaFinite_comap_subtype [IsFiniteMeasureOnCompacts μ] {s : Set α}
    (hs : IsSigmaCompact s) (hsm : MeasurableSet s) :
    SigmaFinite (μ.comap ((↑) : s → α)) := by
  have hσ : SigmaFinite (μ.restrict s) := hs.sigmaFinite_restrict
  rw [← map_comap_subtypeVal hsm] at hσ
  exact SigmaFinite.of_map _ measurable_subtypeVal.aemeasurable hσ

namespace TauCeti

/-- For a σ-finite measure, two null measurable sets that meet every null measurable set of finite
measure in the same measure are almost everywhere equal. -/
theorem ae_eq_of_forall_measure_inter_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] {u v : Set α} (hu : NullMeasurableSet u μ) (hv : NullMeasurableSet v μ)
    (h : ∀ E, NullMeasurableSet E μ → μ E ≠ ∞ → μ (u ∩ E) = μ (v ∩ E)) : u =ᵐ[μ] v := by
  -- Test `u \ v` against its own intersections with the finite-measure spanning sets.
  have diff_null {u v : Set α} (hu : NullMeasurableSet u μ) (hv : NullMeasurableSet v μ)
      (h : ∀ E, NullMeasurableSet E μ → μ E ≠ ∞ → μ (u ∩ E) = μ (v ∩ E)) : μ (u \ v) = 0 := by
    refine (isCountablySpanning_spanningSets μ).null_of_forall_inter_null ?_
    rintro _ ⟨n, rfl⟩
    have hE : NullMeasurableSet ((u \ v) ∩ spanningSets μ n) μ :=
      (hu.diff hv).inter (measurableSet_spanningSets μ n).nullMeasurableSet
    have hμE : μ ((u \ v) ∩ spanningSets μ n) ≠ ∞ :=
      ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
    rw [← inter_eq_right.2 (fun x hx ↦ hx.1.1 : (u \ v) ∩ spanningSets μ n ⊆ u), h _ hE hμE]
    exact measure_mono_null (fun x hx ↦ (hx.2.1.2 hx.1).elim) measure_empty
  exact ae_eq_set.2 ⟨diff_null hu hv h, diff_null hv hu fun E hE hμE ↦ (h E hE hμE).symm⟩

end TauCeti
