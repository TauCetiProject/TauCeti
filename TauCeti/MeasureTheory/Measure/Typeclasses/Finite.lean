/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Criteria and interval bounds for locally finite measures

In an order with a least element whose closed intervals are compact, such as `ℝ≥0` or `ℕ`, a
locally finite measure gives finite mass to each interval `Iic a = Icc ⊥ a`. Dually, with a
greatest element, it gives finite mass to each `Ici a`. These complement Mathlib's
`MeasureTheory.measure_Icc_lt_top`. Measures finite on compact sets have finite restrictions to
bounded left-open, right-closed intervals.

A compact exhaustion also gives a countable criterion for local finiteness and for finiteness
on compact sets. This criterion is useful when checking these properties simultaneously
almost surely for a random measure.

A sum of two locally finite measures is locally finite. Finiteness on compact sets passes to
smaller measures, a sum of two measures is finite on compact sets exactly when both summands
are, and multiplication by a nonzero nonnegative real both preserves and reflects it.

## Main results

* `MeasureTheory.measure_Iic_lt_top`
* `MeasureTheory.measure_Ici_lt_top`
* `MeasureTheory.Measure.isLocallyFiniteMeasure_of_measure_Iic_lt_top`
* `MeasureTheory.Measure.isLocallyFiniteMeasure_of_measure_Ici_lt_top`
* `MeasureTheory.IsLocallyFiniteMeasure.add`: a sum of locally finite measures is locally finite.
* `MeasureTheory.isFiniteMeasureOnCompacts_of_le`: finiteness on compact sets passes to smaller
  measures.
* `MeasureTheory.isFiniteMeasureOnCompacts_add_iff`: a sum is finite on compact sets if and only
  if both summands are.
* `MeasureTheory.isFiniteMeasureOnCompacts_smul_nnreal_iff`: scaling by a nonzero scalar
  preserves and reflects finiteness on compact sets.
-/

public section

open Set
open scoped ENNReal NNReal

namespace MeasureTheory

section CompactIntervals

variable {α : Type*} [Preorder α] [TopologicalSpace α] [CompactIccSpace α]
  [MeasurableSpace α]

/-- A measure finite on compact sets is finite on each bounded left-open, right-closed interval. -/
instance Measure.isFiniteMeasure_restrict_Ioc (μ : Measure α) [IsFiniteMeasureOnCompacts μ]
    (a b : α) : IsFiniteMeasure (μ.restrict (Ioc a b)) :=
  ⟨by simpa using
    (measure_mono Ioc_subset_Icc_self).trans_lt (isCompact_Icc.measure_lt_top (μ := μ))⟩

end CompactIntervals

/-- A measure on a linearly ordered space is locally finite if every closed initial interval
has finite mass and strict lower rays are open. -/
theorem Measure.isLocallyFiniteMeasure_of_measure_Iic_lt_top {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [ClosedIciTopology α] [MeasurableSpace α] (μ : Measure α)
    (hfin : ∀ t : α, μ (Iic t) < ∞) : IsLocallyFiniteMeasure μ := by
  refine ⟨fun t ↦ ?_⟩
  by_cases ht : ∃ u, t < u
  · obtain ⟨u, hu⟩ := ht
    exact ⟨Iic u, Iic_mem_nhds hu, hfin u⟩
  · exact ⟨Iic t, Filter.mem_of_superset Filter.univ_mem
      (fun u _ ↦ le_of_not_gt (fun hu ↦ ht ⟨u, hu⟩)), hfin t⟩

/-- A measure on a linearly ordered space is locally finite if every closed final interval
has finite mass and strict upper rays are open. -/
theorem Measure.isLocallyFiniteMeasure_of_measure_Ici_lt_top {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [ClosedIicTopology α] [MeasurableSpace α] (μ : Measure α)
    (hfin : ∀ t : α, μ (Ici t) < ∞) : IsLocallyFiniteMeasure μ :=
  μ.isLocallyFiniteMeasure_of_measure_Iic_lt_top (α := αᵒᵈ) hfin

/-- Scaling a locally finite measure by a finite extended nonnegative scalar preserves
local finiteness. -/
instance isLocallyFiniteMeasureSMulCoeNNReal {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] (μ : Measure α) [IsLocallyFiniteMeasure μ] (c : ℝ≥0) :
    IsLocallyFiniteMeasure ((c : ℝ≥0∞) • μ) :=
  μ.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top

/-- The sum of two locally finite measures is locally finite. -/
instance IsLocallyFiniteMeasure.add {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ ν : Measure α) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] :
    IsLocallyFiniteMeasure (μ + ν) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U, hU, hμU⟩ := μ.finiteAt_nhds x
  obtain ⟨W, hW, hνW⟩ := ν.finiteAt_nhds x
  refine ⟨U ∩ W, Filter.inter_mem hU hW, ?_⟩
  rw [add_apply]
  exact ENNReal.add_lt_top.mpr ⟨(measure_mono inter_subset_left).trans_lt hμU,
    (measure_mono inter_subset_right).trans_lt hνW⟩

/-- The sum of two measures that are finite on compact sets is finite on compact sets. -/
instance IsFiniteMeasureOnCompacts.add {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (μ + ν) :=
  ⟨fun _ hK ↦ by simp [hK.measure_lt_top]⟩

/-- A measure below a measure that is finite on compact sets is finite on compact sets. -/
theorem isFiniteMeasureOnCompacts_of_le {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : Measure α} (ν : Measure α) [IsFiniteMeasureOnCompacts ν] (h : μ ≤ ν) :
    IsFiniteMeasureOnCompacts μ :=
  ⟨fun _ hK ↦ (h _).trans_lt hK.measure_lt_top⟩

/-- A sum of two measures is finite on compact sets if and only if both summands are. -/
theorem isFiniteMeasureOnCompacts_add_iff {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ ν : Measure α} :
    IsFiniteMeasureOnCompacts (μ + ν) ↔ IsFiniteMeasureOnCompacts μ ∧ IsFiniteMeasureOnCompacts ν :=
  ⟨fun _ ↦ ⟨isFiniteMeasureOnCompacts_of_le (μ + ν) (Measure.le_add_right le_rfl),
    isFiniteMeasureOnCompacts_of_le (μ + ν) (Measure.le_add_left le_rfl)⟩,
    fun ⟨_, _⟩ ↦ inferInstance⟩

/-- Scaling by a nonzero nonnegative real preserves and reflects finiteness on compact sets. -/
theorem isFiniteMeasureOnCompacts_smul_nnreal_iff {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} {c : ℝ≥0} (hc : c ≠ 0) :
    IsFiniteMeasureOnCompacts (c • μ) ↔ IsFiniteMeasureOnCompacts μ := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  simpa [smul_smul, inv_mul_cancel₀ hc] using IsFiniteMeasureOnCompacts.smul_nnreal (c • μ) c⁻¹

variable {α : Type*} [Preorder α] [TopologicalSpace α] [CompactIccSpace α]
  {m : MeasurableSpace α} {μ : Measure α} [IsLocallyFiniteMeasure μ] {a : α}

/-- A locally finite measure gives finite mass to `Iic a` in an order with a least element whose
closed intervals are compact. -/
theorem measure_Iic_lt_top [OrderBot α] : μ (Iic a) < ∞ := by
  rw [← Icc_bot]
  exact measure_Icc_lt_top

/-- A locally finite measure gives finite mass to `Ici a` in an order with a greatest element
whose closed intervals are compact. -/
theorem measure_Ici_lt_top [OrderTop α] : μ (Ici a) < ∞ := by
  rw [← Icc_top]
  exact measure_Icc_lt_top

end MeasureTheory

namespace CompactExhaustion

open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- Local finiteness can be tested on the countably many sets of a compact exhaustion. -/
theorem isLocallyFiniteMeasure_iff (K : CompactExhaustion X) (μ : Measure X) :
    IsLocallyFiniteMeasure μ ↔ ∀ n, μ (K n) < ∞ := by
  refine ⟨fun _ n => (K.isCompact n).measure_lt_top, fun h => ⟨fun x => ?_⟩⟩
  obtain ⟨n, hn⟩ := K.exists_mem_nhds x
  exact ⟨K n, hn, h n⟩

/-- Finiteness on compact sets can be tested on any compact exhaustion. -/
theorem isFiniteMeasureOnCompacts_iff (K : CompactExhaustion X) (μ : Measure X) :
    IsFiniteMeasureOnCompacts μ ↔ ∀ n, μ (K n) < ∞ := by
  refine ⟨fun _ n => (K.isCompact n).measure_lt_top, fun h => ⟨fun s hs => ?_⟩⟩
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hs
  exact (measure_mono hn).trans_lt (h n)

end CompactExhaustion
