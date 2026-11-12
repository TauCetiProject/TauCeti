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
`MeasureTheory.measure_Icc_lt_top`.

A compact exhaustion also gives a countable criterion for local finiteness and for finiteness
on compact sets. This criterion is useful when checking these properties simultaneously
almost surely for a random measure.

## Main results

* `MeasureTheory.measure_Iic_lt_top`
* `MeasureTheory.measure_Ici_lt_top`
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

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
