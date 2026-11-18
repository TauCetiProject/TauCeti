/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Topology.Order.RegionBetween

/-!
# The volume of a closed region between two functions

Mathlib computes the volume of the open region `regionBetween f g s` between two measurable
functions as the Lebesgue integral of `g - f` over `s` (`volume_regionBetween_eq_lintegral'`).
This file gives the same formula for the closed region `TauCeti.closedRegionBetween f g s`, which
also contains the two graphs.

## Main results

* `TauCeti.measurableSet_closedRegionBetween`: the closed region between two measurable functions
  on a measurable set is measurable.
* `TauCeti.volume_closedRegionBetween_eq_lintegral`: its volume is `∫⁻ y in s, ofReal (g y - f y)`.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ} {s : Set α}

/-- The closed region between two measurable functions on a measurable set is measurable. -/
theorem measurableSet_closedRegionBetween (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) : MeasurableSet (closedRegionBetween f g s) := by
  rw [show closedRegionBetween f g s = {p | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} from
    ext fun _ ↦ mem_closedRegionBetween]
  exact measurableSet_region_between_cc hf hg hs

/-- The volume of the closed region between two measurable functions on a measurable set is the
Lebesgue integral of their difference. This is the closed counterpart of
`volume_regionBetween_eq_lintegral'`. -/
theorem volume_closedRegionBetween_eq_lintegral (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    μ.prod volume (closedRegionBetween f g s) = ∫⁻ y in s, ENNReal.ofReal ((g - f) y) ∂μ := by
  rw [Measure.prod_apply (measurableSet_closedRegionBetween hf hg hs), ← lintegral_indicator hs]
  congr 1
  ext x
  by_cases hx : x ∈ s
  · have hpre : Prod.mk x ⁻¹' closedRegionBetween f g s = Icc (f x) (g x) := by
      ext t
      simp [hx]
    rw [hpre, Real.volume_Icc, indicator_of_mem hx, Pi.sub_apply]
  · have hpre : Prod.mk x ⁻¹' closedRegionBetween f g s = ∅ :=
      eq_empty_of_forall_notMem fun t ht ↦ hx (mem_closedRegionBetween.1 ht).1
    rw [hpre, measure_empty, indicator_of_notMem hx]

end TauCeti
