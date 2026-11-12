/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.UpperLower.Basic

/-!
# Real measures of lower sets

Lower sets in a linear order are nested. Consequently, the mass of their intersection is the
minimum of their masses, and the mass of their difference is the positive part of the difference
of their masses. These identities allow interval truncations to treat open and closed endpoints
uniformly, without discarding endpoint atoms.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [LinearOrder α] [MeasurableSpace α] (μ : Measure α) {s t : Set α}

/-- The real measure of the intersection of two finite-mass lower sets is the minimum of their
real measures. -/
theorem measureReal_inter_of_isLowerSet (hs : IsLowerSet s) (ht : IsLowerSet t)
    (hμs : μ s ≠ ∞ := by finiteness) (hμt : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∩ t) = min (μ.real s) (μ.real t) := by
  rcases hs.total ht with h | h
  · rw [inter_eq_left.mpr h, min_eq_left (measureReal_mono h hμt)]
  · rw [inter_eq_right.mpr h, min_eq_right (measureReal_mono h hμs)]

/-- Removing a measurable lower set from another lower set, both of finite mass, subtracts their
real measures, with a lower bound of zero. -/
theorem measureReal_sdiff_of_isLowerSet (hs : IsLowerSet s) (ht : IsLowerSet t)
    (hmt : MeasurableSet t) (hμs : μ s ≠ ∞ := by finiteness)
    (hμt : μ t ≠ ∞ := by finiteness) :
    μ.real (s \ t) = max (μ.real s - μ.real t) 0 := by
  rcases hs.total ht with h | h
  · rw [sdiff_eq_empty.mpr h, measureReal_empty,
      max_eq_right (sub_nonpos.mpr (measureReal_mono h hμt))]
  · rw [measureReal_sdiff h hmt hμs,
      max_eq_left (sub_nonneg.mpr (measureReal_mono h hμs))]

end MeasureTheory.Measure
