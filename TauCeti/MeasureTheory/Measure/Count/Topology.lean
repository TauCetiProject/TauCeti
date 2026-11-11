/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Counting measure on discrete spaces

Counting measure is finite on compact sets and inner regular on finite-measure sets in a
discrete space. On a discrete group it is therefore a Haar measure. These instances allow
regular representations on counting-measure L² spaces without a countability assumption.
-/

public section

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

/-- Counting measure gives positive mass to every nonempty open set. -/
instance count_isOpenPosMeasure : (count : Measure X).IsOpenPosMeasure where
  open_pos _ _ hs := count_ne_zero hs

variable [DiscreteTopology X] [MeasurableSingletonClass X]

/-- Compact sets in a discrete space have finite counting measure. -/
instance count_isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts (count : Measure X) where
  lt_top_of_isCompact _ hs := count_apply_lt_top.mpr hs.finite_of_discrete

/-- Finite-measure sets for counting measure are already compact in a discrete space. -/
instance count_innerRegularCompactLTTop : (count : Measure X).InnerRegularCompactLTTop where
  innerRegular := by
    intro s hs r hr
    exact ⟨s, Set.Subset.rfl, (count_apply_lt_top.mp (lt_top_iff_ne_top.mpr hs.2)).isCompact, hr⟩

/-- Counting measure is a Haar measure on a discrete group. -/
instance count_isHaarMeasure [Group X] [MeasurableMul X] :
    (count : Measure X).IsHaarMeasure where

end MeasureTheory.Measure
