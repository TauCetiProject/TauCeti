/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Real
import TauCeti.Data.Set.SymmDiff

/-!
# Estimates in symmetric-difference measure

Under a finite measure, the mass of an event is a `1`-Lipschitz function of the event in the
symmetric-difference pseudometric (`abs_measureReal_sub_le_measureReal_symmDiff` in Mathlib). This
file records the estimate for an intersection: the mass of `A ∩ B` differs from that of `s` by at
most the sum of the symmetric-difference masses of `A` and `B` against `s`, since the symmetric
difference of the intersection with `s` lies in the union of the two symmetric differences.

## Main results

* `TauCeti.MeasureTheory.abs_measureReal_inter_sub_le_of_measureReal_symmDiff`
-/

public section

open MeasureTheory Set

open scoped symmDiff

namespace TauCeti

namespace MeasureTheory

/-- The mass of `A ∩ B` is within the sum of the symmetric-difference masses of `A` and `B`
against `s` of the mass of `s`. -/
theorem abs_measureReal_inter_sub_le_of_measureReal_symmDiff {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {A B s : Set Ω}
    (hA : NullMeasurableSet A μ) (hB : NullMeasurableSet B μ) (hs : NullMeasurableSet s μ) :
    |μ.real (A ∩ B) - μ.real s| ≤ μ.real (symmDiff A s) + μ.real (symmDiff B s) :=
  calc |μ.real (A ∩ B) - μ.real s|
      ≤ μ.real (symmDiff (A ∩ B) s) :=
        abs_measureReal_sub_le_measureReal_symmDiff (hA.inter hB) hs
    _ ≤ μ.real (symmDiff A s ∪ symmDiff B s) :=
        measureReal_mono TauCeti.Set.inter_symmDiff_subset (by finiteness)
    _ ≤ μ.real (symmDiff A s) + μ.real (symmDiff B s) := measureReal_union_le _ _

end MeasureTheory

end TauCeti
