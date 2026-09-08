/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Estimates in symmetric-difference measure

Under a finite measure, the mass of an event is a `1`-Lipschitz function of the event in the
symmetric-difference pseudometric (`abs_measureReal_sub_le_measureReal_symmDiff` in Mathlib). This
file records the estimate for an intersection: two events each within `e` of `s` have intersection
within `2e` of `s`, since the symmetric difference of the intersection with `s` lies in the union
of the two symmetric differences.

## Main results

* `TauCeti.MeasureTheory.abs_measureReal_inter_sub_lt`
-/

public section

open MeasureTheory Set

open scoped symmDiff

namespace TauCeti

namespace MeasureTheory

/-- Two events within `e` of `s` have intersection within `2e` of `s`. -/
theorem abs_measureReal_inter_sub_lt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {A B s : Set Ω}
    (hA : NullMeasurableSet A μ) (hB : NullMeasurableSet B μ) (hs : NullMeasurableSet s μ)
    {e : ℝ} (h1 : μ.real (symmDiff A s) < e) (h2 : μ.real (symmDiff B s) < e) :
    |μ.real (A ∩ B) - μ.real s| < 2 * e := by
  have hsub : symmDiff (A ∩ B) s ⊆ symmDiff A s ∪ symmDiff B s := by
    simpa only [← compl_inter, compl_symmDiff_compl] using
      (Set.union_symmDiff_subset (s := Aᶜ) (t := Bᶜ) (u := sᶜ))
  have hIS : μ.real (symmDiff (A ∩ B) s) < 2 * e :=
    calc μ.real (symmDiff (A ∩ B) s)
        ≤ μ.real (symmDiff A s ∪ symmDiff B s) := measureReal_mono hsub (by finiteness)
      _ ≤ μ.real (symmDiff A s) + μ.real (symmDiff B s) := measureReal_union_le _ _
      _ < 2 * e := by linarith
  exact lt_of_le_of_lt (abs_measureReal_sub_le_measureReal_symmDiff (hA.inter hB) hs) hIS

end MeasureTheory

end TauCeti
