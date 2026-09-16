/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Basic
import TauCeti.Data.Set.SymmDiff

/-!
# Estimates in symmetric-difference outer measure

For sets of finite outer measure, the mass of a set changes by at most the mass of its symmetric
difference with another set. The intersection estimate follows by containing its symmetric
difference in the union of the two input symmetric differences.

These statements use only monotonicity and subadditivity, so they are stated for
`OuterMeasureClass`, which covers both outer measures and measures without requiring a measurable
space. They supply the approximation estimates for the Hewitt–Savage zero-one criterion in
`TauCeti/MeasureTheory/Measure/ZeroOne.lean`.

## Main results

* `TauCeti.MeasureTheory.abs_toReal_sub_le_toReal_symmDiff`
* `TauCeti.MeasureTheory.abs_toReal_inter_sub_le_toReal_symmDiff_add`
-/

public section

open MeasureTheory Set
open scoped ENNReal symmDiff

namespace TauCeti.MeasureTheory

variable {Ω F : Type*} [FunLike F (Set Ω) ℝ≥0∞] [OuterMeasureClass F Ω] {μ : F}

/-- For sets of finite outer measure, the difference of their masses is bounded by the mass
of their symmetric difference. No measurability or additivity is needed.

This generalizes Mathlib's `MeasureTheory.abs_measureReal_sub_le_measureReal_symmDiff'`
and its finite-measure wrapper `MeasureTheory.abs_measureReal_sub_le_measureReal_symmDiff`. -/
theorem abs_toReal_sub_le_toReal_symmDiff {s t : Set Ω} (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) :
    |(μ s).toReal - (μ t).toReal| ≤ (μ (s ∆ t)).toReal := by
  have hle (a b : Set Ω) (ha : μ a ≠ ∞) (hb : μ b ≠ ∞) :
      (μ a).toReal ≤ (μ (a ∆ b)).toReal + (μ b).toReal := by
    have hab : μ (a ∆ b) ≠ ∞ := ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨ha, hb⟩)
      ((measure_mono symmDiff_subset_union).trans (measure_union_le a b))
    calc
      (μ a).toReal ≤ (μ ((a ∆ b) ∪ b)).toReal :=
        ENNReal.toReal_mono
          (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hab, hb⟩) (measure_union_le _ _))
          (measure_mono (le_symmDiff_sup_right a b))
      _ ≤ (μ (a ∆ b) + μ b).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hab, hb⟩) (measure_union_le _ _)
      _ = _ := ENNReal.toReal_add hab hb
  have hst := hle s t hs ht
  have hts := hle t s ht hs
  rw [symmDiff_comm t s] at hts
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- If `s` and the two symmetric differences have finite outer measure, the mass of `A ∩ B`
is within their summed symmetric-difference masses of the mass of `s`. -/
theorem abs_toReal_inter_sub_le_toReal_symmDiff_add {A B s : Set Ω}
    (hs : μ s ≠ ∞) (hA : μ (A ∆ s) ≠ ∞) (hB : μ (B ∆ s) ≠ ∞) :
    |(μ (A ∩ B)).toReal - (μ s).toReal| ≤ (μ (A ∆ s)).toReal + (μ (B ∆ s)).toReal := by
  have hAfin : μ A ≠ ∞ := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hA, hs⟩)
    ((measure_mono (le_symmDiff_sup_right A s)).trans (measure_union_le _ _))
  have hunion : μ ((A ∆ s) ∪ (B ∆ s)) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hA, hB⟩) (measure_union_le _ _)
  calc
    |(μ (A ∩ B)).toReal - (μ s).toReal| ≤ (μ ((A ∩ B) ∆ s)).toReal :=
      abs_toReal_sub_le_toReal_symmDiff
        (ne_top_of_le_ne_top hAfin (measure_mono inter_subset_left)) hs
    _ ≤ (μ ((A ∆ s) ∪ (B ∆ s))).toReal :=
      ENNReal.toReal_mono hunion (measure_mono Set.inter_symmDiff_subset)
    _ ≤ (μ (A ∆ s) + μ (B ∆ s)).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA, hB⟩) (measure_union_le _ _)
    _ = _ := ENNReal.toReal_add hA hB

end TauCeti.MeasureTheory
