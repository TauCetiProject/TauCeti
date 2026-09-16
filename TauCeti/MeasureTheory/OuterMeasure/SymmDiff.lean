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

For a finite outer measure, the mass of a set changes by at most the mass of its symmetric
difference with another set. The intersection estimate follows by containing its symmetric
difference in the union of the two input symmetric differences.

These statements use only monotonicity and subadditivity, so they are stated for
`OuterMeasureClass`, which covers both outer measures and measures without requiring a measurable
space. They supply the approximation estimates for the Hewitt–Savage zero-one criterion in
`TauCeti/MeasureTheory/OuterMeasure/ZeroOne.lean`.

## Main results

* `TauCeti.MeasureTheory.abs_toReal_sub_le_toReal_symmDiff`
* `TauCeti.MeasureTheory.abs_toReal_inter_sub_le_toReal_symmDiff_add`
-/

public section

open MeasureTheory Set
open scoped ENNReal symmDiff

namespace TauCeti.MeasureTheory

variable {Ω F : Type*} [FunLike F (Set Ω) ℝ≥0∞] [OuterMeasureClass F Ω] {μ : F}

/-- For a finite outer measure, the difference of two set masses is bounded by the mass of their
symmetric difference. No measurability or additivity is needed. -/
theorem abs_toReal_sub_le_toReal_symmDiff (hμ : μ univ ≠ ∞) {s t : Set Ω} :
    |(μ s).toReal - (μ t).toReal| ≤ (μ (s ∆ t)).toReal := by
  have hfin (a : Set Ω) : μ a ≠ ∞ := ne_top_of_le_ne_top hμ (measure_mono (subset_univ a))
  have hle (a b : Set Ω) : (μ a).toReal ≤ (μ (a ∆ b)).toReal + (μ b).toReal := by
    calc
      (μ a).toReal ≤ (μ ((a ∆ b) ∪ b)).toReal :=
        ENNReal.toReal_mono (hfin _) (measure_mono (le_symmDiff_sup_right a b))
      _ ≤ (μ (a ∆ b) + μ b).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩) (measure_union_le _ _)
      _ = _ := ENNReal.toReal_add (hfin _) (hfin _)
  have hst := hle s t
  have hts := hle t s
  rw [symmDiff_comm t s] at hts
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Under a finite outer measure, the mass of `A ∩ B` is within the sum of the
symmetric-difference masses of `A` and `B` against `s` of the mass of `s`. -/
theorem abs_toReal_inter_sub_le_toReal_symmDiff_add (hμ : μ univ ≠ ∞) {A B s : Set Ω} :
    |(μ (A ∩ B)).toReal - (μ s).toReal| ≤ (μ (A ∆ s)).toReal + (μ (B ∆ s)).toReal := by
  have hfin (a : Set Ω) : μ a ≠ ∞ := ne_top_of_le_ne_top hμ (measure_mono (subset_univ a))
  calc
    |(μ (A ∩ B)).toReal - (μ s).toReal| ≤ (μ ((A ∩ B) ∆ s)).toReal :=
      abs_toReal_sub_le_toReal_symmDiff hμ
    _ ≤ (μ ((A ∆ s) ∪ (B ∆ s))).toReal :=
      ENNReal.toReal_mono (hfin _) (measure_mono Set.inter_symmDiff_subset)
    _ ≤ (μ (A ∆ s) + μ (B ∆ s)).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩) (measure_union_le _ _)
    _ = _ := ENNReal.toReal_add (hfin _) (hfin _)

end TauCeti.MeasureTheory
