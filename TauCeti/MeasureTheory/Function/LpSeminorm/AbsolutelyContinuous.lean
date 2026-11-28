/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The essential supremum along absolutely continuous measures

Let `ν ≪ μ`. A function essentially bounded for `μ` is essentially bounded for `ν`, with no larger
essential supremum (`MeasureTheory.eLpNorm_top_mono_ac`, `MeasureTheory.MemLp.mono_ac_top`). At the
exponent `∞`, an `Lᵖ` seminorm only sees a measure through its null sets.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ ν : Measure α}

/-- The essential supremum norm does not increase when passing to an absolutely continuous
measure. -/
theorem eLpNorm_top_mono_ac (f : α → E) (h : ν ≪ μ) : eLpNorm f ∞ ν ≤ eLpNorm f ∞ μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [eLpNorm_exponent_top hf, eLpNorm_exponent_top (hf.mono_ac h)]
    exact eLpNormEssSup_mono_measure f h
  · simp [eLpNorm_of_not_aestronglyMeasurable hf]

/-- An essentially bounded function for `μ` is essentially bounded for every `ν ≪ μ`. -/
theorem MemLp.mono_ac_top {f : α → E} (hf : MemLp f ∞ μ) (h : ν ≪ μ) : MemLp f ∞ ν :=
  memLp_iff.2 <| (eLpNorm_top_mono_ac f h).trans_lt (memLp_iff.1 hf)

end MeasureTheory
