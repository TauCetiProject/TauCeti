/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform

/-! # Mellin transforms of finite sums -/

public section

open MeasureTheory

/-- The Mellin transform of a finite sum is the sum of the individual transforms, with
absolute convergence. -/
theorem HasMellin.finsetSum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : Finset ι} {f : ι → ℝ → E} {s : ℂ} {m : ι → E}
    (h : ∀ i ∈ t, HasMellin (f i) s (m i)) :
    HasMellin (fun x ↦ ∑ i ∈ t, f i x) s (∑ i ∈ t, m i) := by
  have hi i (hit : i ∈ t) := (h i hit).1
  refine ⟨?_, ?_⟩
  · simpa only [MellinConvergent, IntegrableOn, Finset.smul_sum] using integrable_finsetSum t hi
  · simp only [mellin, Finset.smul_sum, integral_finsetSum t hi]
    exact Finset.sum_congr rfl fun i hit ↦ (h i hit).2
