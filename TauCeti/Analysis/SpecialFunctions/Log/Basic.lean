/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Upper boundedness of `Real.log` on bounded and compact sets

Although `Real.log` is discontinuous at `0`, Lean's conventions `Real.log 0 = 0` and
`Real.log (-x) = Real.log x` (`Real.log_abs`), combined with `Real.log_le_self`, ensure
`Real.log y ≤ |y|` for every `y : ℝ`. Consequently, `Real.log '' s` is bounded above for every
bounded subset `s : Set ℝ`, and `(fun x ↦ Real.log (f x)) '' s` is bounded above whenever `f` is a
continuous real-valued function on a compact set `s` (even if `f` vanishes or changes sign on `s`).
-/

public section

/-- For any bounded subset `s : Set ℝ`, the image `Real.log '' s` is bounded above (using
`Real.log y = Real.log |y| ≤ |y|` across nonpositive values). -/
theorem Bornology.IsBounded.bddAbove_image_log {s : Set ℝ} (hs : Bornology.IsBounded s) :
    BddAbove (Real.log '' s) := by
  obtain ⟨C, hC⟩ := hs.exists_norm_le
  refine ⟨C, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [← Real.log_abs]
  exact (Real.log_le_self (abs_nonneg y)).trans (Real.norm_eq_abs y ▸ hC y hy)

/-- If `f : X → ℝ` is continuous on a compact set `s`, the image `(fun x ↦ Real.log (f x)) '' s` is
bounded above, including across zeros and negative values of `f` on `s`. -/
theorem IsCompact.bddAbove_image_log {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ}
    (hs : IsCompact s) (hf : ContinuousOn f s) :
    BddAbove ((fun x ↦ Real.log (f x)) '' s) :=
  Set.image_image Real.log f s ▸ (hs.image_of_continuousOn hf).isBounded.bddAbove_image_log

example : BddAbove ((fun x : ℝ ↦ Real.log x) '' Set.Icc (-1) 1) :=
  isCompact_Icc.bddAbove_image_log continuousOn_id
