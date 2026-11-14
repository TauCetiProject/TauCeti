/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Upper boundedness of `Real.log ‖f ·‖` on compact sets

Although `Real.log` is discontinuous at `0`, Lean's convention `Real.log 0 = 0` ensures
`Real.log x ≤ Real.posLog x` for every `x : ℝ`, while `Real.posLog` is continuous on all of `ℝ`.
Consequently, whenever `f` is continuous on a compact set `s`, `(fun x ↦ Real.log ‖f x‖) '' s` is
bounded above even if `f` vanishes on `s`.
-/

public section

/-- If `f` is continuous on a compact set `s`, the image `(fun x ↦ Real.log ‖f x‖) '' s` is bounded
above, including across zeros of `f` on `s` (where `Real.log 0 = 0 ≤ Real.posLog 0`). -/
theorem IsCompact.bddAbove_image_log_norm {X E : Type*} [TopologicalSpace X]
    [SeminormedAddCommGroup E] {s : Set X} {f : X → E} (hs : IsCompact s)
    (hf : ContinuousOn f s) : BddAbove ((fun x ↦ Real.log ‖f x‖) '' s) := by
  obtain ⟨B, hB⟩ :=
    (hs.image_of_continuousOn (Real.continuous_posLog.comp_continuousOn hf.norm)).bddAbove
  exact ⟨B, fun _ ⟨x, hx, hxv⟩ ↦ hxv ▸ (le_max_right 0 _).trans (hB ⟨x, hx, rfl⟩)⟩

example : BddAbove ((fun x : ℝ ↦ Real.log ‖x‖) '' Set.Icc (-1) 1) :=
  isCompact_Icc.bddAbove_image_log_norm continuousOn_id
