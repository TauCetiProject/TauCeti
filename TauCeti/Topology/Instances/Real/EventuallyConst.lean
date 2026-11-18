/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.Compact

/-!
# Continuous functions on `ℝ` that are constant near both ends

A continuous function on `ℝ` that is constant on `(-∞, -R]` and on `[R, ∞)` is bounded: on
`[-R, R]` by compactness, and beyond by its two constant values. Such functions are the slopes of
exponential weights `e^{κ(s)}` on a cylinder `ℝ × S¹` whose slopes at the two ends are fixed.

## Main results

* `Continuous.exists_forall_norm_le_of_eq_of_eq`: such a function is bounded in norm.
-/

public section

open Set

/-- A continuous function on `ℝ` that is constant on `(-∞, -R]` and on `[R, ∞)` is bounded. -/
theorem Continuous.exists_forall_norm_le_of_eq_of_eq {E : Type*} [SeminormedAddCommGroup E]
    {f : ℝ → E} (hf : Continuous f) {R : ℝ} {a b : E} (ha : ∀ s ≤ -R, f s = a)
    (hb : ∀ s, R ≤ s → f s = b) : ∃ C, ∀ s, ‖f s‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C (max ‖a‖ ‖b‖), fun s ↦ ?_⟩
  rcases le_or_gt s (-R) with hs | hs
  · rw [ha s hs]
    exact (le_max_left _ _).trans (le_max_right _ _)
  rcases le_or_gt R s with hs' | hs'
  · rw [hb s hs']
    exact (le_max_right _ _).trans (le_max_right _ _)
  exact (hC s ⟨hs.le, hs'.le⟩).trans (le_max_left _ _)
