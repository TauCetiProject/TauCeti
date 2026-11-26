/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compactly supported maps on normed groups vanish near infinity

The topological support of a compactly supported map on a seminormed group lies inside some ball
around the origin (`HasCompactSupport.exists_pos_le_norm_notMem_tsupport`). This strengthens
Mathlib's `HasCompactSupport.exists_pos_le_norm`, which only gives vanishing of the map itself,
so that it also applies to derivatives of the map.

On a proper normed group, a compactly supported function on `ℝ` composed with `x ↦ ‖x‖` or with
`x ↦ ‖x‖²` is compactly supported (`HasCompactSupport.comp_norm`, `HasCompactSupport.comp_norm_sq`).
A function on `ℝ` supported in `(r, R)` composed with `x ↦ ‖x‖` is supported in the open shell
`ball 0 R \ closedBall 0 r` (`tsupport_comp_norm_subset`).
-/

public section

open Metric Filter Set

/-- A compactly supported map has topological support inside some open ball of positive radius
around the origin. -/
theorem HasCompactSupport.exists_pos_le_norm_notMem_tsupport {X Y : Type*}
    [SeminormedAddGroup X] [Zero Y] {g : X → Y} (hg : HasCompactSupport g) :
    ∃ R > 0, ∀ x, R ≤ ‖x‖ → x ∉ tsupport g := by
  obtain ⟨R, hR⟩ := hg.isCompact.isBounded.subset_ball 0
  refine ⟨max R 1, by positivity, fun x hx h ↦ ?_⟩
  have := mem_ball_zero_iff.1 (hR h)
  linarith [le_max_left R 1]

/-- A function `ψ` on `ℝ` supported in `(r, R)` gives a radial function `x ↦ ψ ‖x‖` supported in
the open shell `ball 0 R \ closedBall 0 r`. -/
theorem tsupport_comp_norm_subset {E M : Type*} [SeminormedAddGroup E] [Zero M] {r R : ℝ}
    {ψ : ℝ → M} (hψs : tsupport ψ ⊆ Ioo r R) :
    tsupport (fun x : E ↦ ψ ‖x‖) ⊆ ball (0 : E) R \ closedBall 0 r := fun x hx ↦ by
  simpa [and_comm] using hψs (tsupport_comp_subset_preimage ψ continuous_norm hx)

/-- A function of `‖x‖` built from a compactly supported function on `ℝ` is compactly supported
on a proper normed group. -/
theorem HasCompactSupport.comp_norm {E M : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [Zero M] {f : ℝ → M} (hf : HasCompactSupport f) :
    HasCompactSupport fun x : E ↦ f ‖x‖ := by
  rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at hf ⊢
  exact tendsto_norm_cocompact_atTop.eventually (hf.filter_mono atTop_le_cocompact)

/-- A function of `‖x‖²` built from a compactly supported function on `ℝ` is compactly supported
on a proper normed group. -/
theorem HasCompactSupport.comp_norm_sq {E M : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [Zero M] {f : ℝ → M} (hf : HasCompactSupport f) :
    HasCompactSupport fun x : E ↦ f (‖x‖ ^ 2) := by
  rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at hf ⊢
  exact ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop).eventually
    (hf.filter_mono atTop_le_cocompact)
