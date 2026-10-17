/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Small sublevels near a unique minimum

If a real function has a unique global minimum and one compact sublevel strictly above it,
then sufficiently small sublevels lie in any prescribed open neighbourhood of the minimum.
This allows local descriptions near the minimum to describe whole sublevels. Continuity is
needed only on the one compact sublevel, not on the entire space.
-/

public section

open Set

namespace TauCeti

/-- Small sublevels of a function with a unique global minimum lie in any open neighbourhood
of that minimum, provided one sublevel strictly above the minimum is compact. -/
theorem exists_pos_sublevel_subset_of_unique_min {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {x : X} {a : ℝ}
    (hcompact : IsCompact {y | f y ≤ a}) (hf : ContinuousOn f {y | f y ≤ a})
    (ha : f x < a) (hmin : ∀ y, f y ≤ f x → y = x)
    {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ ε > 0, {y | f y ≤ f x + ε} ⊆ U := by
  by_cases hne : ({y | f y ≤ a} \ U).Nonempty
  · obtain ⟨z, hz, hzm⟩ := (hcompact.diff hU).exists_isMinOn hne
      (hf.mono sdiff_subset)
    have hxz : f x < f z := by
      by_contra! hle
      exact hz.2 (hmin z hle ▸ hx)
    let ε := min (a - f x) (f z - f x) / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    refine ⟨ε, hε, fun y hy ↦ ?_⟩
    have hεa : ε ≤ (a - f x) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hεz : ε ≤ (f z - f x) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    by_contra hyU
    have hyK : y ∈ {y | f y ≤ a} \ U := ⟨by dsimp at hy ⊢; linarith, hyU⟩
    have hzy : f z ≤ f y := hzm hyK
    dsimp at hy
    linarith
  · refine ⟨(a - f x) / 2, by positivity, fun y hy ↦ ?_⟩
    by_contra hyU
    exact hne ⟨y, ⟨by dsimp at hy ⊢; linarith, hyU⟩⟩

end TauCeti
