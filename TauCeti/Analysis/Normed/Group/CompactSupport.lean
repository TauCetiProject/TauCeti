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
-/

public section

open Metric

/-- A compactly supported map has topological support inside some open ball of positive radius
around the origin. -/
theorem HasCompactSupport.exists_pos_le_norm_notMem_tsupport {X Y : Type*}
    [SeminormedAddGroup X] [Zero Y] {g : X → Y} (hg : HasCompactSupport g) :
    ∃ R > 0, ∀ x, R ≤ ‖x‖ → x ∉ tsupport g := by
  obtain ⟨R, hR⟩ := hg.isCompact.isBounded.subset_ball 0
  refine ⟨max R 1, by positivity, fun x hx h ↦ ?_⟩
  have := mem_ball_zero_iff.1 (hR h)
  linarith [le_max_left R 1]

/-- A function of `Ψ y` that vanishes outside `T` is compactly supported when the preimage under
`Ψ` of `T` lies in a compact set. -/
theorem HasCompactSupport.comp_of_forall_mem_imp_mem {X Y Z : Type*} [TopologicalSpace X]
    [R1Space X] [Zero Z] {Ψ : X → Y} {T : Set Y} {K : Set X} (hK : IsCompact K)
    (hΨK : ∀ y, Ψ y ∈ T → y ∈ K) {k : Y → Z}
    (hkz : ∀ z ∉ T, k z = 0) : HasCompactSupport fun y ↦ k (Ψ y) :=
  HasCompactSupport.intro hK fun y hy ↦ hkz _ fun h ↦ hy (hΨK y h)
