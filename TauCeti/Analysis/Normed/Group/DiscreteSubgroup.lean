/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Shortest vectors of discrete subgroups

A discrete additive subgroup `L` of a proper normed additive group, viewed as a `ℤ`-submodule,
meets every closed ball in a finite set, since it is closed. If `L` is nonzero, a shortest nonzero
vector therefore exists (`Submodule.exists_norm_le_of_ne_bot`): a nonzero vector of minimal norm
among the finitely many nonzero vectors of `L` in the ball through any nonzero vector. For a lattice
this is a vector realizing its first minimum.
-/

public section

open Metric

/-- A nonzero discrete additive subgroup of a proper normed additive group has a shortest nonzero
vector. -/
theorem Submodule.exists_norm_le_of_ne_bot {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] (hL : L ≠ ⊥) :
    ∃ l₀ ∈ L, l₀ ≠ 0 ∧ ∀ l ∈ L, l ≠ 0 → ‖l₀‖ ≤ ‖l‖ := by
  obtain ⟨l₁, hl₁, hl₁0⟩ := L.ne_bot_iff.mp hL
  have hfin : (closedBall (0 : E) ‖l₁‖ ∩ ((L : Set E) \ {0})).Finite :=
    (finite_isBounded_inter_isClosed (s := (L : Set E)) (isDiscrete_iff_discreteTopology.mpr ‹_›)
      isBounded_closedBall (AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup))).subset
      (Set.inter_subset_inter_right _ Set.sdiff_subset)
  obtain ⟨l₀, ⟨-, hl₀, hl₀0⟩, hmin⟩ := Set.exists_min_image _ (‖·‖) hfin ⟨l₁, by simp, hl₁, hl₁0⟩
  refine ⟨l₀, hl₀, hl₀0, fun l hl hl0 ↦ ?_⟩
  by_cases hl' : ‖l‖ ≤ ‖l₁‖
  · exact hmin l ⟨by simpa using hl', hl, hl0⟩
  · exact (hmin l₁ ⟨by simp, hl₁, hl₁0⟩).trans (le_of_not_ge hl')
