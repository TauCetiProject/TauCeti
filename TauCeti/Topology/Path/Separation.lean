/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Path

/-!
# Separation by a path

A path separates two points inside a set when both points remain after the path's range is removed
and lie in different connected components of the resulting cut set. This is the topological
relation used to compare successive crosscuts in a prime-end chain.

The definition includes membership in the cut set, so it is false for a point on the path or
outside the ambient set. It depends only on the path's range: reversing the path changes nothing,
and an ambient homeomorphism preserves the relation.

## Main declarations

* `Path.SeparatesIn` -- a path separates two points inside a set.
* `Path.separatesIn_symm` -- reversing the path does not change separation.
* `Path.separatesIn_map_homeomorph` -- separation is invariant under ambient homeomorphisms.
-/

public section

open Set

namespace Path

universe u v

variable {X : Type u} [TopologicalSpace X] {x y : X}
  (γ : Path x y) (U : Set X) (z w : X)

/-- A path separates two points in `U` when both points lie in `U \ range γ` and belong to
different connected components of that cut set. -/
def SeparatesIn : Prop :=
  z ∈ U \ range γ ∧ w ∈ U \ range γ ∧
    connectedComponentIn (U \ range γ) z ≠ connectedComponentIn (U \ range γ) w

/-- The defining characterization of separation by a path. -/
theorem separatesIn_def :
    γ.SeparatesIn U z w ↔
      z ∈ U \ range γ ∧ w ∈ U \ range γ ∧
        connectedComponentIn (U \ range γ) z ≠ connectedComponentIn (U \ range γ) w :=
  Iff.rfl

/-- Separation by a path is symmetric in the two points. -/
theorem separatesIn_comm : γ.SeparatesIn U z w ↔ γ.SeparatesIn U w z := by
  rw [separatesIn_def, separatesIn_def]
  tauto

/-- A path does not separate a point from itself. -/
@[simp]
theorem not_separatesIn_self : ¬ γ.SeparatesIn U z z := by
  simp [SeparatesIn]

/-- Reversing a path does not change which points it separates. -/
@[simp]
theorem separatesIn_symm : γ.symm.SeparatesIn U z w ↔ γ.SeparatesIn U z w := by
  simp only [SeparatesIn, Path.symm_range]

/-- An ambient homeomorphism preserves separation by a path. -/
theorem separatesIn_map_homeomorph {Y : Type v} [TopologicalSpace Y] (e : X ≃ₜ Y) :
    (γ.map e.continuous).SeparatesIn (e '' U) (e z) (e w) ↔ γ.SeparatesIn U z w := by
  have hrange : range (γ.map e.continuous) = e '' range γ := by
    ext q
    simp [Path.map_coe]
  have hcut : e '' U \ range (γ.map e.continuous) = e '' (U \ range γ) := by
    rw [hrange, ← image_sdiff e.injective]
  rw [SeparatesIn, hcut, SeparatesIn]
  constructor
  · rintro ⟨hz, hw, hne⟩
    rcases hz with ⟨z', hz', hz'eq⟩
    rcases hw with ⟨w', hw', hw'eq⟩
    have hzz' : z' = z := e.injective hz'eq
    have hww' : w' = w := e.injective hw'eq
    subst z'
    subst w'
    refine ⟨hz', hw', fun heq => hne ?_⟩
    have himage := congrArg (e '' ·) heq
    simpa only [e.image_connectedComponentIn hz', e.image_connectedComponentIn hw'] using himage
  · rintro ⟨hz, hw, hne⟩
    refine ⟨mem_image_of_mem e hz, mem_image_of_mem e hw, ?_⟩
    intro heq
    have himage : e '' connectedComponentIn (U \ range γ) z =
        e '' connectedComponentIn (U \ range γ) w := by
      simpa only [e.image_connectedComponentIn hz, e.image_connectedComponentIn hw] using heq
    exact hne ((image_eq_image e.injective).mp himage)

end Path

end
