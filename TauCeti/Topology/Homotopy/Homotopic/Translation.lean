/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Basic

/-!
# Translations by elements joined to the identity are homotopic to the identity

In a topological monoid `G`, a path `γ` from `1` to `g` gives the homotopy `(s, x) ↦ x * γ s`
from the identity of `G` to right multiplication by `g`. In particular, in a path-connected
topological group every right translation is homotopic to the identity, so it acts trivially on
every homotopy-invariant functor such as singular homology. The additive version covers rotations
of a circle `AddCircle p`.

## Main results

* `Joined.homotopic_id_mulRight`, `Joined.homotopic_id_addRight`: right translation by an element
  joined to the identity is homotopic to the identity.
-/

public section

open scoped unitInterval

namespace Joined

variable {G : Type*} [TopologicalSpace G] [MulOneClass G] [ContinuousMul G]

/-- **Right translation by an element joined to `1` is homotopic to the identity**: a path `γ`
from `1` to `g` gives the homotopy `(s, x) ↦ x * γ s`. -/
@[to_additive /-- **Right translation by an element joined to `0` is homotopic to the identity**:
a path `γ` from `0` to `g` gives the homotopy `(s, x) ↦ x + γ s`. -/]
theorem homotopic_id_mulRight {g : G} (h : Joined 1 g) :
    (ContinuousMap.id G).Homotopic (ContinuousMap.mulRight g) := by
  obtain ⟨γ⟩ := h
  exact ⟨{ toFun := fun p : I × G ↦ p.2 * γ p.1
           continuous_toFun := by fun_prop
           map_zero_left := fun x ↦ by simp
           map_one_left := fun x ↦ by simp }⟩

end Joined
