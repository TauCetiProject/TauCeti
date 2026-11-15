/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.Topology.Homotopy.Basic

/-!
# Equivariant contractions

A homotopy `H` through equivariant maps is one with `H (s, g • y) = g • H (s, y)` for every time
`s`. If such a homotopy contracts a space onto a point, that point is fixed by the action
(`ContinuousMap.Homotopy.mem_fixedPoints_of_map_smul`).
-/

public section

open MulAction

namespace ContinuousMap.Homotopy

variable {G X : Type*} [Monoid G] [MulAction G X] [TopologicalSpace X]

/-- A point onto which `X` contracts through `G`-equivariant maps is fixed by `G`. -/
theorem mem_fixedPoints_of_map_smul {x : X}
    (H : Homotopy (ContinuousMap.id X) (ContinuousMap.const X x))
    (hH : ∀ (s : unitInterval) (g : G) (y : X), H (s, g • y) = g • H (s, y)) :
    x ∈ fixedPoints G X :=
  fun g ↦ by simpa using (hH 1 g x).symm

end ContinuousMap.Homotopy
