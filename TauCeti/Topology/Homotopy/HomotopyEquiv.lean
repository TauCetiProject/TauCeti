/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Path

/-!
# Path connectedness is a homotopy invariant

A homotopy equivalence `e : X ≃ₕ Y` is not surjective, so path connectedness of `Y` cannot be
read off from the image of a path in `X`. What replaces surjectivity is the trace of the
homotopy `e.toFun ∘ e.invFun ≃ id`: evaluated at a point `y`, it is a path from
`e.toFun (e.invFun y)` to `y`. Two points of `Y` are therefore joined to points in the image of
`e.toFun`, which are joined to each other because `X` is path connected.

This is the prerequisite for the base-point-free homotopy-group statements in
`TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv`, which need the target space to be path
connected before base-point change is available there.

## Main declarations

* `ContinuousMap.HomotopyEquiv.pathConnectedSpace`: a space homotopy equivalent to a path
  connected space is path connected.
-/

public section

namespace TauCeti

open scoped ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Path connectedness is a homotopy invariant.** A space homotopy equivalent to a path
connected space is path connected. -/
theorem _root_.ContinuousMap.HomotopyEquiv.pathConnectedSpace [PathConnectedSpace X]
    (e : X ≃ₕ Y) : PathConnectedSpace Y where
  nonempty := (PathConnectedSpace.nonempty (X := X)).map e.toFun
  joined y₀ y₁ :=
    -- Evaluating the homotopy `e.toFun ∘ e.invFun ≃ id` at `y` is a path from
    -- `e.toFun (e.invFun y)` to `y`.
    have trace : ∀ y : Y, Joined (e.toFun (e.invFun y)) y := fun y => ⟨e.right_inv.some.evalAt y⟩
    ((trace y₀).symm.trans
        (Joined.map ⟨PathConnectedSpace.somePath (e.invFun y₀) (e.invFun y₁)⟩
          e.toFun.continuous)).trans
      (trace y₁)

end TauCeti
