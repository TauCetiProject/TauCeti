/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# Homotopy groups of iterated loop spaces

The `k`-fold iterated loop space `Ω^[k] X` of a pointed space, built from Mathlib's loop space
`Ω X x = Path x x`, and the shift of homotopy groups along it,
`π_(m + 1)(Ω^[k] X) ≃* π_(m + 1 + k)(X)`, by iterating
`HomotopyGroup.pathLoopSpaceMulEquiv`.

## Main declarations

* `TauCeti.PtTop`: a topological space with a base point.
* `TauCeti.PtTop.loopSpace`, `TauCeti.PtTop.iterLoop`: the loop space and the `k`-fold iterated
  loop space of a pointed space.
* `TauCeti.PtTop.piIterLoopMulEquiv`: `π_(m + 1)(Ω^[k] X) ≃* π_(m + 1 + k)(X)`.
-/

public section

universe u

namespace TauCeti

open HomotopyGroup
open scoped Topology

/-- A topological space with a base point. -/
structure PtTop where
  /-- The underlying type. -/
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  /-- The base point. -/
  pt : carrier

attribute [instance] PtTop.topologicalSpace

namespace PtTop

/-- The space of loops at the base point, based at the constant loop. -/
def loopSpace (P : PtTop.{u}) : PtTop.{u} where
  carrier := Path P.pt P.pt
  pt := Path.refl P.pt

/-- The `k`-fold iterated loop space, `Ω^[k] P = Ω (Ω^[k - 1] P)`. -/
def iterLoop (P : PtTop.{u}) : ℕ → PtTop.{u}
  | 0 => P
  | k + 1 => (P.iterLoop k).loopSpace

@[simp]
theorem iterLoop_zero (P : PtTop.{u}) : P.iterLoop 0 = P := by
  rw [iterLoop.eq_1]

@[simp]
theorem iterLoop_succ (P : PtTop.{u}) (k : ℕ) :
    P.iterLoop (k + 1) = (P.iterLoop k).loopSpace := by
  rw [iterLoop.eq_2]

/-- **The homotopy groups of the `k`-fold loop space are the homotopy groups of the space,
shifted by `k`**: `π_(m + 1)(Ω^[k] X) ≃* π_(m + 1 + k)(X)`. -/
noncomputable def piIterLoopMulEquiv (P : PtTop.{u}) :
    (k m : ℕ) →
      π_ (m + 1) (P.iterLoop k).carrier (P.iterLoop k).pt ≃* π_ (m + 1 + k) P.carrier P.pt
  | 0, _ => MulEquiv.refl _
  | k + 1, m =>
    (pathLoopSpaceMulEquiv (X := (P.iterLoop k).carrier) (x := (P.iterLoop k).pt) m).trans
      ((P.piIterLoopMulEquiv k (m + 1)).trans
        (congrMulEquiv (finCongr (by omega))))

end PtTop

end TauCeti
