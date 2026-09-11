/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv

/-!
# Asphericity and the `K(G, 1)` property are homotopy invariants

Both properties are stated at a base point, but neither depends on it
(`TauCeti.IsAspherical.of_basepoint`, `TauCeti.IsEilenbergMacLaneSpaceOne.of_basepoint`): an
aspherical space is path connected, so base-point change identifies its homotopy groups at any two
points. With that, homotopy invariance follows from the invariance of the homotopy groups
themselves, since a homotopy equivalence carries no base point with it.

This is the homotopy-invariant form of the stability statements in
`TauCeti.AlgebraicTopology.EilenbergMacLane.Basic`, which record stability under a *pointed
homeomorphism*. Those remain the tool for a homeomorphism: they depend only on the homotopy
groups of homeomorphic spaces, not on base-point change, and they place the conclusion at the
prescribed image base point.

## Main declarations

* `TauCeti.IsAspherical.of_homotopyEquiv`: **asphericity is a homotopy invariant.**
* `TauCeti.IsEilenbergMacLaneSpaceOne.of_homotopyEquiv`: **being a `K(G, 1)` space is a homotopy
  invariant.**

## References

Compare Section 1.B of [hatcher02].
-/

public section

namespace TauCeti

open scoped Topology Topology.Homotopy ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

namespace IsAspherical

/-- **Asphericity is a homotopy invariant.** A space homotopy equivalent to an aspherical space
is aspherical, at every base point. -/
theorem of_homotopyEquiv (h : IsAspherical X x) (e : X ≃ₕ Y) (y : Y) : IsAspherical Y y := by
  let : PathConnectedSpace X := h.pathConnectedSpace
  refine IsAspherical.mk e.pathConnectedSpace fun n => ?_
  let : Subsingleton (π_ (n + 2) X x) := h.subsingleton_homotopyGroup n
  obtain ⟨φ⟩ := nonempty_homotopyGroupMulEquiv_of_homotopyEquiv (N := Fin (n + 2)) e x y
  exact φ.toEquiv.subsingleton_congr.mp inferInstance

end IsAspherical

namespace IsEilenbergMacLaneSpaceOne

variable {G : Type*} [Group G]

/-- **Being an Eilenberg--Mac Lane space of type `K(G, 1)` is a homotopy invariant.** -/
theorem of_homotopyEquiv (h : IsEilenbergMacLaneSpaceOne G X x) (e : X ≃ₕ Y) (y : Y) :
    IsEilenbergMacLaneSpaceOne G Y y := by
  let : PathConnectedSpace X := h.isAspherical.pathConnectedSpace
  obtain ⟨φ⟩ := FundamentalGroup.nonempty_homotopyEquivMulEquiv e x y
  exact IsEilenbergMacLaneSpaceOne.mk (h.isAspherical.of_homotopyEquiv e y)
    (h.nonempty_fundamentalGroupMulEquiv.map fun f => φ.symm.trans f)

end IsEilenbergMacLaneSpaceOne

end TauCeti
