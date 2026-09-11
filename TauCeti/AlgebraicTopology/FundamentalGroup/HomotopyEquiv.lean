/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv

/-!
# The fundamental group is a homotopy invariant

A homotopy equivalence induces an isomorphism of fundamental groups. This is read off from the
corresponding statement for higher homotopy groups in dimension one, through Mathlib's
`HomotopyGroup.pi1MulEquivFundamentalGroup`, rather than reproved: the free-homotopy trace
argument is dimension independent, and `π_ 1` is the fundamental group.

This strengthens `TauCeti.FundamentalGroup.homeomorphMulEquiv`, which covers the case of a
homeomorphism, but the two are independent as API: the homeomorphism version has an explicit
inverse and needs no finiteness or decidability instances, so it stays the tool of choice when a
homeomorphism is what is available.

## Main declarations

* `TauCeti.FundamentalGroup.homotopyEquivMulEquiv`: `π₁(X, x) ≃* π₁(Y, e x)` for a homotopy
  equivalence `e : X ≃ₕ Y`.
* `TauCeti.FundamentalGroup.nonempty_homotopyEquivMulEquiv`: over a path connected space, the
  fundamental groups at *any* pair of base points are isomorphic.
-/

public section
noncomputable section

namespace TauCeti

namespace FundamentalGroup

open scoped ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **A homotopy equivalence induces an isomorphism of fundamental groups.** -/
@[expose] def homotopyEquivMulEquiv (e : X ≃ₕ Y) (x : X) :
    _root_.FundamentalGroup X x ≃* _root_.FundamentalGroup Y (e.toFun x) :=
  _root_.HomotopyGroup.pi1MulEquivFundamentalGroup.symm.trans
    ((homotopyGroupMulEquivOfHomotopyEquiv (N := Fin 1) e x).trans
      _root_.HomotopyGroup.pi1MulEquivFundamentalGroup)

/-- Over a path connected space, homotopy equivalence identifies the fundamental groups at *any*
pair of base points, by composing with base-point change. -/
theorem nonempty_homotopyEquivMulEquiv [PathConnectedSpace X] (e : X ≃ₕ Y) (x : X) (y : Y) :
    Nonempty (_root_.FundamentalGroup X x ≃* _root_.FundamentalGroup Y y) := by
  have : PathConnectedSpace Y := e.pathConnectedSpace
  exact ⟨(homotopyEquivMulEquiv e x).trans
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (e.toFun x) y)⟩

end FundamentalGroup

end TauCeti
