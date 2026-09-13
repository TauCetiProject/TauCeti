/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

* `ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv`: `π₁(X, x) ≃* π₁(Y, e x)` for a homotopy
  equivalence `e : X ≃ₕ Y`, with `ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv_apply` and
  `ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv_symm_apply`.
* `ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv_refl`,
  `ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv_trans`: the construction respects
  identities and composition of homotopy equivalences.
* `ContinuousMap.HomotopyEquiv.nonempty_fundamentalGroupMulEquiv`: over a path connected
  space, the fundamental groups at *any* pair of base points are isomorphic.
-/

public section
noncomputable section

namespace TauCeti

open scoped ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **A homotopy equivalence induces an isomorphism of fundamental groups.** -/
def _root_.ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv (e : X ≃ₕ Y) (x : X) :
    _root_.FundamentalGroup X x ≃* _root_.FundamentalGroup Y (e.toFun x) :=
  _root_.HomotopyGroup.pi1MulEquivFundamentalGroup.symm.trans
    ((_root_.HomotopyGroup.mulEquivOfHomotopyEquiv (N := Fin 1) e x).trans
      _root_.HomotopyGroup.pi1MulEquivFundamentalGroup)

/-- Read through `π_ 1`, the isomorphism induced by a homotopy equivalence `e` is the map that
`e.toFun` induces on homotopy groups. -/
@[simp]
theorem _root_.ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv_apply (e : X ≃ₕ Y) (x : X)
    (a : _root_.FundamentalGroup X x) :
    e.fundamentalGroupMulEquiv x a =
      _root_.HomotopyGroup.pi1MulEquivFundamentalGroup
        (_root_.HomotopyGroup.map e.toFun rfl
          (_root_.HomotopyGroup.pi1MulEquivFundamentalGroup.symm a)) := by
  rw [ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv, MulEquiv.trans_apply,
    MulEquiv.trans_apply, _root_.HomotopyGroup.mulEquivOfHomotopyEquiv_apply]

/-- Read through `π_ 1`, the inverse of the isomorphism induced by a homotopy equivalence `e` is
the map that `e.invFun` induces on homotopy groups, followed by base-point change along the trace
of the round trip `e.invFun ∘ e.toFun ≃ id`. -/
@[simp]
theorem _root_.ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv_symm_apply (e : X ≃ₕ Y)
    (x : X) (b : _root_.FundamentalGroup Y (e.toFun x)) :
    (e.fundamentalGroupMulEquiv x).symm b =
      _root_.HomotopyGroup.pi1MulEquivFundamentalGroup
        (homotopyGroupTransport
          ((e.left_inv.some.evalAt x).cast (ContinuousMap.comp_apply e.invFun e.toFun x).symm
            (ContinuousMap.id_apply x).symm)
          (_root_.HomotopyGroup.map e.invFun rfl
            (_root_.HomotopyGroup.pi1MulEquivFundamentalGroup.symm b))) := by
  rw [ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv, MulEquiv.symm_trans_apply,
    MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    _root_.HomotopyGroup.mulEquivOfHomotopyEquiv_symm_apply]

/-- The identity homotopy equivalence induces the identity isomorphism of fundamental groups. -/
@[simp]
theorem _root_.ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv_refl (x : X) :
    (ContinuousMap.HomotopyEquiv.refl X).fundamentalGroupMulEquiv x = MulEquiv.refl _ :=
  MulEquiv.ext fun a => by
    rw [ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv, MulEquiv.trans_apply,
      MulEquiv.trans_apply, _root_.HomotopyGroup.mulEquivOfHomotopyEquiv_refl]
    exact MulEquiv.apply_symm_apply _ a

/-- The isomorphism of fundamental groups induced by a composite of homotopy equivalences is the
composite of the induced isomorphisms. -/
@[simp]
theorem _root_.ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv_trans {Z : Type*}
    [TopologicalSpace Z] (e : X ≃ₕ Y) (e' : Y ≃ₕ Z) (x : X) :
    (e.trans e').fundamentalGroupMulEquiv x =
      (e.fundamentalGroupMulEquiv x).trans (e'.fundamentalGroupMulEquiv (e.toFun x)) :=
  MulEquiv.ext fun a => by
    -- The two sides live over the base points `(e.trans e').toFun x` and `e'.toFun (e.toFun x)`,
    -- which agree only after unfolding `HomotopyEquiv.trans`, so `rw` cannot rewrite the goal;
    -- chain the application lemmas instead.
    have h := congrArg _root_.HomotopyGroup.pi1MulEquivFundamentalGroup
      ((_root_.HomotopyGroup.map_comp_apply (N := Fin 1) e'.toFun rfl e.toFun rfl
        (_root_.HomotopyGroup.pi1MulEquivFundamentalGroup.symm a)).symm.trans
        (congrArg (_root_.HomotopyGroup.map e'.toFun rfl)
          (MulEquiv.symm_apply_apply _root_.HomotopyGroup.pi1MulEquivFundamentalGroup _).symm))
    exact ((e.trans e').fundamentalGroupMulEquiv_apply x a).trans (h.trans
      ((congrArg (fun b : _root_.FundamentalGroup Y (e.toFun x) =>
          _root_.HomotopyGroup.pi1MulEquivFundamentalGroup (_root_.HomotopyGroup.map e'.toFun rfl
            (_root_.HomotopyGroup.pi1MulEquivFundamentalGroup.symm b)))
        (e.fundamentalGroupMulEquiv_apply x a).symm).trans
        (e'.fundamentalGroupMulEquiv_apply (e.toFun x) _).symm))

/-- Over a path connected space, homotopy equivalence identifies the fundamental groups at *any*
pair of base points, by composing with base-point change. -/
theorem _root_.ContinuousMap.HomotopyEquiv.nonempty_fundamentalGroupMulEquiv
    [PathConnectedSpace X] (e : X ≃ₕ Y) (x : X) (y : Y) :
    Nonempty (_root_.FundamentalGroup X x ≃* _root_.FundamentalGroup Y y) := by
  have : PathConnectedSpace Y := e.pathConnectedSpace
  exact ⟨(e.fundamentalGroupMulEquiv x).trans
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (e.toFun x) y)⟩

end TauCeti
