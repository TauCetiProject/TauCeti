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

* `FundamentalGroup.homotopyEquivMulEquiv`: `π₁(X, x) ≃* π₁(Y, e x)` for a homotopy
  equivalence `e : X ≃ₕ Y`, with `FundamentalGroup.homotopyEquivMulEquiv_apply` and
  `FundamentalGroup.homotopyEquivMulEquiv_symm_apply`.
* `FundamentalGroup.homotopyEquivMulEquiv_refl`, `FundamentalGroup.homotopyEquivMulEquiv_trans`:
  the construction respects identities and composition of homotopy equivalences.
* `FundamentalGroup.nonempty_fundamentalGroupMulEquiv_of_homotopyEquiv`: over a path connected
  space, the fundamental groups at *any* pair of base points are isomorphic.
-/

public section
noncomputable section

namespace FundamentalGroup

open scoped ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **A homotopy equivalence induces an isomorphism of fundamental groups.** -/
def homotopyEquivMulEquiv (e : X ≃ₕ Y) (x : X) :
    _root_.FundamentalGroup X x ≃* _root_.FundamentalGroup Y (e.toFun x) :=
  _root_.HomotopyGroup.pi1MulEquivFundamentalGroup.symm.trans
    ((_root_.HomotopyGroup.mulEquivOfHomotopyEquiv (N := Fin 1) e x).trans
      _root_.HomotopyGroup.pi1MulEquivFundamentalGroup)

/-- Read through `π_ 1`, the isomorphism induced by a homotopy equivalence `e` is the map that
`e.toFun` induces on homotopy groups. -/
@[simp]
theorem homotopyEquivMulEquiv_apply (e : X ≃ₕ Y) (x : X) (a : _root_.FundamentalGroup X x) :
    homotopyEquivMulEquiv e x a =
      _root_.HomotopyGroup.pi1MulEquivFundamentalGroup
        (_root_.HomotopyGroup.map e.toFun rfl
          (_root_.HomotopyGroup.pi1MulEquivFundamentalGroup.symm a)) := by
  rw [homotopyEquivMulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    _root_.HomotopyGroup.mulEquivOfHomotopyEquiv_apply]

/-- Read through `π_ 1`, the inverse of the isomorphism induced by a homotopy equivalence `e` is
the map that `e.invFun` induces on homotopy groups, followed by base-point change along the trace
of the round trip `e.invFun ∘ e.toFun ≃ id`. -/
@[simp]
theorem homotopyEquivMulEquiv_symm_apply (e : X ≃ₕ Y) (x : X)
    (b : _root_.FundamentalGroup Y (e.toFun x)) :
    (homotopyEquivMulEquiv e x).symm b =
      _root_.HomotopyGroup.pi1MulEquivFundamentalGroup
        (TauCeti.homotopyGroupTransport
          ((e.left_inv.some.evalAt x).cast (ContinuousMap.comp_apply e.invFun e.toFun x).symm
            (ContinuousMap.id_apply x).symm)
          (_root_.HomotopyGroup.map e.invFun rfl
            (_root_.HomotopyGroup.pi1MulEquivFundamentalGroup.symm b))) := by
  rw [homotopyEquivMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, _root_.HomotopyGroup.mulEquivOfHomotopyEquiv_symm_apply]

/-- The identity homotopy equivalence induces the identity isomorphism of fundamental groups. -/
@[simp]
theorem homotopyEquivMulEquiv_refl (x : X) :
    homotopyEquivMulEquiv (ContinuousMap.HomotopyEquiv.refl X) x = MulEquiv.refl _ :=
  MulEquiv.ext fun a => by
    rw [homotopyEquivMulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
      _root_.HomotopyGroup.mulEquivOfHomotopyEquiv_refl]
    exact MulEquiv.apply_symm_apply _ a

/-- The isomorphism of fundamental groups induced by a composite of homotopy equivalences is the
composite of the induced isomorphisms. -/
@[simp]
theorem homotopyEquivMulEquiv_trans {Z : Type*} [TopologicalSpace Z] (e : X ≃ₕ Y) (e' : Y ≃ₕ Z)
    (x : X) :
    homotopyEquivMulEquiv (e.trans e') x =
      (homotopyEquivMulEquiv e x).trans (homotopyEquivMulEquiv e' (e.toFun x)) :=
  MulEquiv.ext fun a => by
    -- The two sides live over the base points `(e.trans e').toFun x` and `e'.toFun (e.toFun x)`,
    -- which agree only after unfolding `HomotopyEquiv.trans`, so `rw` cannot rewrite the goal;
    -- chain the application lemmas instead.
    have h := congrArg _root_.HomotopyGroup.pi1MulEquivFundamentalGroup
      ((_root_.HomotopyGroup.map_comp_apply (N := Fin 1) e'.toFun rfl e.toFun rfl
        (_root_.HomotopyGroup.pi1MulEquivFundamentalGroup.symm a)).symm.trans
        (congrArg (_root_.HomotopyGroup.map e'.toFun rfl)
          (MulEquiv.symm_apply_apply _root_.HomotopyGroup.pi1MulEquivFundamentalGroup _).symm))
    exact (homotopyEquivMulEquiv_apply (e.trans e') x a).trans (h.trans
      ((congrArg (fun b : _root_.FundamentalGroup Y (e.toFun x) =>
          _root_.HomotopyGroup.pi1MulEquivFundamentalGroup (_root_.HomotopyGroup.map e'.toFun rfl
            (_root_.HomotopyGroup.pi1MulEquivFundamentalGroup.symm b)))
        (homotopyEquivMulEquiv_apply e x a).symm).trans
        (homotopyEquivMulEquiv_apply e' (e.toFun x) _).symm))

/-- Over a path connected space, homotopy equivalence identifies the fundamental groups at *any*
pair of base points, by composing with base-point change. -/
theorem nonempty_fundamentalGroupMulEquiv_of_homotopyEquiv [PathConnectedSpace X] (e : X ≃ₕ Y)
    (x : X) (y : Y) :
    Nonempty (_root_.FundamentalGroup X x ≃* _root_.FundamentalGroup Y y) := by
  have : PathConnectedSpace Y := e.pathConnectedSpace
  exact ⟨(homotopyEquivMulEquiv e x).trans
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (e.toFun x) y)⟩

end FundamentalGroup
