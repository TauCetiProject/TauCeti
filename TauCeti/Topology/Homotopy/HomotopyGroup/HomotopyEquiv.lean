/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyEquiv
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# Homotopy groups are invariant under homotopy equivalence

Postcomposition with a continuous map induces a map on homotopy groups, and maps homotopic
relative to the base point induce the same one. A *free* homotopy `H` from `f` to `g` moves the
base point along its trace `H.evalAt x`, and the two induced maps then differ exactly by
base-point change. This is immediate from the machinery already in place: dragging a generalized
loop `p` through `H` is a homotopy along the trace, in the sense of
`TauCeti.GenLoop.HomotopyAlong`, from `f ∘ p` to `g ∘ p`, and such a homotopy is canonical by
`TauCeti.GenLoop.HomotopyAlong.homotopic_transport`.

Applied to a homotopy equivalence `e : X ≃ₕ Y`, this makes each round trip of `e` bijective on
homotopy groups after correcting the base point. Both round trips are needed: a homotopy inverse
recovers the identity only up to a free homotopy, so one composite alone gives injectivity of the
map induced by `e.toFun` and surjectivity of the map induced by `e.invFun`, and the other
composite is what upgrades the latter to a bijection.

The statements about the induced map alone need no finiteness of the index type beyond
`[Finite N]`; only the transport formula, which mentions the collar construction, asks for the
`[Fintype N]` that the cube radius uses.

## Main declarations

* `TauCeti.GenLoop.homotopyAlongMap`: dragging a generalized loop through a homotopy is a
  homotopy along the trace of that homotopy at the base point.
* `TauCeti.homotopyGroupTransport_map`: **freely homotopic maps induce the same map on homotopy
  groups, up to transport along the trace of the homotopy.**
* `TauCeti.bijective_homotopyGroupMap_of_homotopyEquiv`: a homotopy equivalence induces a
  bijection on homotopy groups.
* `TauCeti.homotopyGroupEquivOfHomotopyEquiv`, `TauCeti.homotopyGroupMulEquivOfHomotopyEquiv`:
  that bijection, as an equivalence and, in positive dimensions, as a group isomorphism.

## References

That a homotopy equivalence induces isomorphisms on all homotopy groups is Proposition 4.21 of
[hatcher02]; the trace formula for a free homotopy is the discussion preceding it in Section 4.1.
-/

public section
noncomputable section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy ContinuousMap
open Topology.Homotopy

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section Transport

variable [Fintype N]

namespace GenLoop

/-- Dragging a generalized loop `p` based at `x` through a homotopy `H` from `f` to `g` is a
homotopy from `f ∘ p` to `g ∘ p` along the trace of `H` at `x`: on the cube boundary `p` is
constant at `x`, so there the dragged loop traces `H.evalAt x`. -/
def homotopyAlongMap {f g : C(X, Y)} (H : f.Homotopy g) {x : X} (p : Ω^ N X x) :
    HomotopyAlong (H.evalAt x) (_root_.GenLoop.map f rfl p) (_root_.GenLoop.map g rfl p) where
  toContinuousMap := ⟨fun tz => H (tz.1, p tz.2), by fun_prop⟩
  map_zero_left z := H.apply_zero (p z)
  map_one_left z := H.apply_one (p z)
  map_boundary t z hz := congrArg (fun w => H (t, w)) (_root_.GenLoop.boundary p z hz)

/-- **Freely homotopic maps agree on generalized loops, up to transport along the trace of the
homotopy at the base point.** -/
theorem homotopic_map_transport {f g : C(X, Y)} (H : f.Homotopy g) {x : X} (p : Ω^ N X x) :
    _root_.GenLoop.Homotopic (_root_.GenLoop.map g rfl p)
      (transport (H.evalAt x) (_root_.GenLoop.map f rfl p)) :=
  (homotopyAlongMap H p).homotopic_transport

end GenLoop

/-- **Freely homotopic maps induce the same map on homotopy groups, after transporting along the
trace of the homotopy at the base point.** For a homotopy that fixes the base point the trace is
constant, and this is the pointed statement `HomotopyGroup.map_eq_of_homotopicRel`. -/
theorem homotopyGroupTransport_map {f g : C(X, Y)} (H : f.Homotopy g) {x : X}
    (a : HomotopyGroup N X x) :
    homotopyGroupTransport (H.evalAt x) (_root_.HomotopyGroup.map f rfl a) =
      _root_.HomotopyGroup.map g rfl a := by
  induction a using Quotient.inductionOn with
  | h p =>
    rw [_root_.HomotopyGroup.map_mk, homotopyGroupTransport_mk, _root_.HomotopyGroup.map_mk]
    exact (Quotient.sound (GenLoop.homotopic_map_transport H p)).symm

end Transport

section Finite

variable [Finite N]

/-- If `g ∘ f` is freely homotopic to the identity, the composite of the maps that `f` and `g`
induce on homotopy groups is a bijection: it is base-point change along the trace of the
homotopy, reversed. -/
theorem bijective_homotopyGroupMap_comp_of_homotopy_id {f : C(X, Y)} {g : C(Y, X)}
    (H : (g.comp f).Homotopy (ContinuousMap.id X)) (x : X) :
    Function.Bijective (_root_.HomotopyGroup.map (N := N) g rfl ∘
      _root_.HomotopyGroup.map (N := N) f (rfl : f x = f x)) := by
  have : Fintype N := Fintype.ofFinite N
  have key : ∀ a : HomotopyGroup N X x,
      homotopyGroupTransport (H.evalAt x)
        (_root_.HomotopyGroup.map g rfl (_root_.HomotopyGroup.map f rfl a)) = a := by
    intro a
    have hcomp : _root_.HomotopyGroup.map (N := N) g rfl
        (_root_.HomotopyGroup.map f (rfl : f x = f x) a) =
          _root_.HomotopyGroup.map (g.comp f) rfl a :=
      _root_.HomotopyGroup.map_comp_apply g rfl f rfl a
    rw [hcomp]
    exact (homotopyGroupTransport_map H a).trans (_root_.HomotopyGroup.map_id_apply a)
  have hfun : _root_.HomotopyGroup.map (N := N) g rfl ∘
      _root_.HomotopyGroup.map (N := N) f (rfl : f x = f x) =
        (homotopyGroupEquivOfPath (H.evalAt x)).symm := by
    funext a
    -- `rw [Equiv.eq_symm_apply]` fails here: the two sides sit over base points that agree only
    -- up to unfolding `ContinuousMap.comp` and `ContinuousMap.id`, so the rewrite is not
    -- type-correct at `implicit` transparency. In term mode the defeq is accepted.
    exact ((homotopyGroupEquivOfPath (H.evalAt x)).eq_symm_apply).mpr
      ((homotopyGroupEquivOfPath_apply _ _).trans (key a))
  rw [hfun]
  exact (homotopyGroupEquivOfPath (H.evalAt x)).symm.bijective

/-- **A homotopy equivalence induces a bijection on homotopy groups.** -/
theorem bijective_homotopyGroupMap_of_homotopyEquiv (e : X ≃ₕ Y) (x : X) :
    Function.Bijective
      (_root_.HomotopyGroup.map (N := N) e.toFun (rfl : e.toFun x = e.toFun x)) := by
  -- The left inverse makes the composite `e.invFun⁎ ∘ e.toFun⁎` bijective at `x`, the right
  -- inverse makes `e.toFun⁎ ∘ e.invFun⁎` bijective at `e.toFun x`. The map `e.invFun⁎` is common
  -- to the two composites, so it is injective as well as surjective, and then so is `e.toFun⁎`.
  have hleft := bijective_homotopyGroupMap_comp_of_homotopy_id (N := N) e.left_inv.some x
  have hright :=
    bijective_homotopyGroupMap_comp_of_homotopy_id (N := N) e.right_inv.some (e.toFun x)
  have hmid : Function.Injective (_root_.HomotopyGroup.map (N := N) e.invFun
      (rfl : e.invFun (e.toFun x) = e.invFun (e.toFun x))) := hright.injective.of_comp
  refine ⟨hleft.injective.of_comp, fun b => ?_⟩
  obtain ⟨a, ha⟩ := hleft.surjective (_root_.HomotopyGroup.map e.invFun rfl b)
  rw [Function.comp_apply] at ha
  exact ⟨a, hmid ha⟩

/-- The bijection on homotopy groups induced by a homotopy equivalence. -/
@[expose] def homotopyGroupEquivOfHomotopyEquiv (e : X ≃ₕ Y) (x : X) :
    HomotopyGroup N X x ≃ HomotopyGroup N Y (e.toFun x) :=
  Equiv.ofBijective _ (bijective_homotopyGroupMap_of_homotopyEquiv e x)

@[simp]
theorem homotopyGroupEquivOfHomotopyEquiv_apply (e : X ≃ₕ Y) (x : X) (a : HomotopyGroup N X x) :
    homotopyGroupEquivOfHomotopyEquiv e x a = _root_.HomotopyGroup.map e.toFun rfl a :=
  rfl

/-- **Homotopy equivalent spaces have isomorphic homotopy groups.** In positive dimensions the
bijection induced by a homotopy equivalence is a group isomorphism, being induced by a continuous
map. -/
@[expose] def homotopyGroupMulEquivOfHomotopyEquiv [Nonempty N] [DecidableEq N] (e : X ≃ₕ Y)
    (x : X) : HomotopyGroup N X x ≃* HomotopyGroup N Y (e.toFun x) :=
  MulEquiv.ofBijective (_root_.HomotopyGroup.mapHom e.toFun rfl)
    (bijective_homotopyGroupMap_of_homotopyEquiv e x)

@[simp]
theorem homotopyGroupMulEquivOfHomotopyEquiv_apply [Nonempty N] [DecidableEq N] (e : X ≃ₕ Y)
    (x : X) (a : HomotopyGroup N X x) :
    homotopyGroupMulEquivOfHomotopyEquiv e x a = _root_.HomotopyGroup.map e.toFun rfl a :=
  rfl

/-- Over a path connected space, homotopy equivalence identifies the homotopy groups in a fixed
positive dimension at *any* pair of base points, by composing with base-point change. -/
theorem nonempty_homotopyGroupMulEquiv_of_homotopyEquiv [Nonempty N] [DecidableEq N]
    [PathConnectedSpace X] (e : X ≃ₕ Y) (x : X) (y : Y) :
    Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N Y y) := by
  have : PathConnectedSpace Y := e.pathConnectedSpace
  obtain ⟨φ⟩ := nonempty_homotopyGroupMulEquiv (N := N) (X := Y) (x := e.toFun x) (y := y)
  exact ⟨(homotopyGroupMulEquivOfHomotopyEquiv e x).trans φ⟩

end Finite

end TauCeti
