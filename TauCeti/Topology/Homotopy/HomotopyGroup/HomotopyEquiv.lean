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

The trace formula takes the base points of the two induced maps as equations, as
`HomotopyGroup.map` does, and the trace is recast along them with `Path.cast`. This is what lets
a round trip `g ∘ f ≃ id` be stated at the base points `g (f x)` and `x` themselves, rather than at
`(g.comp f) x` and `(ContinuousMap.id X) x`.

Applied to a homotopy equivalence `e : X ≃ₕ Y`, this makes each round trip of `e` bijective on
homotopy groups after correcting the base point. Both round trips are needed: a homotopy inverse
recovers the identity only up to a free homotopy, so one composite alone gives injectivity of the
map induced by `e.toFun` and surjectivity of the map induced by `e.invFun`, and the other
composite is what upgrades the latter to a bijection. The inverse of the resulting bijection is
the map induced by `e.invFun`, corrected by base-point change along the trace of the round trip.

The statements about the induced map alone need no finiteness of the index type beyond
`[Finite N]`; the statements that mention transport, which uses the collar construction, ask for
the `[Fintype N]` that the cube radius uses.

## Main declarations

* `TauCeti.GenLoop.homotopyAlongMap`: dragging a generalized loop through a homotopy is a
  homotopy along the trace of that homotopy at the base point.
* `TauCeti.homotopyGroupTransport_map`: **freely homotopic maps induce the same map on homotopy
  groups, up to transport along the trace of the homotopy.**
* `TauCeti.homotopyGroupTransport_map_map`: the case of a round trip `g ∘ f ≃ id`.
* `HomotopyGroup.map_bijective_of_homotopyEquiv`: a homotopy equivalence induces a bijection on
  homotopy groups.
* `HomotopyGroup.equivOfHomotopyEquiv`, `HomotopyGroup.mulEquivOfHomotopyEquiv`: that bijection,
  as an equivalence and, in positive dimensions, as a group isomorphism, with their identity and
  composition laws.

## References

That a homotopy equivalence induces isomorphisms on all homotopy groups is Proposition 4.21 of
[hatcher02]; the trace formula for a free homotopy is the discussion preceding it in Section 4.1.
-/

public section
noncomputable section

open scoped unitInterval Topology Topology.Homotopy ContinuousMap
open Topology.Homotopy

namespace TauCeti

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section Transport

variable [Fintype N]

namespace GenLoop

/-- Dragging a generalized loop `p` based at `x` through a homotopy `H` from `f` to `g` is a
homotopy from `f ∘ p` to `g ∘ p` along the trace of `H` at `x`: on the cube boundary `p` is
constant at `x`, so there the dragged loop traces `H.evalAt x`. -/
def homotopyAlongMap {f g : C(X, Y)} (H : f.Homotopy g) {x : X} {y₀ y₁ : Y} (hf : f x = y₀)
    (hg : g x = y₁) (p : Ω^ N X x) :
    HomotopyAlong ((H.evalAt x).cast hf.symm hg.symm) (_root_.GenLoop.map f hf p)
      (_root_.GenLoop.map g hg p) where
  toContinuousMap := ⟨fun tz => H (tz.1, p tz.2), by fun_prop⟩
  map_zero_left z := H.apply_zero (p z)
  map_one_left z := H.apply_one (p z)
  map_boundary t z hz := congrArg (fun w => H (t, w)) (_root_.GenLoop.boundary p z hz)

/-- **Freely homotopic maps agree on generalized loops, up to transport along the trace of the
homotopy at the base point.** -/
theorem homotopic_map_transport {f g : C(X, Y)} (H : f.Homotopy g) {x : X} {y₀ y₁ : Y}
    (hf : f x = y₀) (hg : g x = y₁) (p : Ω^ N X x) :
    _root_.GenLoop.Homotopic (_root_.GenLoop.map g hg p)
      (transport ((H.evalAt x).cast hf.symm hg.symm) (_root_.GenLoop.map f hf p)) :=
  (homotopyAlongMap H hf hg p).homotopic_transport

end GenLoop

/-- **Freely homotopic maps induce the same map on homotopy groups, after transporting along the
trace of the homotopy at the base point.** For a homotopy that fixes the base point the trace is
constant, and this is the pointed statement `HomotopyGroup.map_eq_of_homotopicRel`. -/
theorem homotopyGroupTransport_map {f g : C(X, Y)} (H : f.Homotopy g) {x : X} {y₀ y₁ : Y}
    (hf : f x = y₀) (hg : g x = y₁) (a : HomotopyGroup N X x) :
    homotopyGroupTransport ((H.evalAt x).cast hf.symm hg.symm) (_root_.HomotopyGroup.map f hf a) =
      _root_.HomotopyGroup.map g hg a := by
  induction a using Quotient.inductionOn with
  | h p =>
    rw [_root_.HomotopyGroup.map_mk, homotopyGroupTransport_mk, _root_.HomotopyGroup.map_mk]
    exact (Quotient.sound (GenLoop.homotopic_map_transport H hf hg p)).symm

/-- If `g ∘ f` is freely homotopic to the identity, then transport along the trace of the
homotopy undoes the composite of the maps that `f` and `g` induce on homotopy groups. -/
theorem homotopyGroupTransport_map_map {f : C(X, Y)} {g : C(Y, X)}
    (H : (g.comp f).Homotopy (ContinuousMap.id X)) (x : X) (a : HomotopyGroup N X x) :
    homotopyGroupTransport
        ((H.evalAt x).cast (ContinuousMap.comp_apply g f x).symm (ContinuousMap.id_apply x).symm)
        (_root_.HomotopyGroup.map g rfl (_root_.HomotopyGroup.map f rfl a)) = a := by
  rw [_root_.HomotopyGroup.map_comp_apply]
  exact (homotopyGroupTransport_map H _ (ContinuousMap.id_apply x) a).trans
    (_root_.HomotopyGroup.map_id_apply a)

end Transport

end TauCeti

namespace HomotopyGroup

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section Finite

variable [Finite N]

/-- If `g ∘ f` is freely homotopic to the identity, the composite of the maps that `f` and `g`
induce on homotopy groups is a bijection: it is base-point change along the trace of the
homotopy, reversed. -/
theorem map_comp_map_bijective_of_homotopy_id {f : C(X, Y)} {g : C(Y, X)}
    (H : (g.comp f).Homotopy (ContinuousMap.id X)) (x : X) :
    Function.Bijective (map (N := N) g rfl ∘ map (N := N) f (rfl : f x = f x)) := by
  have : Fintype N := Fintype.ofFinite N
  have hfun : map (N := N) g rfl ∘ map (N := N) f (rfl : f x = f x) =
      (TauCeti.homotopyGroupEquivOfPath ((H.evalAt x).cast (ContinuousMap.comp_apply g f x).symm
        (ContinuousMap.id_apply x).symm)).symm := by
    funext a
    rw [Function.comp_apply, Equiv.eq_symm_apply, TauCeti.homotopyGroupEquivOfPath_apply]
    exact TauCeti.homotopyGroupTransport_map_map H x a
  rw [hfun]
  exact Equiv.bijective _

/-- **A homotopy equivalence induces a bijection on homotopy groups.** -/
theorem map_bijective_of_homotopyEquiv (e : X ≃ₕ Y) (x : X) :
    Function.Bijective (map (N := N) e.toFun (rfl : e.toFun x = e.toFun x)) := by
  -- The left inverse makes the composite `e.invFun⁎ ∘ e.toFun⁎` bijective at `x`, the right
  -- inverse makes `e.toFun⁎ ∘ e.invFun⁎` bijective at `e.toFun x`. The map `e.invFun⁎` is common
  -- to the two composites, so it is injective as well as surjective, and then so is `e.toFun⁎`.
  -- The surjectivity of `e.toFun⁎` cannot be read off the second composite directly: there
  -- `e.toFun⁎` is based at `e.invFun (e.toFun x)`, not at `x`.
  have hleft := map_comp_map_bijective_of_homotopy_id (N := N) e.left_inv.some x
  have hright := map_comp_map_bijective_of_homotopy_id (N := N) e.right_inv.some (e.toFun x)
  have hmid : Function.Injective (map (N := N) e.invFun
      (rfl : e.invFun (e.toFun x) = e.invFun (e.toFun x))) := hright.injective.of_comp
  refine ⟨hleft.injective.of_comp, fun b => ?_⟩
  obtain ⟨a, ha⟩ := hleft.surjective (map e.invFun rfl b)
  rw [Function.comp_apply] at ha
  exact ⟨a, hmid ha⟩

/-- The bijection on homotopy groups induced by a homotopy equivalence. -/
def equivOfHomotopyEquiv (e : X ≃ₕ Y) (x : X) :
    HomotopyGroup N X x ≃ HomotopyGroup N Y (e.toFun x) :=
  Equiv.ofBijective _ (map_bijective_of_homotopyEquiv e x)

@[simp]
theorem equivOfHomotopyEquiv_apply (e : X ≃ₕ Y) (x : X) (a : HomotopyGroup N X x) :
    equivOfHomotopyEquiv e x a = map e.toFun rfl a :=
  (rfl)

/-- **A homotopy equivalence induces a group isomorphism on homotopy groups.** In positive
dimensions the bijection induced by a homotopy equivalence is a group isomorphism, being induced
by a continuous map. -/
def mulEquivOfHomotopyEquiv [Nonempty N] [DecidableEq N] (e : X ≃ₕ Y) (x : X) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y (e.toFun x) :=
  MulEquiv.ofBijective (mapHom e.toFun rfl) (map_bijective_of_homotopyEquiv e x)

@[simp]
theorem mulEquivOfHomotopyEquiv_apply [Nonempty N] [DecidableEq N] (e : X ≃ₕ Y) (x : X)
    (a : HomotopyGroup N X x) :
    mulEquivOfHomotopyEquiv e x a = map e.toFun rfl a :=
  (rfl)

/-- The identity homotopy equivalence induces the identity on homotopy groups. -/
@[simp]
theorem equivOfHomotopyEquiv_refl (x : X) :
    equivOfHomotopyEquiv (N := N) (ContinuousMap.HomotopyEquiv.refl X) x = Equiv.refl _ :=
  Equiv.ext map_id_apply

/-- The bijection induced by a composite of homotopy equivalences is the composite of the
induced bijections. -/
@[simp]
theorem equivOfHomotopyEquiv_trans {Z : Type*} [TopologicalSpace Z] (e : X ≃ₕ Y) (e' : Y ≃ₕ Z)
    (x : X) :
    equivOfHomotopyEquiv (N := N) (e.trans e') x =
      (equivOfHomotopyEquiv e x).trans (equivOfHomotopyEquiv e' (e.toFun x)) :=
  Equiv.ext fun a => (map_comp_apply _ rfl _ rfl a).symm

/-- The identity homotopy equivalence induces the identity isomorphism on homotopy groups. -/
@[simp]
theorem mulEquivOfHomotopyEquiv_refl [Nonempty N] [DecidableEq N] (x : X) :
    mulEquivOfHomotopyEquiv (N := N) (ContinuousMap.HomotopyEquiv.refl X) x = MulEquiv.refl _ :=
  MulEquiv.ext map_id_apply

/-- The isomorphism induced by a composite of homotopy equivalences is the composite of the
induced isomorphisms. -/
@[simp]
theorem mulEquivOfHomotopyEquiv_trans [Nonempty N] [DecidableEq N] {Z : Type*}
    [TopologicalSpace Z] (e : X ≃ₕ Y) (e' : Y ≃ₕ Z) (x : X) :
    mulEquivOfHomotopyEquiv (N := N) (e.trans e') x =
      (mulEquivOfHomotopyEquiv e x).trans (mulEquivOfHomotopyEquiv e' (e.toFun x)) :=
  MulEquiv.ext fun a => (map_comp_apply _ rfl _ rfl a).symm

end Finite

variable [Fintype N]

/-- The inverse of the bijection induced by a homotopy equivalence `e` is the map induced by
`e.invFun`, followed by base-point change along the trace of the round trip
`e.invFun ∘ e.toFun ≃ id`. -/
@[simp]
theorem equivOfHomotopyEquiv_symm_apply (e : X ≃ₕ Y) (x : X) (b : HomotopyGroup N Y (e.toFun x)) :
    (equivOfHomotopyEquiv e x).symm b =
      TauCeti.homotopyGroupTransport
        ((e.left_inv.some.evalAt x).cast (ContinuousMap.comp_apply e.invFun e.toFun x).symm
          (ContinuousMap.id_apply x).symm) (map e.invFun rfl b) := by
  obtain ⟨a, rfl⟩ := (equivOfHomotopyEquiv e x).surjective b
  rw [Equiv.symm_apply_apply, equivOfHomotopyEquiv_apply,
    TauCeti.homotopyGroupTransport_map_map]

/-- The inverse of the group isomorphism induced by a homotopy equivalence `e` is the map induced
by `e.invFun`, followed by base-point change along the trace of the round trip
`e.invFun ∘ e.toFun ≃ id`. -/
@[simp]
theorem mulEquivOfHomotopyEquiv_symm_apply [Nonempty N] [DecidableEq N] (e : X ≃ₕ Y) (x : X)
    (b : HomotopyGroup N Y (e.toFun x)) :
    (mulEquivOfHomotopyEquiv e x).symm b =
      TauCeti.homotopyGroupTransport
        ((e.left_inv.some.evalAt x).cast (ContinuousMap.comp_apply e.invFun e.toFun x).symm
          (ContinuousMap.id_apply x).symm) (map e.invFun rfl b) := by
  obtain ⟨a, rfl⟩ := (mulEquivOfHomotopyEquiv e x).surjective b
  rw [MulEquiv.symm_apply_apply, mulEquivOfHomotopyEquiv_apply,
    TauCeti.homotopyGroupTransport_map_map]

end HomotopyGroup

namespace TauCeti

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Over a path connected space, homotopy equivalence identifies the homotopy groups in a fixed
positive dimension at *any* pair of base points, by composing with base-point change. -/
theorem nonempty_homotopyGroupMulEquiv_of_homotopyEquiv [Finite N] [Nonempty N] [DecidableEq N]
    [PathConnectedSpace X] (e : X ≃ₕ Y) (x : X) (y : Y) :
    Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N Y y) := by
  have : PathConnectedSpace Y := e.pathConnectedSpace
  obtain ⟨φ⟩ := nonempty_homotopyGroupMulEquiv (N := N) (X := Y) (x := e.toFun x) (y := y)
  exact ⟨(HomotopyGroup.mulEquivOfHomotopyEquiv e x).trans φ⟩

end TauCeti
