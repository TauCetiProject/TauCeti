/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# The action of the fundamental group on the higher homotopy groups

Transporting a generalized loop along a path `γ` from `x` to `y` gives an isomorphism
`π_n(X, x) ≃* π_n(X, y)` depending only on the homotopy class of `γ`
(`TauCeti.homotopyGroupMulEquivOfPath`). Taking `y = x` turns that isomorphism into extra
structure carried by a single homotopy group: the fundamental group at `x` acts on `π_n(X, x)`
by group automorphisms. This file builds that action and identifies its orbits.

The action is the higher-dimensional analogue of the conjugation action of `π₁(X, x)` on
itself, and it is what the phrase "`π_n` is a `π₁`-module" (for `n ≥ 2`, where `π_n` is
abelian) abbreviates. Its orbits have a purely topological meaning, recorded here in
`TauCeti.homotopyGroup_mem_orbit_iff_exists_homotopyAlong`: two generalized loops based at `x`
lie in the
same orbit exactly when they are *freely* homotopic, that is, when some homotopy connects them
through generalized loops whose base points sweep out a loop at `x`. So the quotient of
`π_n(X, x)` by the action is the set of free homotopy classes of maps `Sⁿ → X`, and the action
is trivial precisely when based and free homotopy classes agree.

## Conventions

Transport composes covariantly — transporting along `γ` and then along `δ` transports along
`γ.trans δ` — while multiplication in `FundamentalGroup X x` is
`FundamentalGroup.mul_def : p * q = q.trans p`. The two conventions match, so transport is a
*left* action and no `ᵐᵒᵖ` is needed; this is the same bookkeeping that makes Mathlib's
monodromy action `IsCoveringMap.fundamentalGroupMulAction` a left action.

## Main declarations

* `TauCeti.homotopyGroupTransportQuotient`: transport of homotopy classes along a homotopy
  class of paths, with `TauCeti.homotopyGroupTransportQuotient_refl` and
  `TauCeti.homotopyGroupTransportQuotient_trans`.
* `TauCeti.homotopyGroupMulAction`: **the fundamental group acts on every homotopy group at
  the same base point**, with `TauCeti.fundamentalGroup_smul_mk` computing the action of the
  class of a loop.
* `TauCeti.homotopyGroupMulDistribMulAction` and `TauCeti.fundamentalGroupMulAut`: **in
  positive dimensions the action is by group automorphisms**.
* `TauCeti.map_fundamentalGroup_smul`: a based continuous map is equivariant for the actions on
  source and target, along the homomorphism it induces on fundamental groups.
* `TauCeti.homotopyGroup_mem_orbit_iff` and
  `TauCeti.homotopyGroup_mem_orbit_iff_exists_homotopyAlong`: **the orbits of the action are
  the free homotopy classes**, the latter through
  `TauCeti.GenLoop.exists_homotopyAlong_iff_exists_homotopic_transport`, which reads free
  homotopy as transport up to based homotopy.
* `TauCeti.fundamentalGroup_smul_eq_self`: on a simply connected space the action is trivial.

## References

This continues the higher-homotopy API requested in `TauCetiRoadmap/UniversalCovers/README.md`,
Stage 3, item 9, whose base-point-change half is `TauCeti.homotopyGroupMulEquivOfPath`. See
Hatcher, *Algebraic Topology*, Section 4.1, where the action is introduced immediately after
base-point change and the description of its orbits is the definition of an `n`-simple space.
-/

public section
noncomputable section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

variable {N : Type*} [Fintype N] {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x x' : X}

/-! ### Transport along a homotopy class of paths -/

/-- Transport of homotopy classes along a homotopy *class* of paths. This is
`TauCeti.homotopyGroupTransport` descended to `Path.Homotopic.Quotient`, which is legitimate
because homotopic paths transport alike. -/
def homotopyGroupTransportQuotient (γ : Path.Homotopic.Quotient x x') :
    HomotopyGroup N X x → HomotopyGroup N X x' :=
  Quotient.liftOn γ homotopyGroupTransport fun _ _ h => homotopyGroupTransport_congr h

/-- Transport along the class of a path is transport along the path. -/
@[simp]
theorem homotopyGroupTransportQuotient_mk (γ : Path x x') :
    homotopyGroupTransportQuotient (N := N) (.mk γ) = homotopyGroupTransport γ := by
  rfl

/-- Transport along the class of the constant path is the identity. -/
@[simp]
theorem homotopyGroupTransportQuotient_refl :
    homotopyGroupTransportQuotient (N := N) (.refl x) = id := by
  rw [← Path.Homotopic.Quotient.mk_refl, homotopyGroupTransportQuotient_mk,
    homotopyGroupTransport_refl]

/-- Transport along a composite of classes of paths is the composite of the two transports. -/
@[simp]
theorem homotopyGroupTransportQuotient_trans {x'' : X} (γ : Path.Homotopic.Quotient x x')
    (δ : Path.Homotopic.Quotient x' x'') :
    homotopyGroupTransportQuotient (N := N) (γ.trans δ) =
      homotopyGroupTransportQuotient δ ∘ homotopyGroupTransportQuotient γ := by
  induction γ with | mk p =>
  induction δ with | mk q =>
  rw [← Path.Homotopic.Quotient.mk_trans, homotopyGroupTransportQuotient_mk,
    homotopyGroupTransportQuotient_mk, homotopyGroupTransportQuotient_mk,
    homotopyGroupTransport_trans]

/-! ### The action of the fundamental group -/

/-- **The fundamental group at `x` acts on every homotopy group based at `x`**, an element of
`π₁(X, x)` acting by transport around the loop it represents.

The action is a left action: transport composes covariantly and `FundamentalGroup.mul_def`
reverses the order of concatenation, so the two reversals cancel. -/
instance homotopyGroupMulAction : MulAction (FundamentalGroup X x) (HomotopyGroup N X x) where
  smul γ a := homotopyGroupTransportQuotient γ.toPath a
  one_smul a := by
    change homotopyGroupTransportQuotient (1 : FundamentalGroup X x).toPath a = a
    rw [FundamentalGroup.one_def, homotopyGroupTransportQuotient_refl, id_eq]
  mul_smul γ δ a := by
    change homotopyGroupTransportQuotient (γ * δ).toPath a =
      homotopyGroupTransportQuotient γ.toPath (homotopyGroupTransportQuotient δ.toPath a)
    rw [FundamentalGroup.mul_def, homotopyGroupTransportQuotient_trans]
    rfl

/-- The action of the fundamental group is transport along the class of loops. -/
theorem fundamentalGroup_smul_def (γ : FundamentalGroup X x) (a : HomotopyGroup N X x) :
    γ • a = homotopyGroupTransportQuotient γ.toPath a := by
  rfl

/-- An element of `π₁(X, x)` represented by a loop `p` acts by transport along `p`. -/
theorem fundamentalGroup_smul_eq_transport {γ : FundamentalGroup X x} {p : Path x x}
    (h : γ.toPath = .mk p) (a : HomotopyGroup N X x) :
    γ • a = homotopyGroupTransport p a := by
  rw [fundamentalGroup_smul_def, h]
  exact congrFun (homotopyGroupTransportQuotient_mk p) a

/-- The class of a loop `p` acts by transport along `p`. -/
@[simp]
theorem fundamentalGroup_smul_mk (p : Path x x) (a : HomotopyGroup N X x) :
    (FundamentalGroup.fromPath (.mk p) : FundamentalGroup X x) • a =
      homotopyGroupTransport p a :=
  fundamentalGroup_smul_eq_transport rfl a

/-- Acting by an element of `π₁(X, x)` is base-point change along a representing loop. -/
theorem fundamentalGroup_smul_eq_homotopyGroupMulEquivOfPath [Nonempty N] [DecidableEq N]
    (p : Path x x) (a : HomotopyGroup N X x) :
    (FundamentalGroup.fromPath (.mk p) : FundamentalGroup X x) • a =
      homotopyGroupMulEquivOfPath p a := by
  rw [fundamentalGroup_smul_mk, homotopyGroupMulEquivOfPath_apply]

/-- **In positive dimensions the fundamental group acts by group automorphisms.** -/
instance homotopyGroupMulDistribMulAction [Nonempty N] [DecidableEq N] :
    MulDistribMulAction (FundamentalGroup X x) (HomotopyGroup N X x) where
  __ := (inferInstance : MulAction (FundamentalGroup X x) (HomotopyGroup N X x))
  smul_mul γ a b := by
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ.toPath
    rw [fundamentalGroup_smul_eq_homotopyGroupMulEquivOfPath,
      fundamentalGroup_smul_eq_homotopyGroupMulEquivOfPath,
      fundamentalGroup_smul_eq_homotopyGroupMulEquivOfPath, map_mul]
  smul_one γ := by
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ.toPath
    rw [fundamentalGroup_smul_eq_homotopyGroupMulEquivOfPath, map_one]

variable (N) in
/-- **The action of the fundamental group on a positive-dimensional homotopy group, as a
homomorphism into the automorphism group.** This is the `π₁`-module structure on `π_n`. -/
def fundamentalGroupMulAut [Nonempty N] [DecidableEq N] (x : X) :
    FundamentalGroup X x →* MulAut (HomotopyGroup N X x) :=
  MulDistribMulAction.toMulAut _ _

/-- The automorphism attached to an element of the fundamental group acts by that element. -/
@[simp]
theorem fundamentalGroupMulAut_apply [Nonempty N] [DecidableEq N] (γ : FundamentalGroup X x)
    (a : HomotopyGroup N X x) : fundamentalGroupMulAut N x γ a = γ • a := by
  rfl

/-! ### Naturality -/

namespace GenLoop

/-- Postcomposition with a continuous map commutes with transport, along the image path. -/
theorem map_transport (F : C(X, Y)) (γ : Path x x') (f : Ω^ N X x) :
    _root_.GenLoop.map F rfl (transport γ f) =
      transport (γ.map F.continuous) (_root_.GenLoop.map F rfl f) := by
  apply _root_.GenLoop.ext
  intro z
  rw [_root_.GenLoop.map_apply, transport_apply_eq, transport_apply_eq, apply_ite F]
  split_ifs <;> simp

end GenLoop

/-- Postcomposition with a continuous map commutes with transport of homotopy classes, along
the image class of paths. -/
theorem map_homotopyGroupTransportQuotient (F : C(X, Y)) (γ : Path.Homotopic.Quotient x x')
    (a : HomotopyGroup N X x) :
    _root_.HomotopyGroup.map F rfl (homotopyGroupTransportQuotient γ a) =
      homotopyGroupTransportQuotient (γ.map F) (_root_.HomotopyGroup.map F rfl a) := by
  induction γ with | mk p =>
  induction a using Quotient.inductionOn with | _ f =>
  rw [← Path.Homotopic.Quotient.mk_map, homotopyGroupTransportQuotient_mk,
    homotopyGroupTransportQuotient_mk]
  simp only [homotopyGroupTransport_mk, _root_.HomotopyGroup.map_mk]
  rw [GenLoop.map_transport]

/-- **A based continuous map is equivariant** for the actions of the fundamental groups on
source and target, along the homomorphism it induces on fundamental groups. -/
theorem map_fundamentalGroup_smul (F : C(X, Y)) (γ : FundamentalGroup X x)
    (a : HomotopyGroup N X x) :
    _root_.HomotopyGroup.map F rfl (γ • a) =
      FundamentalGroup.map F x γ • _root_.HomotopyGroup.map F rfl a := by
  rw [fundamentalGroup_smul_def, fundamentalGroup_smul_def,
    map_homotopyGroupTransportQuotient]
  rfl

/-! ### The orbits of the action -/

/-- Membership in an orbit of the action is transport: a class `b` lies in the orbit of `a`
exactly when some loop at `x` transports `a` to `b`. -/
theorem homotopyGroup_mem_orbit_iff (a b : HomotopyGroup N X x) :
    b ∈ MulAction.orbit (FundamentalGroup X x) a ↔
      ∃ p : Path x x, homotopyGroupTransport p a = b := by
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective γ.toPath
    exact ⟨p, (fundamentalGroup_smul_eq_transport hp.symm a).symm.trans hγ⟩
  · rintro ⟨p, rfl⟩
    exact ⟨FundamentalGroup.fromPath (.mk p), fundamentalGroup_smul_mk p a⟩

namespace GenLoop

/-- **Free homotopy is transport up to based homotopy.** A homotopy connecting two generalized
loops based at `x` through generalized loops, its base point sweeping out a loop, exists
exactly when one of them is homotopic, relative to the cube boundary, to the transport of the
other along a loop. -/
theorem exists_homotopyAlong_iff_exists_homotopic_transport (f g : Ω^ N X x) :
    (∃ γ : Path x x, Nonempty (HomotopyAlong γ f g)) ↔
      ∃ p : Path x x, _root_.GenLoop.Homotopic (transport p f) g := by
  constructor
  · rintro ⟨γ, ⟨h⟩⟩
    exact ⟨γ, h.homotopic_transport.symm⟩
  · rintro ⟨p, hp⟩
    obtain ⟨K⟩ := HomotopyAlong.nonempty_of_homotopic hp
    exact ⟨p.trans (Path.refl x), ⟨(collarHomotopyAlong p f).trans K⟩⟩

end GenLoop

/-- **The orbits of the action of `π₁(X, x)` on `π_n(X, x)` are the free homotopy classes.**
Classes of two generalized loops based at `x` lie in the same orbit exactly when some homotopy
connects the two loops through generalized loops, the base point sweeping out a loop at `x`. So
the quotient of `π_n(X, x)` by the action is the set of free homotopy classes of maps
`Sⁿ → X`.

The two classes are given by representatives rather than written as `⟦f⟧` and `⟦g⟧` directly,
because the type of `⟦f⟧` is the underlying quotient rather than `HomotopyGroup N X x`, which
hides the action from instance search. -/
theorem homotopyGroup_mem_orbit_iff_exists_homotopyAlong {a b : HomotopyGroup N X x}
    {f g : Ω^ N X x}
    (ha : a = ⟦f⟧) (hb : b = ⟦g⟧) :
    b ∈ MulAction.orbit (FundamentalGroup X x) a ↔
      ∃ γ : Path x x, Nonempty (GenLoop.HomotopyAlong γ f g) := by
  rw [homotopyGroup_mem_orbit_iff,
    GenLoop.exists_homotopyAlong_iff_exists_homotopic_transport]
  refine exists_congr fun p => ?_
  rw [ha, hb, homotopyGroupTransport_mk]
  exact Quotient.eq

/-- On a space with trivial fundamental group at `x` — a simply connected space, for instance —
the action is trivial, so based and free homotopy classes of maps `Sⁿ → X` agree. -/
theorem fundamentalGroup_smul_eq_self [Subsingleton (FundamentalGroup X x)]
    (γ : FundamentalGroup X x) (a : HomotopyGroup N X x) : γ • a = a := by
  rw [Subsingleton.elim γ 1, one_smul]

end TauCeti
