/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange

/-!
# The action of the fundamental group on the higher homotopy groups

Transporting a generalized loop along a path `γ` from `x` to `y` gives an isomorphism
`π_n(X, x) ≃* π_n(X, y)` depending only on the homotopy class of `γ`
(`TauCeti.homotopyGroupMulEquivOfPath`). Taking `y = x` turns that isomorphism into extra
structure carried by a single homotopy group: the fundamental group at `x` acts on the type
`π_n(X, x)`, and in positive dimensions — where that type carries a group structure — it acts
by group automorphisms. This file builds that action and identifies its orbits.

The action is the higher-dimensional analogue of the conjugation action of `π₁(X, x)` on
itself, and in dimensions at least two, where `π_n` is abelian, it is what the phrase
"`π_n` is a `π₁`-module" abbreviates. Its orbits have a purely topological meaning, recorded
here in `TauCeti.homotopyGroup_mem_orbit_iff_exists_homotopyAlong`: two generalized loops based
at `x` lie in the same orbit exactly when they are *freely* homotopic, that is, when some
homotopy connects them through generalized loops whose base points sweep out a loop at `x`.
So the quotient of
`π_n(X, x)` by the action is, in positive dimensions, the set of free homotopy classes of maps
`Sⁿ → X` landing in the path component of `x`. In dimension zero, it instead records the
classes for which the distinguished point of `S⁰` remains in the path component of `x`. The
action is trivial precisely when the corresponding based and free homotopy classes agree.

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
  the free homotopy classes into the path component of `x` in positive dimensions (with the
  distinguished point restricted to the component of `x` in dimension zero)**, the latter through
  `TauCeti.GenLoop.exists_homotopyAlong_iff_exists_homotopic_transport`, which reads free
  homotopy as transport up to based homotopy.
* `TauCeti.fundamentalGroup_smul_eq_self`: on a simply connected space the action is trivial.

## References

See Hatcher, *Algebraic Topology*, Section 4.1, where the action is introduced immediately after
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

/-- The fundamental group at `x` acts on a homotopy group based at `x` by transport around
loops; `TauCeti.homotopyGroupMulAction` shows that this is a group action. -/
instance homotopyGroupSMul : SMul (FundamentalGroup X x) (HomotopyGroup N X x) where
  smul γ a := homotopyGroupTransportQuotient γ.toPath a

/-- The action of the fundamental group is transport along the class of loops. -/
theorem fundamentalGroup_smul_def (γ : FundamentalGroup X x) (a : HomotopyGroup N X x) :
    γ • a = homotopyGroupTransportQuotient γ.toPath a := by
  rfl

/-- **The fundamental group at `x` acts on every homotopy group based at `x`**, an element of
`π₁(X, x)` acting by transport around the loop it represents.

The action is a left action: transport composes covariantly and `FundamentalGroup.mul_def`
reverses the order of concatenation, so the two reversals cancel. -/
instance homotopyGroupMulAction : MulAction (FundamentalGroup X x) (HomotopyGroup N X x) where
  one_smul a := by
    rw [fundamentalGroup_smul_def, FundamentalGroup.one_def, homotopyGroupTransportQuotient_refl,
      id_eq]
  mul_smul γ δ a := by
    rw [fundamentalGroup_smul_def, fundamentalGroup_smul_def, fundamentalGroup_smul_def,
      FundamentalGroup.mul_def, homotopyGroupTransportQuotient_trans, Function.comp_apply]

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
homomorphism into the automorphism group.** In dimensions at least two, where `π_n` is abelian,
this is the `π₁`-module structure on `π_n`; in dimension one it is an action of `π₁(X, x)` on
itself by group automorphisms. -/
def fundamentalGroupMulAut [Nonempty N] [DecidableEq N] (x : X) :
    FundamentalGroup X x →* MulAut (HomotopyGroup N X x) :=
  MulDistribMulAction.toMulAut _ _

/-- The automorphism attached to an element of the fundamental group acts by that element. -/
@[simp]
theorem fundamentalGroupMulAut_apply [Nonempty N] [DecidableEq N] (γ : FundamentalGroup X x)
    (a : HomotopyGroup N X x) : fundamentalGroupMulAut N x γ a = γ • a := by
  rfl

/-! ### Naturality -/

/-- Postcomposition with a continuous map commutes with transport of homotopy classes, along
the image class of paths. -/
@[simp]
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
@[simp]
theorem map_fundamentalGroup_smul (F : C(X, Y)) (γ : FundamentalGroup X x)
    (a : HomotopyGroup N X x) :
    _root_.HomotopyGroup.map F rfl (γ • a) =
      FundamentalGroup.map F x γ • _root_.HomotopyGroup.map F rfl a := by
  rw [fundamentalGroup_smul_def, fundamentalGroup_smul_def,
    map_homotopyGroupTransportQuotient]
  rw [FundamentalGroup.map_apply]

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
    obtain ⟨K⟩ := Nonempty.map HomotopyAlong.ofHomotopyRel hp
    exact ⟨p.trans (Path.refl x), ⟨(collarHomotopyAlong p f).trans K⟩⟩

end GenLoop

/-- **In positive dimensions, the orbits of the action of `π₁(X, x)` on `π_n(X, x)` are the
free homotopy classes.** Classes of two generalized loops based at `x` lie in the same orbit
exactly when some homotopy connects the two loops through generalized loops, the base point
sweeping out a loop at `x`. Thus in positive dimensions the quotient of `π_n(X, x)` by the
action is the set of free homotopy classes of maps `Sⁿ → X` landing in the path component of
`x`. In dimension zero, it instead classifies the free homotopy classes of maps `S⁰ → X` whose
distinguished point lies in the path component of `x`. -/
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
the action is trivial. Thus in positive dimensions based and free homotopy classes of maps
`Sⁿ → X` landing in the path component of `x` agree; in dimension zero this uses the
interpretation with the distinguished point restricted to the path component of `x`. -/
@[simp]
theorem fundamentalGroup_smul_eq_self [Subsingleton (FundamentalGroup X x)]
    (γ : FundamentalGroup X x) (a : HomotopyGroup N X x) : γ • a = a := by
  rw [Subsingleton.elim γ 1, one_smul]

end TauCeti
