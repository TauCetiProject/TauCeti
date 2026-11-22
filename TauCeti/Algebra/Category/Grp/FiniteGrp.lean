/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.FiniteGrp
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Isomorphism classes of finite groups

Invariants of a finite group such as its multiset of chief factors or of composition factors
record finite groups only up to isomorphism, and need a target type that does not depend on the
universe of the group at hand, so that invariants of groups in different universes can be
compared. This file provides the common target of such invariants:
`TauCeti.IsoClass`, the set of isomorphism classes of objects of Mathlib's category `FiniteGrp` of
finite groups in `Type`, together with `TauCeti.IsoClass.mk`, which sends a finite group in any
universe to its class through a copy of it on `Fin (Nat.card H)`.

## Main definitions

* `TauCeti.IsoClass`: the isomorphism classes of finite groups.
* `TauCeti.IsoClass.mk`: the isomorphism class of a finite group in any universe.

## Main results

* `FiniteGrp.isIsomorphic_iff_nonempty_mulEquiv`: two finite groups are isomorphic in `FiniteGrp`
  exactly when there is a group isomorphism between them.
* `TauCeti.IsoClass.mk_eq_mk_iff`: two finite groups have the same class exactly when they are
  isomorphic, whatever their universes.
* `TauCeti.IsoClass.exists_mk_eq`: every class is the class of a finite group.
-/

public section

open CategoryTheory

universe u v

/-- Two finite groups are isomorphic as objects of `FiniteGrp` exactly when there is a group
isomorphism between them. -/
theorem FiniteGrp.isIsomorphic_iff_nonempty_mulEquiv {X Y : FiniteGrp.{u}} :
    IsIsomorphic X Y ↔ Nonempty (X ≃* Y) :=
  ⟨fun ⟨i⟩ ↦ ⟨((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv⟩,
    fun ⟨e⟩ ↦ ⟨InducedCategory.isoMk e.toGrpIso⟩⟩

namespace TauCeti

/-- The isomorphism classes of finite groups: the objects of Mathlib's category `FiniteGrp` of
finite groups in `Type`, up to isomorphism. Every finite group, in any universe, has a class,
`TauCeti.IsoClass.mk`. -/
def IsoClass : Type 1 :=
  Quotient (isIsomorphicSetoid FiniteGrp.{0})

namespace IsoClass

/-- The copy of a finite group `H` on `Fin (Nat.card H)`, with the group structure transported
along `Finite.equivFin H`, as an object of `FiniteGrp` in `Type`. -/
private noncomputable def finiteGrpCopy (H : Type u) [Group H] [Finite H] : FiniteGrp.{0} :=
  @FiniteGrp.of (Fin (Nat.card H)) (Finite.equivFin H).symm.group _

/-- The copy `finiteGrpCopy H` of `H` is isomorphic to `H`. -/
private noncomputable def finiteGrpCopyMulEquiv (H : Type u) [Group H] [Finite H] :
    finiteGrpCopy H ≃* H :=
  (Finite.equivFin H).symm.mulEquiv

/-- The isomorphism class of a finite group `H` in any universe, through the copy of `H` on
`Fin (Nat.card H)` given by transporting the group structure along `Finite.equivFin H`. -/
noncomputable def mk (H : Type u) [Group H] [Finite H] : IsoClass :=
  Quotient.mk _ (finiteGrpCopy H)

/-- Two finite groups, possibly in different universes, have the same isomorphism class exactly
when they are isomorphic. -/
theorem mk_eq_mk_iff {H : Type u} {K : Type v} [Group H] [Finite H] [Group K] [Finite K] :
    mk H = mk K ↔ Nonempty (H ≃* K) := by
  refine (Quotient.eq (r := isIsomorphicSetoid _)).trans
    (FiniteGrp.isIsomorphic_iff_nonempty_mulEquiv.trans ?_)
  let eH := finiteGrpCopyMulEquiv H
  let eK := finiteGrpCopyMulEquiv K
  exact ⟨fun ⟨e⟩ ↦ ⟨(eH.symm.trans e).trans eK⟩, fun ⟨e⟩ ↦ ⟨(eH.trans e).trans eK.symm⟩⟩

/-- Isomorphic finite groups have the same isomorphism class. -/
theorem mk_eq_mk_of_mulEquiv {H : Type u} {K : Type v} [Group H] [Finite H] [Group K] [Finite K]
    (e : H ≃* K) : mk H = mk K :=
  mk_eq_mk_iff.mpr ⟨e⟩

/-- Every isomorphism class of finite groups is the class of a finite group in `Type`. -/
theorem exists_mk_eq (c : IsoClass) : ∃ H : FiniteGrp.{0}, mk H = c :=
  Quotient.inductionOn c fun H ↦ ⟨H, Quotient.sound
    (FiniteGrp.isIsomorphic_iff_nonempty_mulEquiv.mpr ⟨finiteGrpCopyMulEquiv H⟩)⟩

end IsoClass

end TauCeti
