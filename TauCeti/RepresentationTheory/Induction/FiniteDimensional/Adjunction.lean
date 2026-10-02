/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Limits
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Basic

/-!
# Adjunctions and exactness of finite-dimensional induction

Induction from a finite-index subgroup is both left and right adjoint to restriction on
finite-dimensional representations. Consequently it preserves finite limits and finite colimits,
and sends short exact sequences to short exact sequences over every field, including when the
group order vanishes in the field. This permits induction to descend to the exact Grothendieck
group, where nonsplit short exact sequences impose relations.

The adjunctions are restrictions of Mathlib's `Rep.indResAdjunction` and `Rep.resIndAdjunction`
along the fully faithful inclusions of finite-dimensional representations. The comparison with
ordinary induction is `TauCeti.indFDRepForgetNatIso`.

Import this file to infer `PreservesFiniteLimits` and `PreservesFiniteColimits` for
`indFDRepFunctor`. With the short-exact-sequence API imported, apply
`CategoryTheory.ShortComplex.ShortExact.map_of_exact` to obtain preservation of short exact
sequences. No semisimplicity or finiteness of the ambient group is required.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable {k G : Type u} [Field k] [Group G] {S : Subgroup G} [S.FiniteIndex]

/-- Finite-dimensional induction from a finite-index subgroup is left adjoint to restriction. -/
noncomputable def indResFDRepAdjunction :
    indFDRepFunctor (k := k) (S := S) ⊣ Action.res (FGModuleCat k) S.subtype :=
  (Rep.indResAdjunction.{u, u, u, u} k S.subtype).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (forget₂ (FDRep k S) (Rep k S)))
    (Functor.FullyFaithful.ofFullyFaithful (forget₂ (FDRep k G) (Rep k G)))
    indFDRepForgetNatIso.symm
    -- Restriction and the inclusion both retain the underlying module and action maps.
    (eqToIso (by rfl))

/-- For a finite-index subgroup, restriction is also left adjoint to finite-dimensional
induction. -/
noncomputable def resIndFDRepAdjunction :
    Action.res (FGModuleCat k) S.subtype ⊣ indFDRepFunctor (k := k) (S := S) := by
  classical
  exact (Rep.resIndAdjunction.{u, u, u} k S).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (forget₂ (FDRep k G) (Rep k G)))
    (Functor.FullyFaithful.ofFullyFaithful (forget₂ (FDRep k S) (Rep k S)))
    -- Restriction commutes with the inclusion on both objects and morphisms.
    (eqToIso (by rfl)) indFDRepForgetNatIso.symm

/-- Finite-dimensional induction is a left adjoint. -/
noncomputable instance indFDRepFunctor_isLeftAdjoint :
    (indFDRepFunctor (k := k) (S := S)).IsLeftAdjoint :=
  indResFDRepAdjunction.isLeftAdjoint

/-- Finite-dimensional induction from a finite-index subgroup is a right adjoint. -/
noncomputable instance indFDRepFunctor_isRightAdjoint :
    (indFDRepFunctor (k := k) (S := S)).IsRightAdjoint :=
  resIndFDRepAdjunction.isRightAdjoint

end TauCeti
