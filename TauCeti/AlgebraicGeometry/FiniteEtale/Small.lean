/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.CategoryTheory.Aut.Basic
public import TauCeti.CategoryTheory.Functor.LocallySmall
public import TauCeti.RingTheory.Etale.Small

/-!
# Smallness of finite étale covers and of étale fundamental groups

The category `TauCeti.FiniteEtaleScheme S` has objects in `Type (u + 1)`, and so does the
automorphism group `Aut (TauCeti.FiniteEtaleScheme.fiber x)` of a geometric fibre functor, the
étale fundamental group at `x`. This file shows that the group has a model in `Type u` whenever
the finite étale covers of `S` form an essentially small category, and that they do over an
affine base (`TauCeti.FiniteEtaleScheme.essentiallySmall_of_isAffine`). The first statement is
found by instance search, through `TauCeti.locallySmall_functor_of_small_skeleton` and
`TauCeti.small_aut`, so `Small.{u} (Aut (fiber x))` needs no named theorem; an `example` below
records it.

Over an affine base the covers are anti-equivalent to finite étale algebras over the ring of
global functions (`TauCeti.FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme`
transported along `AlgebraicGeometry.Scheme.isoSpec`). Finite étale algebras are of finite type,
so they form an essentially small category by Mathlib's essential smallness of finitely generated
algebras (`TauCeti.essentiallySmall_commAlgCatFiniteEtale`, in
`TauCeti.RingTheory.Etale.Small`).

## Main results

* `TauCeti.FiniteEtaleScheme.essentiallySmall_of_isAffine`: finite étale covers of an affine
  scheme form an essentially small category.

## References

* The Stacks Project, Section 58.5 (*Finite étale covers of schemes*).
-/

public section

open CategoryTheory AlgebraicGeometry

universe v u

namespace TauCeti

namespace FiniteEtaleScheme

/-- Finite étale covers of an affine scheme form an essentially small category: they are
anti-equivalent to finite étale algebras over its ring of global functions. -/
instance essentiallySmall_of_isAffine (S : Scheme.{u}) [IsAffine S] :
    EssentiallySmall.{u} (FiniteEtaleScheme S) :=
  (essentiallySmall_congr ((finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme _).trans
    (pullbackIsoEquiv S.isoSpec))).1 inferInstance

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/- If the finite étale covers of `S` form an essentially small category, the automorphism group
of the geometric fibre functor at `x`, the étale fundamental group, has a model in `Type u`. -/
example [EssentiallySmall.{u} (FiniteEtaleScheme S)] (x : Spec (.of Ω) ⟶ S) :
    Small.{u} (Aut (fiber x)) :=
  inferInstance

end FiniteEtaleScheme

end TauCeti
