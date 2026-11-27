/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
public import TauCeti.AlgebraicGeometry.Cover.Directed
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.CategoryTheory.Aut.Basic
public import TauCeti.CategoryTheory.Functor.LocallySmall
public import TauCeti.RingTheory.Etale.Small

/-!
# Smallness of finite étale covers and of étale fundamental groups

The category `TauCeti.FiniteEtaleScheme S` has objects in `Type (u + 1)`, and so does the
automorphism group `Aut (TauCeti.FiniteEtaleScheme.fiber x)` of a geometric fibre functor, the
étale fundamental group at `x`. This file shows that the finite étale covers of every scheme
`S : Scheme.{u}` form an essentially small category
(`TauCeti.FiniteEtaleScheme.essentiallySmall`), so that the group has a model in `Type u`. Once
the category is essentially small, `Small.{u} (Aut (fiber x))` is found by instance search,
through `TauCeti.locallySmall_functor_of_small_skeleton` and `TauCeti.small_aut`, and needs no
named theorem; an `example` below records it.

Over an affine base the covers are anti-equivalent to finite étale algebras over the ring of
global functions (`TauCeti.FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme`
transported along `AlgebraicGeometry.Scheme.isoSpec`). Finite étale algebras are of finite type,
so they form an essentially small category by Mathlib's essential smallness of finitely generated
algebras (`TauCeti.essentiallySmall_commAlgCatFiniteEtale`, in
`TauCeti.RingTheory.Etale.Small`).

Over a general base, every scheme `X` over `S` is the colimit, in `Over S`, of its restrictions
`X ×_S U` to the affine opens `U` of `S`, indexed by the affine opens ordered by inclusion
(`AlgebraicGeometry.Scheme.colimitPresentationAffineOpens`, in
`TauCeti.AlgebraicGeometry.Cover.Directed`, from Mathlib's colimit of a locally directed open
cover, `AlgebraicGeometry.Scheme.OpenCover.isColimitCoconeOfLocallyDirected`, applied to the
pullback of `S.directedAffineCover`). For a finite étale `X` each restriction is a
finite étale cover of the affine scheme `U`, pushed forward to `Over S`. These pushed-forward
covers form an essentially small property of `Over S`, a union over the small set of affine opens
of essential images of essentially small categories, and Mathlib's closure of an essentially
small property under colimits of one small shape is again essentially small
(`CategoryTheory.ObjectProperty.colimitsClosure`).

## Main results

* `TauCeti.FiniteEtaleScheme.essentiallySmall_of_isAffine`: finite étale covers of an affine
  scheme form an essentially small category.
* `TauCeti.FiniteEtaleScheme.essentiallySmall`: finite étale covers of any scheme form an
  essentially small category.

## References

* The Stacks Project, Section 58.5 (*Finite étale covers of schemes*).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe v u

namespace TauCeti

namespace FiniteEtaleScheme

/-- Finite étale covers of an affine scheme form an essentially small category: they are
anti-equivalent to finite étale algebras over its ring of global functions. -/
instance essentiallySmall_of_isAffine (S : Scheme.{u}) [IsAffine S] :
    EssentiallySmall.{u} (FiniteEtaleScheme S) :=
  (essentiallySmall_congr ((finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme _).trans
    (pullbackIsoEquiv S.isoSpec))).1 inferInstance

/-- Finite étale covers of any scheme `S` form an essentially small category. -/
instance essentiallySmall (S : Scheme.{u}) : EssentiallySmall.{u} (FiniteEtaleScheme S) := by
  let P : ObjectProperty (Over S) :=
    ⨆ U : S.affineOpens, ((finiteEtaleSchemeProperty U).ι ⋙ Over.map U.val.ι).essImage
  have hle : finiteEtaleSchemeProperty S ≤ P.colimitsClosure (fun _ : Unit ↦ S.affineOpens) := by
    intro X hX
    refine .of_colimitPresentation (a := ()) (S.colimitPresentationAffineOpens X)
      fun U ↦ .of_mem _ ((ObjectProperty.prop_iSup_iff _ _).2
        ⟨U, (pullback U.val.ι).obj ⟨X, hX⟩, ⟨?_⟩⟩)
    rw [Functor.comp_obj, ObjectProperty.ι_obj, pullback_obj_obj,
      Scheme.colimitPresentationAffineOpens_diag_obj]
    exact Over.isoMk (Iso.refl _) (by simp [pullback.condition])
  have := ObjectProperty.EssentiallySmall.of_le hle
  infer_instance

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/- The automorphism group of the geometric fibre functor at `x`, the étale fundamental group, has
a model in `Type u`. -/
example (x : Spec (.of Ω) ⟶ S) : Small.{u} (Aut (fiber x)) :=
  inferInstance

end FiniteEtaleScheme

end TauCeti
