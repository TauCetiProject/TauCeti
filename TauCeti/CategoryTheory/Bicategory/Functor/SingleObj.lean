/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.LocallyDiscrete

/-!
# Constant pseudofunctors with one-object fibres

For a category `C` and a monoid `M`, `TauCeti.constSingleObj C M` is the constant pseudofunctor
`LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` with fibre the one-object category `SingleObj M` and identities as
pullbacks. A monoid homomorphism `φ : M →* N` induces the strong transformation
`TauCeti.constSingleObjMap C φ : constSingleObj C M ⟶ constSingleObj C N`, whose components are
the functor `SingleObj.mapHom M N φ` (`TauCeti.constSingleObjMap_app`): they send the unique
object to the unique object (`TauCeti.constSingleObjMap_app_obj`) and a morphism `m` to `φ m`
(`TauCeti.constSingleObjMap_app_map`).
-/

public section

universe w v u

open CategoryTheory Bicategory Pseudofunctor
open scoped Pseudofunctor.StrongTrans

namespace TauCeti

variable (C : Type u) [Category.{v} C] {M N : Type w} [Monoid M] [Monoid N]

/-- The constant pseudofunctor on `C` with fibre the one-object category `SingleObj M` of a
monoid `M`, and identities as pullbacks. -/
abbrev constSingleObj (M : Type w) [Monoid M] : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w, 0} :=
  ((Functor.const Cᵒᵖ).obj (Cat.of (SingleObj M))).toPseudofunctor.comp (𝟭 Cat).toPseudofunctor'

/-- The strong transformation of constant pseudofunctors on `C` with one-object fibres induced by
a monoid homomorphism `φ : M →* N`: each component is the functor `SingleObj M ⥤ SingleObj N` of
`φ`. -/
def constSingleObjMap (φ : M →* N) : constSingleObj C M ⟶ constSingleObj C N :=
  (𝟭 Cat).toPseudofunctor'.mapNatTrans ((Functor.const Cᵒᵖ).map (SingleObj.mapHom M N φ).toCatHom)

variable {C}

/-- The components of `constSingleObjMap C φ` are the functor `SingleObj.mapHom M N φ`. -/
lemma constSingleObjMap_app (φ : M →* N) (U : LocallyDiscrete Cᵒᵖ) :
    (constSingleObjMap C φ).app U = (SingleObj.mapHom M N φ).toCatHom :=
  (rfl)

/-- The components of `constSingleObjMap C φ` send the unique object to the unique object. -/
@[simp]
lemma constSingleObjMap_app_obj (φ : M →* N) (U : LocallyDiscrete Cᵒᵖ)
    (x : (constSingleObj C M).obj U) :
    ((constSingleObjMap C φ).app U).toFunctor.obj x = SingleObj.star N :=
  (rfl)

/-- The components of `constSingleObjMap C φ` send a morphism `m` of `SingleObj M` to `φ m`. -/
@[simp]
lemma constSingleObjMap_app_map (φ : M →* N) (U : LocallyDiscrete Cᵒᵖ)
    {x y : (constSingleObj C M).obj U} (m : x ⟶ y) :
    ((constSingleObjMap C φ).app U).toFunctor.map m = (φ m : N) :=
  (rfl)

end TauCeti
