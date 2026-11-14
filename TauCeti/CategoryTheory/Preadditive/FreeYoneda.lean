/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Morphisms from free abelian representable presheaves

The free-forgetful adjunction and the Yoneda lemma identify morphisms from the free abelian
presheaf on a representable with sections. `CategoryTheory.Functor.freeYonedaHomIso` packages
this as an isomorphism of abelian presheaves, natural in the represented object. The universe
lift accounts for the universe of natural transformations. This identification allows the
exact functor `Hom(-, P)` for an injective presheaf `P` to compute its Čech complex.

Adapted from the free-presheaf identification in split 5 of the
[lookahead development](https://github.com/roed-math/TauCeti-w2-fresh/tree/lookahead/SchemeAndStackFoundations/leray-spectral-sequence).
-/

public section

noncomputable section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

/-- Morphisms from the free abelian presheaf on `X` to `P` are the sections of `P` over `X`,
naturally in `X`; the sections are lifted to the universe of the morphisms. -/
def freeYonedaHomIso (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free.{v}).op ⋙
        preadditiveYoneda.obj P ≅ P ⋙ AddCommGrpCat.uliftFunctor.{u} :=
  NatIso.ofComponents (fun X ↦ AddEquiv.toAddCommGrpIso
    { ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj.{v}).homEquiv _ _).trans
        (yonedaEquiv.trans Equiv.ulift.symm) with
      map_add' := fun _ _ ↦ rfl }) fun {X X'} g ↦ by
    ext f
    exact congrArg ULift.up <| (congrArg yonedaEquiv
      (Adjunction.homEquiv_naturality_left _ _ _)).trans (yonedaEquiv_naturality _ _).symm

/-- The component of the identification sends a morphism of presheaves to its value
at the generator corresponding to the identity. -/
@[simp]
lemma freeYonedaHomIso_hom_app (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (X : Cᵒᵖ) :
    P.freeYonedaHomIso.hom.app X = AddCommGrpCat.ofHom
      { toFun := fun (f : yoneda.obj X.unop ⋙ AddCommGrpCat.free.{v} ⟶ P) ↦
          ULift.up (f.app X (FreeAbelianGroup.of (𝟙 X.unop)))
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl } :=
  (rfl)

end CategoryTheory.Functor
