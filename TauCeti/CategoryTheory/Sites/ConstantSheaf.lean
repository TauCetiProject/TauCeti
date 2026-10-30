/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.CategoryTheory.Limits.Final

/-!
# Pullback of constant sheaves

Let `u : C ⥤ D` be a continuous functor from a site `(C, J)` to a site `(D, K)`, whose sheaf
pushforward `u_* : Sheaf K A ⥤ Sheaf J A` has the left adjoint `u^* = u.sheafPullback A J K`.
For every `X : A` there is a canonical comparison `u^* (X_J) ⟶ X_K` between the pullback of the
constant sheaf on `(C, J)` and the constant sheaf on `(D, K)`: it is adjoint to the map of
presheaves `X ⟶ (X_K)(u -)` induced by sheafification.

When `u` is final, which holds for instance when `u` is representably flat
(`CategoryTheory.Functor.final_of_representablyFlat`), so in particular for a morphism of sites,
this comparison is an isomorphism: maps out of either side into a sheaf `F` on `(D, K)` are cones
with apex `X` over `F`, restricted along `u` in the first case.

## Main declarations

* `CategoryTheory.Functor.sheafPullbackConstantSheafHom`: the comparison `u^* (X_J) ⟶ X_K`.
* `CategoryTheory.Functor.sheafPullbackConstantSheafHom_naturality`: the comparison is natural
  in `X`.
* `CategoryTheory.Functor.sheafPullbackConstantSheafIso`: the comparison as an isomorphism, for
  `u` final.
* `CategoryTheory.Functor.whiskerLeft_toSheafify_comp_sheafPullbackConstantSheafIso_inv`: the
  inverse comparison `X_K ⟶ u^* (X_J)`, read on sections over objects `u(U)`, is the unit of the
  adjunction `u^* ⊣ u_*` on the constant section `X ⟶ X_J(U)`.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (u : C ⥤ D)
  (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [u.IsContinuous J K] [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

noncomputable section

/-- The canonical comparison `u^* (X_J) ⟶ X_K` from the pullback of the constant sheaf with value
`X` on `(C, J)` to the constant sheaf with value `X` on `(D, K)`, both written as
sheafifications of constant presheaves (Mathlib's `constantSheaf` is by definition this
sheafification). It is adjoint, for the composite of sheafification and `u^* ⊣ u_*`, to the map
of presheaves `X ⟶ (X_K)(u -)` given by the canonical map to the sheafification. -/
def sheafPullbackConstantSheafHom (X : A) :
    (u.sheafPullback A J K).obj ((presheafToSheaf J A).obj ((Functor.const Cᵒᵖ).obj X)) ⟶
      (presheafToSheaf K A).obj ((Functor.const Dᵒᵖ).obj X) :=
  (((sheafificationAdjunction J A).comp (u.sheafAdjunctionContinuous A J K)).homEquiv _ _).symm
    ((constCompWhiskeringLeftIso _ (C := A) u.op).inv.app X ≫
      ((whiskeringLeft _ _ A).obj u.op).map (toSheafify K ((Functor.const Dᵒᵖ).obj X)) ≫
      (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K).inv.app _)

/-- Maps out of `X_K` and out of `u^* (X_J)` into a sheaf `F` on `(D, K)` correspond to cones with
apex `X` over `F` and over `F(u -)` respectively; precomposition with
`sheafPullbackConstantSheafHom` is restriction of cones along `u`. -/
lemma homEquiv_sheafPullbackConstantSheafHom_comp (X : A) {F : Sheaf K A}
    (g : (presheafToSheaf K A).obj ((Functor.const Dᵒᵖ).obj X) ⟶ F) :
    ((sheafificationAdjunction J A).comp (u.sheafAdjunctionContinuous A J K)).homEquiv _ _
      (u.sheafPullbackConstantSheafHom A J K X ≫ g) =
      Functor.whiskerLeft u.op ((sheafificationAdjunction K A).homEquiv _ _ g) := by
  rw [sheafPullbackConstantSheafHom, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply]
  ext U
  rw [Adjunction.homEquiv_apply]
  simp only [const_obj_obj, comp_obj, ObjectProperty.ι_obj, whiskeringLeft_obj_obj,
    whiskeringLeft_obj_map, comp_map, ObjectProperty.ι_map, Category.assoc, NatTrans.comp_app,
    op_obj, constCompWhiskeringLeftIso_inv_app_app, whiskerLeft_app,
    sheafPushforwardContinuousCompSheafToPresheafIso_inv_app_app,
    sheafPushforwardContinuous_map_hom_app, Category.id_comp, sheafificationAdjunction_unit_app]
  -- The remaining identity is on the sections of the pushforward of the sheafification, whose
  -- type `simp` does not match against `Category.id_comp` syntactically.
  exact congrArg _ (Category.id_comp _)

/-- The comparison `u^* (X_J) ⟶ X_K` is natural in `X`. -/
@[reassoc (attr := simp)]
lemma sheafPullbackConstantSheafHom_naturality {X Y : A} (f : X ⟶ Y) :
    (u.sheafPullback A J K).map ((presheafToSheaf J A).map ((Functor.const Cᵒᵖ).map f)) ≫
      u.sheafPullbackConstantSheafHom A J K Y =
      u.sheafPullbackConstantSheafHom A J K X ≫
        (presheafToSheaf K A).map ((Functor.const Dᵒᵖ).map f) := by
  let adj := (sheafificationAdjunction J A).comp (u.sheafAdjunctionContinuous A J K)
  apply (adj.homEquiv _ _).injective
  refine (adj.homEquiv_naturality_left ((Functor.const Cᵒᵖ).map f) _).trans ?_
  rw [homEquiv_sheafPullbackConstantSheafHom_comp, sheafPullbackConstantSheafHom,
    Equiv.apply_symm_apply, ← Category.comp_id ((presheafToSheaf K A).map _),
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_id, sheafificationAdjunction_unit_app]
  ext U
  simp only [const_obj_obj, comp_obj, ObjectProperty.ι_obj, whiskeringLeft_obj_obj,
    whiskeringLeft_obj_map, NatTrans.comp_app, op_obj, constCompWhiskeringLeftIso_inv_app_app,
    whiskerLeft_app, sheafPushforwardContinuousCompSheafToPresheafIso_inv_app_app,
    Category.id_comp, const_map_app]
  -- The remaining identity is on the sections of the pushforward of the sheafification, whose
  -- type `simp` does not match against `Category.comp_id` syntactically.
  exact congrArg _ (Category.comp_id _)

instance [u.Final] (X : A) : IsIso (u.sheafPullbackConstantSheafHom A J K X) := by
  let adj := (sheafificationAdjunction J A).comp (u.sheafAdjunctionContinuous A J K)
  rw [isIso_iff_coyoneda_map_bijective]
  intro F
  have : (fun g => u.sheafPullbackConstantSheafHom A J K X ≫ g) =
      (adj.homEquiv _ _).symm ∘ Initial.constHomEquiv u.op F.obj X ∘
        (sheafificationAdjunction K A).homEquiv _ _ := by
    ext1 g
    exact (adj.homEquiv _ _).eq_symm_apply.2
      ((homEquiv_sheafPullbackConstantSheafHom_comp u A J K X g).trans
        (Initial.constHomEquiv_apply _ _ _ _).symm)
  rw [this]
  exact (adj.homEquiv _ _).symm.bijective.comp ((Initial.constHomEquiv u.op F.obj X).bijective.comp
    ((sheafificationAdjunction K A).homEquiv _ _).bijective)

/-- For `u` final, the pullback of the constant sheaf with value `X` on `(C, J)` is the constant
sheaf with value `X` on `(D, K)`, through `sheafPullbackConstantSheafHom`. -/
def sheafPullbackConstantSheafIso [u.Final] (X : A) :
    (u.sheafPullback A J K).obj ((constantSheaf J A).obj X) ≅ (constantSheaf K A).obj X :=
  -- `constantSheaf J A` is by definition `Functor.const Cᵒᵖ ⋙ presheafToSheaf J A`; elaborating
  -- `asIso` without the expected type lets the `IsIso` instance be found in the latter form.
  (asIso (u.sheafPullbackConstantSheafHom A J K X) :)

@[simp]
lemma sheafPullbackConstantSheafIso_hom [u.Final] (X : A) :
    (u.sheafPullbackConstantSheafIso A J K X).hom = u.sheafPullbackConstantSheafHom A J K X :=
  (rfl)

/-- For `u` final, the inverse comparison `X_K ⟶ u^* (X_J)` is natural in `X`. -/
@[reassoc (attr := simp)]
lemma sheafPullbackConstantSheafIso_inv_naturality [u.Final] {X Y : A} (f : X ⟶ Y) :
    (constantSheaf K A).map f ≫ (u.sheafPullbackConstantSheafIso A J K Y).inv =
      (u.sheafPullbackConstantSheafIso A J K X).inv ≫
        (u.sheafPullback A J K).map ((constantSheaf J A).map f) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (sheafPullbackConstantSheafHom_naturality u A J K f).symm

/-- The inverse comparison `X_K ⟶ u^* (X_J)`, restricted to the objects `u(U)`, is the unit of the
adjunction `u^* ⊣ u_*` on the constant sections: on sections over `u(U)` it sends the constant
section to the image of the constant section of `X_J` over `U`. -/
lemma whiskerLeft_toSheafify_comp_sheafPullbackConstantSheafIso_inv [u.Final] (X : A) :
    Functor.whiskerLeft u.op (toSheafify K ((Functor.const Dᵒᵖ).obj X) ≫
      (u.sheafPullbackConstantSheafIso A J K X).inv.hom) =
      toSheafify J ((Functor.const Cᵒᵖ).obj X) ≫
        ((u.sheafAdjunctionContinuous A J K).unit.app ((constantSheaf J A).obj X)).hom := by
  have := homEquiv_sheafPullbackConstantSheafHom_comp u A J K X
    (CategoryTheory.inv (u.sheafPullbackConstantSheafHom A J K X))
  rw [IsIso.hom_inv_id] at this
  simp only [Adjunction.homEquiv_apply, Functor.map_id, Adjunction.comp_unit_app] at this
  -- The identity left by `Functor.map_id` is on the sections of `u_* u^* X_J`, which `simp`
  -- does not match against `Category.comp_id` syntactically.
  exact ((Category.comp_id _).symm.trans this).symm

end

end CategoryTheory.Functor
