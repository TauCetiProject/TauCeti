/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Pullback
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Pullback

/-!
# Functoriality of the pullback of cohomology over objects

Let `pb : Sheaf J Ab ⥤ Sheaf K Ab` be an exact additive functor and
`c : ℤ[u(-)] ⟶ pb ℤ[-]` a comparison of free abelian sheaves along `u : C ⥤ D`, so that
`CategoryTheory.Sheaf.H'.pullback pb c G n ψ : Hⁿ(U, G) ⟶ Hⁿ(V, pb G)` is defined for
`ψ : V ⟶ u(U)`. This file proves that these maps compose, and that they are compatible with a
natural transformation between the exact functors:

* `CategoryTheory.Sheaf.H'.pullback_comp_pullback`: pulling back along `(pb₁, c₁)` and then along
  `(pb₂, c₂)` is pulling back along `pb₁ ⋙ pb₂` with the composite comparison;
* `CategoryTheory.Sheaf.H'.pullback_comp_map_app`: pulling back along `(pb, c)` followed by a
  natural transformation `τ : pb ⟶ pb'` applied to the coefficients is pulling back along
  `(pb', c ≫ τ)`.

For continuous functors `u : C ⥤ D` and `v : D ⥤ E`, the comparisons
`CategoryTheory.Functor.freeYonedaSheafToSheafPullback` of `u`, `v` and `u ⋙ v` are compatible
with the isomorphism `CategoryTheory.Functor.sheafPullbackComp` of sheaf pullbacks
(`CategoryTheory.Functor.freeYonedaSheafToSheafPullback_comp`). Together, pullback of
cohomology over objects along a composite of morphisms of sites is the composite of the pullbacks
(`CategoryTheory.Sheaf.H'.pullback_comp_pullback_sheafPullback`).
-/

public section

open CategoryTheory Abelian Limits Opposite

namespace CategoryTheory.Functor

open TauCeti.CategoryTheory

universe v u₁ u₂ u₃

variable {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u₂} [Category.{v} D] (K : GrothendieckTopology D)
  {E : Type u₃} [Category.{v} E] (L : GrothendieckTopology E)
  (u₁ : C ⥤ D) (u₂ : D ⥤ E) [u₁.IsContinuous J K] [u₂.IsContinuous K L]

noncomputable section

/-- The unit of `(u₁ ⋙ u₂)^* ⊣ (u₁ ⋙ u₂)_*` is the unit of `u₁^* ⊣ u₁_*`, followed by the unit of
`u₂^* ⊣ u₂_*` and the isomorphism `u₂^* u₁^* ≅ (u₁ ⋙ u₂)^*` of `sheafPullbackComp`. -/
lemma sheafAdjunctionContinuous_comp_unit_app (A : Type*) [Category* A]
    [(u₁.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(u₂.sheafPushforwardContinuous A K L).IsRightAdjoint] (G : Sheaf J A) :
    let := isContinuous_comp u₁ u₂ J K L
    have := isRightAdjoint_sheafPushforwardContinuous_comp u₁ u₂ A J K L
    ((u₁ ⋙ u₂).sheafAdjunctionContinuous A J L).unit.app G =
      (u₁.sheafAdjunctionContinuous A J K).unit.app G ≫
        (u₁.sheafPushforwardContinuous A J K).map
          ((u₂.sheafAdjunctionContinuous A K L).unit.app _ ≫
            (u₂.sheafPushforwardContinuous A K L).map
              ((sheafPullbackComp u₁ u₂ A J K L).hom.app G)) := by
  intro _ _
  have h := unit_conjugateEquiv ((u₁.sheafAdjunctionContinuous A J K).comp
    (u₂.sheafAdjunctionContinuous A K L)) ((u₁ ⋙ u₂).sheafAdjunctionContinuous A J L)
    (sheafPullbackComp u₁ u₂ A J K L).inv G
  rw [conjugateEquiv_sheafPullbackComp_inv, Adjunction.comp_unit_app] at h
  -- The isomorphism of pushforwards in `sheafPullbackComp` is the identity.
  have h' := congrArg (· ≫ ((u₁ ⋙ u₂).sheafPushforwardContinuous A J L).map
    ((sheafPullbackComp u₁ u₂ A J K L).hom.app G)) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id] at h'
  refine (Category.comp_id _).symm.trans (h'.symm.trans ?_)
  rw [Functor.map_comp]
  simp only [sheafPushforwardContinuousComp, Iso.refl_hom, NatTrans.id_app]
  exact congrArg (fun φ ↦ _ ≫ _ ≫ φ) (Category.id_comp _)

variable [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  [HasSheafify L AddCommGrpCat.{v}]
  [(u₁.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]
  [(u₂.sheafPushforwardContinuous AddCommGrpCat.{v} K L).IsRightAdjoint]

/-- The comparison `ℤ[u₂(u₁(U))] ⟶ (u₁ ⋙ u₂)^* ℤ[U]` of free abelian sheaves along `u₁ ⋙ u₂` is
the comparison along `u₂` followed by the image under `u₂^*` of the comparison along `u₁` and the
isomorphism `u₂^* u₁^* ≅ (u₁ ⋙ u₂)^*` of `sheafPullbackComp`. -/
lemma freeYonedaSheafToSheafPullback_comp :
    let := isContinuous_comp u₁ u₂ J K L
    have := isRightAdjoint_sheafPushforwardContinuous_comp u₁ u₂ AddCommGrpCat.{v} J K L
    (u₁.whiskerLeft (u₂.freeYonedaSheafToSheafPullback K L) ≫
        Functor.whiskerRight (u₁.freeYonedaSheafToSheafPullback J K)
          (u₂.sheafPullback AddCommGrpCat.{v} K L) ≫
        (freeYonedaSheafFunctor J).whiskerLeft
          (sheafPullbackComp u₁ u₂ AddCommGrpCat.{v} J K L).hom :
      (u₁ ⋙ u₂) ⋙ freeYonedaSheafFunctor L ⟶ _) =
      (u₁ ⋙ u₂).freeYonedaSheafToSheafPullback J L := by
  intro _ _
  ext U : 2
  apply (freeYonedaSheafSectionsEquiv L ((u₁ ⋙ u₂).obj U) _).injective
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [freeYonedaSheafSectionsEquiv_naturality_right,
    freeYonedaSheafSectionsEquiv_freeYonedaSheafToSheafPullback_app]
  erw [freeYonedaSheafSectionsEquiv_freeYonedaSheafToSheafPullback_app K L u₂ (u₁.obj U)]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  erw [ConcreteCategory.comp_apply]
  refine (congrArg (((sheafPullbackComp u₁ u₂ AddCommGrpCat.{v} J K L).hom.app _).hom.app _)
    (sheafAdjunctionContinuous_unit_app_hom_app_freeYonedaSheafSectionsEquiv K L u₂
      ((u₁.freeYonedaSheafToSheafPullback J K).app U)).symm).trans ?_
  erw [freeYonedaSheafSectionsEquiv_freeYonedaSheafToSheafPullback_app J K u₁ U]
  rw [sheafAdjunctionContinuous_comp_unit_app J K L u₁ u₂ AddCommGrpCat.{v}]
  rfl

end

end CategoryTheory.Functor

namespace CategoryTheory.Sheaf.H'

open TauCeti TauCeti.CategoryTheory

universe w v u₁ u₂ u₃

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v} D] {K : GrothendieckTopology D}
  {E : Type u₃} [Category.{v} E] {L : GrothendieckTopology E}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  [HasSheafify L AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w} (Sheaf K AddCommGrpCat.{v})]
  [HasExt.{w} (Sheaf L AddCommGrpCat.{v})]

noncomputable section

section General

variable (pb₁ : Sheaf J AddCommGrpCat.{v} ⥤ Sheaf K AddCommGrpCat.{v}) [pb₁.Additive]
  [PreservesFiniteLimits pb₁] [PreservesFiniteColimits pb₁]
  {u₁ : C ⥤ D} (c₁ : u₁ ⋙ freeYonedaSheafFunctor K ⟶ freeYonedaSheafFunctor J ⋙ pb₁)

/-- Pulling back along `(pb₁, c₁)` and then along `(pb₂, c₂)` is pulling back along `pb₁ ⋙ pb₂`
with the composite comparison `ℤ[u₂(u₁(-))] ⟶ pb₂ ℤ[u₁(-)] ⟶ pb₂ (pb₁ ℤ[-])`. -/
@[reassoc]
lemma pullback_comp_pullback
    (pb₂ : Sheaf K AddCommGrpCat.{v} ⥤ Sheaf L AddCommGrpCat.{v}) [pb₂.Additive]
    [PreservesFiniteLimits pb₂] [PreservesFiniteColimits pb₂]
    {u₂ : D ⥤ E} (c₂ : u₂ ⋙ freeYonedaSheafFunctor L ⟶ freeYonedaSheafFunctor K ⋙ pb₂)
    (G : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U : C} {V : D} {W : E} (ψ₁ : V ⟶ u₁.obj U)
    (ψ₂ : W ⟶ u₂.obj V) :
    pullback pb₁ c₁ G n ψ₁ ≫ pullback pb₂ c₂ (pb₁.obj G) n ψ₂ =
      pullback (pb₁ ⋙ pb₂) (u₁.whiskerLeft c₂ ≫ Functor.whiskerRight c₁ pb₂ :
        (u₁ ⋙ u₂) ⋙ freeYonedaSheafFunctor L ⟶ freeYonedaSheafFunctor J ⋙ pb₁ ⋙ pb₂)
        G n (ψ₂ ≫ u₂.map ψ₁) := by
  refine AddCommGrpCat.ext fun x ↦ ?_
  rw [ConcreteCategory.comp_apply, pullback_apply, pullback_apply, pullback_apply]
  revert x
  refine fun (x : Ext ((freeYonedaSheafFunctor J).obj U) G n) ↦ ?_
  rw [Ext.comp_mapExactFunctor, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  congr 2
  simp only [Functor.map_comp, Category.assoc, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  have h := c₂.naturality ψ₁
  dsimp only [Functor.comp_map] at h
  rw [reassoc_of% h]

/-- Pulling back along `(pb₁, c₁)` followed by a natural transformation `τ : pb₁ ⟶ pb₁'`
applied to the coefficient sheaf is pulling back along `(pb₁', c₁ ≫ τ)`. -/
@[reassoc]
lemma pullback_comp_map_app
    (pb₁' : Sheaf J AddCommGrpCat.{v} ⥤ Sheaf K AddCommGrpCat.{v}) [pb₁'.Additive]
    [PreservesFiniteLimits pb₁'] [PreservesFiniteColimits pb₁'] (τ : pb₁ ⟶ pb₁')
    (G : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U : C} {V : D} (ψ : V ⟶ u₁.obj U) :
    pullback pb₁ c₁ G n ψ ≫ ((Sheaf.cohomologyPresheafFunctor K n).map (τ.app G)).app (op V) =
      pullback pb₁' (c₁ ≫ (freeYonedaSheafFunctor J).whiskerLeft τ) G n ψ := by
  refine AddCommGrpCat.ext fun x ↦ ?_
  rw [ConcreteCategory.comp_apply, pullback_apply, pullback_apply]
  revert x
  refine fun (x : Ext ((freeYonedaSheafFunctor J).obj U) G n) ↦ ?_
  change ((Ext.mk₀ _).comp (x.mapExactFunctor pb₁) (zero_add n)).comp (Ext.mk₀ (τ.app G))
    (add_zero n) = _
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mapExactFunctor_comp_mk₀_natTransApp,
    ← Ext.comp_assoc_of_second_deg_zero]
  congr 1
  exact (Ext.mk₀_comp_mk₀ _ _).trans (congrArg Ext.mk₀ (Category.assoc _ _ _))

end General

section SheafPullback

variable (u₁ : C ⥤ D) (u₂ : D ⥤ E) [u₁.IsContinuous J K] [u₂.IsContinuous K L]
  [(u₁.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]
  [(u₂.sheafPushforwardContinuous AddCommGrpCat.{v} K L).IsRightAdjoint]
  [PreservesFiniteLimits (u₁.sheafPullback AddCommGrpCat.{v} J K)]
  [PreservesFiniteLimits (u₂.sheafPullback AddCommGrpCat.{v} K L)]

/-- Pullback of cohomology over objects along the morphisms of sites `u₁` and then `u₂`, followed
by the isomorphism `u₂^* u₁^* ≅ (u₁ ⋙ u₂)^*` on coefficients, is pullback along `u₁ ⋙ u₂`. -/
lemma pullback_comp_pullback_sheafPullback (G : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U : C}
    {V : D} {W : E} (ψ₁ : V ⟶ u₁.obj U) (ψ₂ : W ⟶ u₂.obj V) :
    let := Functor.isContinuous_comp u₁ u₂ J K L
    have := Functor.isRightAdjoint_sheafPushforwardContinuous_comp u₁ u₂ AddCommGrpCat.{v} J K L
    have := preservesFiniteLimits_of_natIso
      (Functor.sheafPullbackComp u₁ u₂ AddCommGrpCat.{v} J K L)
    pullback (u₁.sheafPullback AddCommGrpCat.{v} J K) (u₁.freeYonedaSheafToSheafPullback J K)
        G n ψ₁ ≫
      pullback (u₂.sheafPullback AddCommGrpCat.{v} K L) (u₂.freeYonedaSheafToSheafPullback K L)
        ((u₁.sheafPullback AddCommGrpCat.{v} J K).obj G) n ψ₂ ≫
      ((Sheaf.cohomologyPresheafFunctor L n).map
        ((Functor.sheafPullbackComp u₁ u₂ AddCommGrpCat.{v} J K L).hom.app G)).app (op W) =
    pullback ((u₁ ⋙ u₂).sheafPullback AddCommGrpCat.{v} J L)
      ((u₁ ⋙ u₂).freeYonedaSheafToSheafPullback J L) G n (ψ₂ ≫ u₂.map ψ₁) := by
  intro _ _ _
  rw [pullback_comp_pullback_assoc, pullback_comp_map_app, Category.assoc,
    Functor.freeYonedaSheafToSheafPullback_comp]

end SheafPullback

end

end CategoryTheory.Sheaf.H'
