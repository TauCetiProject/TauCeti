/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.EqToHom

/-!
# Coherence of base change in over categories

Mathlib identifies base change `Over.pullback` along an identity with the identity functor
(`Over.pullbackId`) and base change along a composite with the composite of base changes
(`Over.pullbackComp`). This file records that these identifications are coherent, up to the
equalities `f ≫ 𝟙 Y = f` and `f ≫ g ≫ h = (f ≫ g) ≫ h`:

* `CategoryTheory.Over.pullbackComp_id_inv_app_comp_eqToHom`: `pullbackComp f (𝟙 Y)` is the base
  change along `f` of `pullbackId`;
* `CategoryTheory.Over.pullbackComp_comp_inv_app_comp_eqToHom`: the two identifications of base
  change along `f ≫ g ≫ h` with the composite of the three base changes agree;
* `CategoryTheory.Over.pullbackCompIsoOfEq`: a commuting square `f₁ ≫ g₁ = f₂ ≫ g₂` induces a
  natural isomorphism `Over.pullback g₁ ⋙ Over.pullback f₁ ≅ Over.pullback g₂ ⋙ Over.pullback f₂`.
-/

public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace Over

variable {C : Type u} [Category.{v} C]

attribute [local instance] hasPullback_of_right_iso

/-- Base change along `f : X ⟶ Y` of the identification `pullbackId` of base change along the
identity is the composition isomorphism `pullbackComp f (𝟙 Y)`, up to the equality
`f ≫ 𝟙 Y = f`. -/
@[reassoc]
theorem pullbackComp_id_inv_app_comp_eqToHom {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    (A : Over Y) :
    (pullbackComp f (𝟙 Y)).inv.app A ≫ eqToHom (by simp) =
      (pullback f).map (pullbackId.hom.app A) := by
  -- The identity is checked on the two projections out of `A ×_Y X`.
  ext1
  apply pullback.hom_ext
  · simp [pullbackComp, pullbackId, eqToHom_comp_pullback_fst A.hom (Category.comp_id f)]
  · simp [pullbackComp, pullbackId, eqToHom_comp_pullback_snd A.hom (Category.comp_id f)]

/-- The two ways of identifying base change along `f ≫ g ≫ h` with the composite of the base
changes along `h`, `g` and `f` agree, up to the equality `f ≫ g ≫ h = (f ≫ g) ≫ h`. -/
@[reassoc]
theorem pullbackComp_comp_inv_app_comp_eqToHom {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong h] (A : Over Z) :
    (pullbackComp f (g ≫ h)).inv.app A ≫ eqToHom (by simp) =
      (pullback f).map ((pullbackComp g h).hom.app A) ≫
        (pullbackComp f g).inv.app ((pullback h).obj A) ≫ (pullbackComp (f ≫ g) h).inv.app A := by
  -- As above, the identity is checked on the two projections out of `A ×_Z W`.
  ext1
  apply pullback.hom_ext
  · simp [pullbackComp, eqToHom_comp_pullback_fst A.hom (Category.assoc f g h).symm]
  · simp [pullbackComp, eqToHom_comp_pullback_snd A.hom (Category.assoc f g h).symm]

/-- A commuting square `f₁ ≫ g₁ = f₂ ≫ g₂` induces a natural isomorphism between the composite
base-change functors `Over.pullback g₁ ⋙ Over.pullback f₁` and
`Over.pullback g₂ ⋙ Over.pullback f₂`. -/
noncomputable def pullbackCompIsoOfEq {W X Y Z : C} {f₁ : W ⟶ X} {g₁ : X ⟶ Z}
    {f₂ : W ⟶ Y} {g₂ : Y ⟶ Z} [HasPullbacksAlong f₁] [HasPullbacksAlong g₁]
    [HasPullbacksAlong f₂] [HasPullbacksAlong g₂] (h : f₁ ≫ g₁ = f₂ ≫ g₂) :
    pullback g₁ ⋙ pullback f₁ ≅ pullback g₂ ⋙ pullback f₂ :=
  (pullbackComp f₁ g₁).symm ≪≫
    eqToIso (by
      have heq : ∀ (k₁ k₂ : W ⟶ Z) [i₁ : HasPullbacksAlong k₁] [i₂ : HasPullbacksAlong k₂],
          k₁ = k₂ → @pullback C _ W Z k₁ i₁ = @pullback C _ W Z k₂ i₂ := by
        rintro _ _ _ _ rfl
        rfl
      exact heq _ _ h) ≪≫
    pullbackComp f₂ g₂

/-- First-projection compatibility for the forward direction of `pullbackCompIsoOfEq`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIsoOfEq_hom_app_left_fst_fst {W X Y Z : C} {f₁ : W ⟶ X} {g₁ : X ⟶ Z}
    {f₂ : W ⟶ Y} {g₂ : Y ⟶ Z} [HasPullbacksAlong f₁] [HasPullbacksAlong g₁]
    [HasPullbacksAlong f₂] [HasPullbacksAlong g₂] (h : f₁ ≫ g₁ = f₂ ≫ g₂) (A : Over Z) :
    ((pullbackCompIsoOfEq h).hom.app A).left ≫
        Limits.pullback.fst (Limits.pullback.snd A.hom g₂) f₂ ≫
        Limits.pullback.fst A.hom g₂ =
      Limits.pullback.fst (Limits.pullback.snd A.hom g₁) f₁ ≫
        Limits.pullback.fst A.hom g₁ := by
  simp [pullbackCompIsoOfEq, pullbackComp, eqToHom_comp_pullback_fst A.hom h]

/-- Second-projection compatibility for the forward direction of `pullbackCompIsoOfEq`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIsoOfEq_hom_app_left_snd {W X Y Z : C} {f₁ : W ⟶ X} {g₁ : X ⟶ Z}
    {f₂ : W ⟶ Y} {g₂ : Y ⟶ Z} [HasPullbacksAlong f₁] [HasPullbacksAlong g₁]
    [HasPullbacksAlong f₂] [HasPullbacksAlong g₂] (h : f₁ ≫ g₁ = f₂ ≫ g₂) (A : Over Z) :
    ((pullbackCompIsoOfEq h).hom.app A).left ≫
        Limits.pullback.snd (Limits.pullback.snd A.hom g₂) f₂ =
      Limits.pullback.snd (Limits.pullback.snd A.hom g₁) f₁ :=
  Over.w ((pullbackCompIsoOfEq h).hom.app A)

/-- First-projection compatibility for the inverse direction of `pullbackCompIsoOfEq`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIsoOfEq_inv_app_left_fst_fst {W X Y Z : C} {f₁ : W ⟶ X} {g₁ : X ⟶ Z}
    {f₂ : W ⟶ Y} {g₂ : Y ⟶ Z} [HasPullbacksAlong f₁] [HasPullbacksAlong g₁]
    [HasPullbacksAlong f₂] [HasPullbacksAlong g₂] (h : f₁ ≫ g₁ = f₂ ≫ g₂) (A : Over Z) :
    ((pullbackCompIsoOfEq h).inv.app A).left ≫
        Limits.pullback.fst (Limits.pullback.snd A.hom g₁) f₁ ≫
        Limits.pullback.fst A.hom g₁ =
      Limits.pullback.fst (Limits.pullback.snd A.hom g₂) f₂ ≫
        Limits.pullback.fst A.hom g₂ := by
  simp [pullbackCompIsoOfEq, pullbackComp, eqToHom_comp_pullback_fst A.hom h.symm]

/-- Second-projection compatibility for the inverse direction of `pullbackCompIsoOfEq`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIsoOfEq_inv_app_left_snd {W X Y Z : C} {f₁ : W ⟶ X} {g₁ : X ⟶ Z}
    {f₂ : W ⟶ Y} {g₂ : Y ⟶ Z} [HasPullbacksAlong f₁] [HasPullbacksAlong g₁]
    [HasPullbacksAlong f₂] [HasPullbacksAlong g₂] (h : f₁ ≫ g₁ = f₂ ≫ g₂) (A : Over Z) :
    ((pullbackCompIsoOfEq h).inv.app A).left ≫
        Limits.pullback.snd (Limits.pullback.snd A.hom g₁) f₁ =
      Limits.pullback.snd (Limits.pullback.snd A.hom g₂) f₂ :=
  Over.w ((pullbackCompIsoOfEq h).inv.app A)

end Over

end CategoryTheory
