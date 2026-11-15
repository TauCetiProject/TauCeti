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
* `CategoryTheory.Over.pullbackCongr` and `CategoryTheory.Over.pullbackCompIsoOfEq`: natural
  isomorphisms of `Over.pullback` along equal base morphisms and along factorizations `f ≫ g = fg`,
  together with `Limits.pullback` projection lemmas.
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

/-- Pullback functors on `Over` categories along equal base morphisms are naturally isomorphic. -/
noncomputable def pullbackCongr {X Y : C} {f₁ f₂ : X ⟶ Y}
    [HasPullbacksAlong f₁] [HasPullbacksAlong f₂] (h : f₁ = f₂) :
    pullback f₁ ≅ pullback f₂ :=
  eqToIso (by subst h; rfl)

/-- Along `rfl`, `pullbackCongr` is the identity natural isomorphism. -/
@[simp]
theorem pullbackCongr_refl {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    pullbackCongr (rfl : f = f) = Iso.refl (pullback f) :=
  (rfl)

/-- `pullbackCongr` reverses along `Eq.symm`. -/
@[simp]
theorem pullbackCongr_symm {X Y : C} {f₁ f₂ : X ⟶ Y}
    [HasPullbacksAlong f₁] [HasPullbacksAlong f₂] (h : f₁ = f₂) :
    (pullbackCongr h).symm = pullbackCongr h.symm := by
  subst h; rfl

/-- The components of `(pullbackCongr h).hom` are `eqToHom` along `h`. -/
theorem pullbackCongr_hom_app {X Y : C} {f₁ f₂ : X ⟶ Y}
    [HasPullbacksAlong f₁] [HasPullbacksAlong f₂] (h : f₁ = f₂) (A : Over Y) :
    (pullbackCongr h).hom.app A = eqToHom (by subst h; rfl) := by
  subst h; rfl

/-- The components of `(pullbackCongr h).inv` are `eqToHom` along `h.symm`. -/
theorem pullbackCongr_inv_app {X Y : C} {f₁ f₂ : X ⟶ Y}
    [HasPullbacksAlong f₁] [HasPullbacksAlong f₂] (h : f₁ = f₂) (A : Over Y) :
    (pullbackCongr h).inv.app A = eqToHom (by subst h; rfl) := by
  subst h; rfl

/-- First projection of `(pullbackCongr h).hom.app A`. -/
@[reassoc (attr := simp)]
theorem pullbackCongr_hom_app_left_fst {X Y : C} {f₁ f₂ : X ⟶ Y}
    [HasPullbacksAlong f₁] [HasPullbacksAlong f₂] (h : f₁ = f₂) (A : Over Y) :
    ((pullbackCongr h).hom.app A).left ≫ Limits.pullback.fst A.hom f₂ =
      Limits.pullback.fst A.hom f₁ := by
  subst h; exact Category.id_comp _

/-- Second projection of `(pullbackCongr h).hom.app A`. -/
@[reassoc (attr := simp)]
theorem pullbackCongr_hom_app_left_snd {X Y : C} {f₁ f₂ : X ⟶ Y}
    [HasPullbacksAlong f₁] [HasPullbacksAlong f₂] (h : f₁ = f₂) (A : Over Y) :
    ((pullbackCongr h).hom.app A).left ≫ Limits.pullback.snd A.hom f₂ =
      Limits.pullback.snd A.hom f₁ := by
  subst h; exact Category.id_comp _

/-- First projection of `(pullbackCongr h).inv.app A`. -/
@[reassoc (attr := simp)]
theorem pullbackCongr_inv_app_left_fst {X Y : C} {f₁ f₂ : X ⟶ Y}
    [HasPullbacksAlong f₁] [HasPullbacksAlong f₂] (h : f₁ = f₂) (A : Over Y) :
    ((pullbackCongr h).inv.app A).left ≫ Limits.pullback.fst A.hom f₁ =
      Limits.pullback.fst A.hom f₂ := by
  subst h; exact Category.id_comp _

/-- Second projection of `(pullbackCongr h).inv.app A`. -/
@[reassoc (attr := simp)]
theorem pullbackCongr_inv_app_left_snd {X Y : C} {f₁ f₂ : X ⟶ Y}
    [HasPullbacksAlong f₁] [HasPullbacksAlong f₂] (h : f₁ = f₂) (A : Over Y) :
    ((pullbackCongr h).inv.app A).left ≫ Limits.pullback.snd A.hom f₁ =
      Limits.pullback.snd A.hom f₂ := by
  subst h; exact Category.id_comp _

/-- Natural isomorphism `pullback g ⋙ pullback f ≅ pullback fg` attached to an equality
`f ≫ g = fg`. -/
noncomputable def pullbackCompIsoOfEq {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (fg : W ⟶ Y)
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong fg] (h : f ≫ g = fg) :
    pullback g ⋙ pullback f ≅ pullback fg :=
  (pullbackComp f g).symm ≪≫ pullbackCongr h

/-- The components of `(pullbackCompIsoOfEq f g fg h).hom` are `(pullbackComp f g).inv` followed by
`(pullbackCongr h).hom`. -/
@[simp]
theorem pullbackCompIsoOfEq_hom_app {W X Y : C} {f : W ⟶ X} {g : X ⟶ Y} {fg : W ⟶ Y}
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong fg]
    (h : f ≫ g = fg) (A : Over Y) :
    (pullbackCompIsoOfEq f g fg h).hom.app A =
      (pullbackComp f g).inv.app A ≫ (pullbackCongr h).hom.app A :=
  (rfl)

/-- The components of `(pullbackCompIsoOfEq f g fg h).inv` are `(pullbackCongr h).inv` followed by
`(pullbackComp f g).hom`. -/
@[simp]
theorem pullbackCompIsoOfEq_inv_app {W X Y : C} {f : W ⟶ X} {g : X ⟶ Y} {fg : W ⟶ Y}
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong fg]
    (h : f ≫ g = fg) (A : Over Y) :
    (pullbackCompIsoOfEq f g fg h).inv.app A =
      (pullbackCongr h).inv.app A ≫ (pullbackComp f g).hom.app A :=
  (rfl)

/-- First projection of `(pullbackCompIsoOfEq f g fg h).hom.app A`. -/
@[reassoc]
theorem pullbackCompIsoOfEq_hom_app_left_fst {W X Y : C} {f : W ⟶ X} {g : X ⟶ Y} {fg : W ⟶ Y}
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong fg]
    (h : f ≫ g = fg) (A : Over Y) :
    ((pullbackCompIsoOfEq f g fg h).hom.app A).left ≫ Limits.pullback.fst A.hom fg =
      Limits.pullback.fst (Limits.pullback.snd A.hom g) f ≫ Limits.pullback.fst A.hom g := by
  subst h; simp [pullbackComp]

/-- Second projection of `(pullbackCompIsoOfEq f g fg h).hom.app A`. -/
@[reassoc]
theorem pullbackCompIsoOfEq_hom_app_left_snd {W X Y : C} {f : W ⟶ X} {g : X ⟶ Y} {fg : W ⟶ Y}
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong fg]
    (h : f ≫ g = fg) (A : Over Y) :
    ((pullbackCompIsoOfEq f g fg h).hom.app A).left ≫ Limits.pullback.snd A.hom fg =
      Limits.pullback.snd (Limits.pullback.snd A.hom g) f := by
  subst h; simp [pullbackComp]

/-- First projection of `(pullbackCompIsoOfEq f g fg h).inv.app A`. -/
@[reassoc]
theorem pullbackCompIsoOfEq_inv_app_left_fst {W X Y : C} {f : W ⟶ X} {g : X ⟶ Y} {fg : W ⟶ Y}
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong fg]
    (h : f ≫ g = fg) (A : Over Y) :
    ((pullbackCompIsoOfEq f g fg h).inv.app A).left ≫
        Limits.pullback.fst (Limits.pullback.snd A.hom g) f =
      Limits.pullback.map A.hom fg A.hom g (𝟙 _) f (𝟙 _) (by simp) (by simp [h]) := by
  subst h; apply Limits.pullback.hom_ext <;> simp [pullbackComp]

/-- Second projection of `(pullbackCompIsoOfEq f g fg h).inv.app A`. -/
@[reassoc]
theorem pullbackCompIsoOfEq_inv_app_left_snd {W X Y : C} {f : W ⟶ X} {g : X ⟶ Y} {fg : W ⟶ Y}
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong fg]
    (h : f ≫ g = fg) (A : Over Y) :
    ((pullbackCompIsoOfEq f g fg h).inv.app A).left ≫
        Limits.pullback.snd (Limits.pullback.snd A.hom g) f =
      Limits.pullback.snd A.hom fg := by
  subst h; simp [pullbackComp]

end Over

end CategoryTheory
