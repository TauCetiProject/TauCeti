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
equalities `f ≫ 𝟙 Y = f` and `f ≫ g ≫ h = (f ≫ g) ≫ h`, and provides general comparison
isomorphisms for `Over.pullback` along equal composites and commutative squares:

* `CategoryTheory.Over.pullbackComp_id_inv_app_comp_eqToHom`: `pullbackComp f (𝟙 Y)` is the base
  change along `f` of `pullbackId`;
* `CategoryTheory.Over.pullbackComp_comp_inv_app_comp_eqToHom`: the two identifications of base
  change along `f ≫ g ≫ h` with the composite of the three base changes agree;
* `CategoryTheory.Over.pullbackCompIso`: canonical natural isomorphism
  `Over.pullback g ⋙ Over.pullback f ≅ Over.pullback h` for `f ≫ g = h`;
* `CategoryTheory.Over.pullback_hom_ext`: morphisms into `(Over.pullback f).obj Y` are
  determined by their composition with `pullback.fst Y.hom f`;
* `CategoryTheory.Over.conjPullback`: conjugation of morphisms between pullbacks along `f ≫ g = h`;
* `CategoryTheory.Over.pullbackSquareIso`: canonical natural isomorphism between the two ways of
  pulling back around a commutative square `i₁ ≫ j₁ = i₂ ≫ j₂`.
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

section PullbackIso

variable [HasPullbacks C]

/-- Canonical natural isomorphism between pulling back along `g` then `f` and pulling back along
`h`, given `w : f ≫ g = h`. -/
noncomputable def pullbackCompIso {A B D : C} {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D} (w : f ≫ g = h) :
    Over.pullback g ⋙ Over.pullback f ≅ Over.pullback h :=
  (Over.pullbackComp f g).symm ≪≫
    NatIso.ofComponents (fun X ↦ Over.isoMk (pullback.congrHom rfl w) (by simp))
      (fun _ ↦ by ext1; apply pullback.hom_ext <;> simp)

/-- The forward map of `pullbackCompIso` commutes with the first projections to `X`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIso_hom_app_left_fst {A B D : C} {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D}
    (w : f ≫ g = h) (X : Over D) :
    ((pullbackCompIso w).hom.app X).left ≫ pullback.fst X.hom h =
      pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g := by
  simp [pullbackCompIso, Over.pullbackComp]

/-- The forward map of `pullbackCompIso` commutes with the base projections. -/
@[reassoc (attr := simp)]
theorem pullbackCompIso_hom_app_left_snd {A B D : C} {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D}
    (w : f ≫ g = h) (X : Over D) :
    ((pullbackCompIso w).hom.app X).left ≫ pullback.snd X.hom h =
      pullback.snd (pullback.snd X.hom g) f :=
  Over.w ((pullbackCompIso w).hom.app X)

/-- The inverse map of `pullbackCompIso` commutes with the double first projections to `X`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIso_inv_app_left_fst_fst {A B D : C} {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D}
    (w : f ≫ g = h) (X : Over D) :
    ((pullbackCompIso w).inv.app X).left ≫
        pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g =
      pullback.fst X.hom h := by
  simp [pullbackCompIso, Over.pullbackComp]

/-- Composing the inverse map of `pullbackCompIso` with the projection to `B` agrees with
pulling back along `h` followed by `f`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIso_inv_app_left_fst_snd {A B D : C} {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D}
    (w : f ≫ g = h) (X : Over D) :
    ((pullbackCompIso w).inv.app X).left ≫
        pullback.fst (pullback.snd X.hom g) f ≫ pullback.snd X.hom g =
      pullback.snd X.hom h ≫ f := by
  simp [pullbackCompIso, Over.pullbackComp]

/-- The inverse map of `pullbackCompIso` commutes with the base projections. -/
@[reassoc (attr := simp)]
theorem pullbackCompIso_inv_app_left_snd {A B D : C} {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D}
    (w : f ≫ g = h) (X : Over D) :
    ((pullbackCompIso w).inv.app X).left ≫ pullback.snd (pullback.snd X.hom g) f =
      pullback.snd X.hom h :=
  Over.w ((pullbackCompIso w).inv.app X)

/-- Morphisms into `(Over.pullback f).obj Y` are determined by their composition with
`pullback.fst Y.hom f`. -/
theorem pullback_hom_ext {B T : C} {f : T ⟶ B} {Z : Over T} {Y : Over B}
    {φ ψ : Z ⟶ (Over.pullback f).obj Y}
    (h : φ.left ≫ pullback.fst Y.hom f = ψ.left ≫ pullback.fst Y.hom f) : φ = ψ := by
  ext1; exact pullback.hom_ext h ((Over.w φ).trans (Over.w ψ).symm)

/-- Transport a morphism between pullbacks along `g` to a morphism between pullbacks along `h`,
via `pullbackCompIso w` for `w : f ≫ g = h`. -/
noncomputable def conjPullback {A B D : C} {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D} (w : f ≫ g = h)
    {X Y : Over D} (φ : (Over.pullback g).obj X ⟶ (Over.pullback g).obj Y) :
    (Over.pullback h).obj X ⟶ (Over.pullback h).obj Y :=
  (pullbackCompIso w).inv.app X ≫ (Over.pullback f).map φ ≫ (pullbackCompIso w).hom.app Y

/-- Unfolding lemma for `conjPullback`. -/
theorem conjPullback_eq {A B D : C} {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D} (w : f ≫ g = h)
    {X Y : Over D} (φ : (Over.pullback g).obj X ⟶ (Over.pullback g).obj Y) :
    conjPullback w φ =
      (pullbackCompIso w).inv.app X ≫ (Over.pullback f).map φ ≫ (pullbackCompIso w).hom.app Y := by
  unfold conjPullback
  rfl

/-- Conjugation by `pullbackCompIso w` cancels on the left and right, so equal conjugates imply
equal pullbacks along `f`. -/
theorem conjPullback_injective {A B D : C} {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D}
    (w : f ≫ g = h) {X Y : Over D}
    {φ ψ : (Over.pullback g).obj X ⟶ (Over.pullback g).obj Y}
    (H : conjPullback w φ = conjPullback w ψ) :
    (Over.pullback f).map φ = (Over.pullback f).map ψ := by
  rw [conjPullback_eq, conjPullback_eq] at H
  rwa [← cancel_epi ((pullbackCompIso w).inv.app X),
    ← cancel_mono ((pullbackCompIso w).hom.app Y), Category.assoc, Category.assoc]

/-- `conjPullback` preserves composition. -/
theorem conjPullback_comp {A B D : C} {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D} (w : f ≫ g = h)
    {X Y Z : Over D}
    (a : (Over.pullback g).obj X ⟶ (Over.pullback g).obj Y)
    (b : (Over.pullback g).obj Y ⟶ (Over.pullback g).obj Z) :
    conjPullback w a ≫ conjPullback w b = conjPullback w (a ≫ b) := by
  simp only [conjPullback_eq, Category.assoc, Functor.map_comp]
  rw [← Category.assoc ((pullbackCompIso w).hom.app Y), Iso.hom_inv_id_app, Category.id_comp]

/-- `conjPullback` preserves identities. -/
@[simp]
theorem conjPullback_id {A B D : C} {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D} (w : f ≫ g = h)
    (X : Over D) :
    conjPullback w (𝟙 ((Over.pullback g).obj X)) = 𝟙 ((Over.pullback h).obj X) := by
  simp [conjPullback_eq]

/-- Iterated `conjPullback` satisfies associativity up to the corresponding morphism equalities. -/
theorem conjPullback_conjPullback {A B D E : C}
    {f : A ⟶ B} {g : B ⟶ D} {h : D ⟶ E} {fg : A ⟶ D} {gh : B ⟶ E} {fgh : A ⟶ E}
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh₁ : f ≫ gh = fgh) (hfgh₂ : fg ≫ h = fgh)
    {X Y : Over E} (ψ : (Over.pullback h).obj X ⟶ (Over.pullback h).obj Y) :
    conjPullback hfgh₁ (conjPullback hgh ψ) = conjPullback hfgh₂ ψ := by
  apply pullback_hom_ext
  simp only [conjPullback_eq, Over.comp_left, Category.assoc, pullbackCompIso_hom_app_left_fst,
    Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst_assoc]
  have hkey : ((pullbackCompIso hfgh₁).inv.app X).left ≫
        pullback.fst (pullback.snd X.hom gh) f ≫
        ((pullbackCompIso hgh).inv.app X).left ≫
        pullback.fst (pullback.snd X.hom h) g =
      ((pullbackCompIso hfgh₂).inv.app X).left ≫
        pullback.fst (pullback.snd X.hom h) fg := by
    apply pullback.hom_ext <;> simp [← hfg]
  rw [reassoc_of% hkey]

/-- Conjugating a pullback-conjugated morphism along `hfg` cancels the intermediate
`pullbackCompIso hgh` conjugation. -/
theorem conjPullback_conjIso {A B D E : C}
    {f : A ⟶ B} {g : B ⟶ D} {h : D ⟶ E} {fg : A ⟶ D} {gh : B ⟶ E} {fgh : A ⟶ E}
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh₁ : f ≫ gh = fgh) (hfgh₂ : fg ≫ h = fgh)
    {X Y : Over E} (φ : (Over.pullback gh).obj X ⟶ (Over.pullback gh).obj Y) :
    (pullbackCompIso hfgh₂).inv.app X ≫
        conjPullback hfg ((pullbackCompIso hgh).hom.app X ≫ φ ≫
          (pullbackCompIso hgh).inv.app Y) ≫
        (pullbackCompIso hfgh₂).hom.app Y =
      conjPullback hfgh₁ φ := by
  apply pullback_hom_ext
  have hfg_hom := pullbackCompIso_hom_app_left_fst hfg ((Over.pullback h).obj Y)
  have hfg_inv := pullbackCompIso_inv_app_left_fst_fst hfg ((Over.pullback h).obj X)
  have hfg_inv_snd := pullbackCompIso_inv_app_left_snd hfg ((Over.pullback h).obj X)
  dsimp only [Over.pullback_obj_hom] at hfg_hom hfg_inv hfg_inv_snd
  simp only [conjPullback_eq, Functor.map_comp, Over.comp_left, Category.assoc,
    pullbackCompIso_hom_app_left_fst, reassoc_of% hfg_hom, Over.pullback_map_left,
    Over.pullback_obj_hom, pullback.lift_fst_assoc, pullbackCompIso_inv_app_left_fst_fst]
  have hkey : ((pullbackCompIso hfgh₂).inv.app X).left ≫
        ((pullbackCompIso hfg).inv.app ((Over.pullback h).obj X)).left ≫
        pullback.fst (pullback.snd (pullback.snd X.hom h) g) f ≫
        ((pullbackCompIso hgh).hom.app X).left =
      ((pullbackCompIso hfgh₁).inv.app X).left ≫ pullback.fst (pullback.snd X.hom gh) f := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackCompIso_hom_app_left_fst, reassoc_of% hfg_inv,
        pullbackCompIso_inv_app_left_fst_fst]
    · simp only [Category.assoc, pullbackCompIso_hom_app_left_snd, pullback.condition,
        reassoc_of% hfg_inv_snd, pullbackCompIso_inv_app_left_snd_assoc]
  rw [reassoc_of% hkey]

/-- Canonical natural isomorphism between the two ways of pulling back around a commutative square
`i₁ ≫ j₁ = i₂ ≫ j₂`. -/
noncomputable def pullbackSquareIso {B U₁ U₂ V : C} {i₁ : V ⟶ U₁} {i₂ : V ⟶ U₂}
    {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B} (w : i₁ ≫ j₁ = i₂ ≫ j₂) :
    Over.pullback j₁ ⋙ Over.pullback i₁ ≅ Over.pullback j₂ ⋙ Over.pullback i₂ :=
  pullbackCompIso w ≪≫ (pullbackCompIso (rfl : i₂ ≫ j₂ = i₂ ≫ j₂)).symm

/-- The forward map of `pullbackSquareIso` commutes with the double first projections to `Y`. -/
@[reassoc (attr := simp)]
theorem pullbackSquareIso_hom_app_left_fst_fst {B U₁ U₂ V : C} {i₁ : V ⟶ U₁} {i₂ : V ⟶ U₂}
    {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B} (w : i₁ ≫ j₁ = i₂ ≫ j₂) (Y : Over B) :
    ((pullbackSquareIso w).hom.app Y).left ≫
        pullback.fst (pullback.snd Y.hom j₂) i₂ ≫ pullback.fst Y.hom j₂ =
      pullback.fst (pullback.snd Y.hom j₁) i₁ ≫ pullback.fst Y.hom j₁ := by
  simp [pullbackSquareIso]

/-- The forward map of `pullbackSquareIso` commutes with the base projections. -/
@[reassoc (attr := simp)]
theorem pullbackSquareIso_hom_app_left_snd {B U₁ U₂ V : C} {i₁ : V ⟶ U₁} {i₂ : V ⟶ U₂}
    {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B} (w : i₁ ≫ j₁ = i₂ ≫ j₂) (Y : Over B) :
    ((pullbackSquareIso w).hom.app Y).left ≫ pullback.snd (pullback.snd Y.hom j₂) i₂ =
      pullback.snd (pullback.snd Y.hom j₁) i₁ :=
  Over.w ((pullbackSquareIso w).hom.app Y)

/-- The inverse map of `pullbackSquareIso` commutes with the double first projections to `Y`. -/
@[reassoc (attr := simp)]
theorem pullbackSquareIso_inv_app_left_fst_fst {B U₁ U₂ V : C} {i₁ : V ⟶ U₁} {i₂ : V ⟶ U₂}
    {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B} (w : i₁ ≫ j₁ = i₂ ≫ j₂) (Y : Over B) :
    ((pullbackSquareIso w).inv.app Y).left ≫
        pullback.fst (pullback.snd Y.hom j₁) i₁ ≫ pullback.fst Y.hom j₁ =
      pullback.fst (pullback.snd Y.hom j₂) i₂ ≫ pullback.fst Y.hom j₂ := by
  simp [pullbackSquareIso]

/-- The inverse map of `pullbackSquareIso` commutes with the base projections. -/
@[reassoc (attr := simp)]
theorem pullbackSquareIso_inv_app_left_snd {B U₁ U₂ V : C} {i₁ : V ⟶ U₁} {i₂ : V ⟶ U₂}
    {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B} (w : i₁ ≫ j₁ = i₂ ≫ j₂) (Y : Over B) :
    ((pullbackSquareIso w).inv.app Y).left ≫ pullback.snd (pullback.snd Y.hom j₁) i₁ =
      pullback.snd (pullback.snd Y.hom j₂) i₂ :=
  Over.w ((pullbackSquareIso w).inv.app Y)

/-- Express `(pullbackSquareIso w).hom.app X` through `pullbackCompIso` via any common composite
`h : V ⟶ B`. -/
theorem pullbackSquareIso_hom_app {B U₁ U₂ V : C} {i₁ : V ⟶ U₁} {i₂ : V ⟶ U₂}
    {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B} {h : V ⟶ B}
    (w₁ : i₁ ≫ j₁ = h) (w₂ : i₂ ≫ j₂ = h) (w : i₁ ≫ j₁ = i₂ ≫ j₂) (X : Over B) :
    (pullbackSquareIso w).hom.app X =
      (pullbackCompIso w₁).hom.app X ≫ (pullbackCompIso w₂).inv.app X := by
  ext1; apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp
    · simp only [Over.comp_left, Over.pullback_obj_hom, Category.assoc,
        pullbackSquareIso_hom_app_left_snd_assoc, pullback.condition,
        pullbackCompIso_inv_app_left_snd_assoc, pullbackCompIso_hom_app_left_snd_assoc]
  · simp

/-- Compatibility of two morphisms with `pullbackSquareIso` is equivalent to equality of their
conjugates along any common composite `h : V ⟶ B`. -/
theorem pullbackSquareIso_iff_conjPullback {B U₁ U₂ V : C} {i₁ : V ⟶ U₁} {i₂ : V ⟶ U₂}
    {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B} {h : V ⟶ B}
    (w₁ : i₁ ≫ j₁ = h) (w₂ : i₂ ≫ j₂ = h) (w : i₁ ≫ j₁ = i₂ ≫ j₂) {X Y : Over B}
    (φ₁ : (Over.pullback j₁).obj X ⟶ (Over.pullback j₁).obj Y)
    (φ₂ : (Over.pullback j₂).obj X ⟶ (Over.pullback j₂).obj Y) :
    (Over.pullback i₁).map φ₁ ≫ (pullbackSquareIso w).hom.app Y =
        (pullbackSquareIso w).hom.app X ≫ (Over.pullback i₂).map φ₂ ↔
      conjPullback w₁ φ₁ = conjPullback w₂ φ₂ := by
  rw [pullbackSquareIso_hom_app w₁ w₂ w X, pullbackSquareIso_hom_app w₁ w₂ w Y]
  constructor
  · intro H
    rw [← cancel_mono ((pullbackCompIso w₂).inv.app Y)]
    simp only [conjPullback_eq, Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id]
    rw [H, ← Category.assoc, Iso.inv_hom_id_app_assoc]
  · intro H
    rw [← cancel_epi ((pullbackCompIso w₁).inv.app X),
      ← cancel_mono ((pullbackCompIso w₂).hom.app Y)]
    simpa only [conjPullback_eq, Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
      Category.comp_id] using H

end PullbackIso

end Over

end CategoryTheory
