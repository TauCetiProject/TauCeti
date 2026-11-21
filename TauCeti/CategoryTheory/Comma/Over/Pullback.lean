/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import TauCeti.CategoryTheory.Comma.Over
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.EqToHom

/-!
# Base change in over categories: coherence, faithfulness, and epimorphism preservation

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
  together with `Limits.pullback` projection lemmas;
* `CategoryTheory.Over.pullback_map_left_of_eq_mk`: transports `((Over.pullback g).map φ).left`
  along identifications `Y₁ = Over.mk p₁` and `Y₂ = Over.mk p₂` to a `Limits.pullback.lift`;
* `CategoryTheory.Over.pullback_iso_triangle`: for an isomorphism `e : X ≅ Y`, the unit and
  counit built from `pullbackId` and `pullbackComp` satisfy the triangle identity for
  `pullback e.hom` and `pullback e.inv`.

It also establishes faithfulness and epimorphism preservation for the base-change functors
`Over.pullback f : Over Y ⥤ Over X` and `Over.star X : C ⥤ Over X`:

* `CategoryTheory.Over.preservesEpimorphisms_pullback`: when epimorphisms in `C` are stable under
  base change and `Over.forget Y` preserves epimorphisms, `Over.pullback f` preserves epimorphisms;
* `CategoryTheory.Over.faithful_star` and `CategoryTheory.Over.jointlyFaithful_star`: `Over.star X`
  is faithful when the second projections `X ⨯ Y ⟶ Y` are epimorphisms (and jointly faithful for a
  family `U` whose second projections are jointly epimorphic);
* `CategoryTheory.Over.preservesEpimorphisms_star`: `Over.star X` preserves epimorphisms whenever
  `X ⨯ -` does (in particular when epimorphisms in `C` are stable under base change).
-/

public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace Over

variable {C : Type u} [Category.{v} C]

section Coherence

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

/-- For an isomorphism `e : X ≅ Y`, the unit and counit built from `pullbackId` and `pullbackComp`
for `pullback e.hom` and `pullback e.inv` satisfy the triangle identity on every object `A` of
`Over Y`. -/
@[reassoc]
theorem pullback_iso_triangle {X Y : C} (e : X ≅ Y) (A : Over Y) :
    (pullback e.hom).map
        (pullbackId.inv.app A ≫ eqToHom (by simp) ≫ (pullbackComp e.inv e.hom).hom.app A) ≫
      (pullbackComp e.hom e.inv).inv.app ((pullback e.hom).obj A) ≫
        eqToHom (by simp) ≫ pullbackId.hom.app ((pullback e.hom).obj A) =
      𝟙 ((pullback e.hom).obj A) := by
  -- As above, the identity is checked on the two projections out of `A ×_Y X`.
  ext1
  apply pullback.hom_ext
  · simp [pullbackComp, pullbackId,
      eqToHom_comp_pullback_fst_assoc (pullback.snd A.hom e.hom) e.hom_inv_id,
      eqToHom_comp_pullback_fst A.hom e.inv_hom_id.symm]
  · exact (Over.w _).trans (Category.id_comp _).symm

end Coherence

section Congr

variable {X Y : C}

/-- Pullback functors on `Over` categories along equal base morphisms are naturally isomorphic. -/
noncomputable def pullbackCongr {f₁ f₂ : X ⟶ Y} [HasPullbacksAlong f₁] [HasPullbacksAlong f₂]
    (h : f₁ = f₂) : pullback f₁ ≅ pullback f₂ := eqToIso (by subst h; rfl)

/-- Along `rfl`, `pullbackCongr` is the identity natural isomorphism. -/
@[simp] theorem pullbackCongr_refl (f : X ⟶ Y) [HasPullbacksAlong f] :
    pullbackCongr (rfl : f = f) = Iso.refl (pullback f) := (rfl)

variable {f₁ f₂ : X ⟶ Y} [HasPullbacksAlong f₁] [HasPullbacksAlong f₂]

/-- `pullbackCongr` reverses along `Eq.symm`. -/
@[simp] theorem pullbackCongr_symm (h : f₁ = f₂) :
    (pullbackCongr h).symm = pullbackCongr h.symm := by subst h; rfl

/-- The components of `(pullbackCongr h).hom` are `eqToHom` along `h`. -/
theorem pullbackCongr_hom_app (h : f₁ = f₂) (A : Over Y) :
    (pullbackCongr h).hom.app A = eqToHom (by subst h; rfl) := by subst h; rfl

/-- The components of `(pullbackCongr h).inv` are `eqToHom` along `h.symm`. -/
theorem pullbackCongr_inv_app (h : f₁ = f₂) (A : Over Y) :
    (pullbackCongr h).inv.app A = eqToHom (by subst h; rfl) := by subst h; rfl

/-- First projection of `(pullbackCongr h).hom.app A`. -/
@[reassoc (attr := simp)] theorem pullbackCongr_hom_app_left_fst (h : f₁ = f₂) (A : Over Y) :
    ((pullbackCongr h).hom.app A).left ≫ Limits.pullback.fst A.hom f₂ =
      Limits.pullback.fst A.hom f₁ := by subst h; exact Category.id_comp _

/-- Second projection of `(pullbackCongr h).hom.app A`. -/
@[reassoc (attr := simp)] theorem pullbackCongr_hom_app_left_snd (h : f₁ = f₂) (A : Over Y) :
    ((pullbackCongr h).hom.app A).left ≫ Limits.pullback.snd A.hom f₂ =
      Limits.pullback.snd A.hom f₁ := by subst h; exact Category.id_comp _

/-- First projection of `(pullbackCongr h).inv.app A`. -/
@[reassoc (attr := simp)] theorem pullbackCongr_inv_app_left_fst (h : f₁ = f₂) (A : Over Y) :
    ((pullbackCongr h).inv.app A).left ≫ Limits.pullback.fst A.hom f₁ =
      Limits.pullback.fst A.hom f₂ := by subst h; exact Category.id_comp _

/-- Second projection of `(pullbackCongr h).inv.app A`. -/
@[reassoc (attr := simp)] theorem pullbackCongr_inv_app_left_snd (h : f₁ = f₂) (A : Over Y) :
    ((pullbackCongr h).inv.app A).left ≫ Limits.pullback.snd A.hom f₁ =
      Limits.pullback.snd A.hom f₂ := by subst h; exact Category.id_comp _

end Congr

/-- Natural isomorphism `pullback g ⋙ pullback f ≅ pullback fg` from `f ≫ g = fg`. -/
noncomputable def pullbackCompIsoOfEq {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (fg : W ⟶ Y)
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong fg] (h : f ≫ g = fg) :
    pullback g ⋙ pullback f ≅ pullback fg := (pullbackComp f g).symm ≪≫ pullbackCongr h

variable {W X Y : C} {f : W ⟶ X} {g : X ⟶ Y} {fg : W ⟶ Y}
  [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong fg]

/-- Forward component of `pullbackCompIsoOfEq` at `A`. -/
@[simp] theorem pullbackCompIsoOfEq_hom_app (h : f ≫ g = fg) (A : Over Y) :
    (pullbackCompIsoOfEq f g fg h).hom.app A =
      (pullbackComp f g).inv.app A ≫ (pullbackCongr h).hom.app A := (rfl)

/-- Inverse component of `pullbackCompIsoOfEq` at `A`. -/
@[simp] theorem pullbackCompIsoOfEq_inv_app (h : f ≫ g = fg) (A : Over Y) :
    (pullbackCompIsoOfEq f g fg h).inv.app A =
      (pullbackCongr h).inv.app A ≫ (pullbackComp f g).hom.app A := (rfl)

/-- First projection of `(pullbackCompIsoOfEq f g fg h).hom.app A`. -/
@[reassoc] theorem pullbackCompIsoOfEq_hom_app_left_fst (h : f ≫ g = fg) (A : Over Y) :
    ((pullbackCompIsoOfEq f g fg h).hom.app A).left ≫ Limits.pullback.fst A.hom fg =
      Limits.pullback.fst (Limits.pullback.snd A.hom g) f ≫ Limits.pullback.fst A.hom g := by
  subst h; simp [pullbackComp]

/-- Second projection of `(pullbackCompIsoOfEq f g fg h).hom.app A`. -/
@[reassoc] theorem pullbackCompIsoOfEq_hom_app_left_snd (h : f ≫ g = fg) (A : Over Y) :
    ((pullbackCompIsoOfEq f g fg h).hom.app A).left ≫ Limits.pullback.snd A.hom fg =
      Limits.pullback.snd (Limits.pullback.snd A.hom g) f := by subst h; simp [pullbackComp]

/-- First projection of `(pullbackCompIsoOfEq f g fg h).inv.app A`. -/
@[reassoc] theorem pullbackCompIsoOfEq_inv_app_left_fst (h : f ≫ g = fg) (A : Over Y) :
    ((pullbackCompIsoOfEq f g fg h).inv.app A).left ≫
      Limits.pullback.fst (Limits.pullback.snd A.hom g) f =
      Limits.pullback.map A.hom fg A.hom g (𝟙 _) f (𝟙 _) (by simp) (by simp [h]) := by
  subst h; apply Limits.pullback.hom_ext <;> simp [pullbackComp]

/-- Second projection of `(pullbackCompIsoOfEq f g fg h).inv.app A`. -/
@[reassoc] theorem pullbackCompIsoOfEq_inv_app_left_snd (h : f ≫ g = fg) (A : Over Y) :
    ((pullbackCompIsoOfEq f g fg h).inv.app A).left ≫
      Limits.pullback.snd (Limits.pullback.snd A.hom g) f = Limits.pullback.snd A.hom fg := by
  subst h; simp [pullbackComp]

/-- Transporting `((Over.pullback g).map φ).left` along identifications `Y₁ = Over.mk p₁` and
`Y₂ = Over.mk p₂` yields the canonical `Limits.pullback.lift` on the underlying pullbacks. -/
theorem pullback_map_left_of_eq_mk {S T : C} (g : T ⟶ S) [HasPullbacksAlong g]
    {Y₁ Y₂ : Over S} (φ : Y₁ ⟶ Y₂) {X₁ X₂ : C} {p₁ : X₁ ⟶ S} {p₂ : X₂ ⟶ S}
    (h₁ : Y₁ = Over.mk p₁) (h₂ : Y₂ = Over.mk p₂) :
    eqToHom (by subst h₁; rfl) ≫ ((pullback g).map φ).left ≫ eqToHom (by subst h₂; rfl) =
      Limits.pullback.lift (f := p₂) (g := g) (Limits.pullback.fst p₁ g ≫
        eqToHom (congrArg Over.left h₁.symm) ≫ φ.left ≫ eqToHom (congrArg Over.left h₂))
        (Limits.pullback.snd p₁ g) (by
          have hw := Over.w φ; subst h₁ h₂
          simp only [Over.mk_left, Over.mk_hom] at hw; simp [hw, Limits.pullback.condition]) := by
  subst h₁ h₂; simp

/-- Base change `Over.pullback f : Over Y ⥤ Over X` preserves epimorphisms whenever `Over.forget Y`
does and epimorphisms in `C` are stable under base change. -/
instance preservesEpimorphisms_pullback {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    [(forget Y).PreservesEpimorphisms]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange] :
    (pullback f).PreservesEpimorphisms where
  preserves k _ :=
    have : Epi k.left := (forget Y).map_epi k
    (forget X).epi_of_epi_map <|
      MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
        (isPullback_pullback_map_left f k).flip ‹_›

section HasBinaryProducts

variable [HasBinaryProducts C]

/-- `Over.star X : C ⥤ Over X` is faithful when every second projection `X ⨯ Y ⟶ Y` is an
epimorphism. -/
instance faithful_star (X : C) [∀ Y : C, Epi (prod.snd : X ⨯ Y ⟶ Y)] : (star X).Faithful := by
  have (Y : C) : Epi ((forgetAdjStar X).counit.app Y) := by
    rw [forgetAdjStar_counit_app]
    exact inferInstanceAs (Epi (prod.snd : X ⨯ Y ⟶ Y))
  exact (forgetAdjStar X).faithful_R_of_epi_counit_app

/-- A family of base-change functors `Over.star (U i) : C ⥤ Over (U i)` is jointly faithful when
the second projections `U i ⨯ Z ⟶ Z` are jointly epimorphic for every `Z : C`. -/
theorem jointlyFaithful_star {I : Type*} (U : I → C)
    (hU : ∀ {Z W : C} (a b : Z ⟶ W),
      (∀ i, (prod.snd : U i ⨯ Z ⟶ Z) ≫ a = prod.snd ≫ b) → a = b) :
    JointlyFaithful (fun i ↦ star (U i)) where
  map_injective {Z W a b} h := hU a b fun i ↦ by
    have hi := ((forgetAdjStar (U i)).counit.naturality a).symm.trans <|
      (congrArg (fun k ↦ (forget (U i)).map k ≫ (forgetAdjStar (U i)).counit.app W) (h i)).trans
        ((forgetAdjStar (U i)).counit.naturality b)
    rwa [Functor.id_map, Functor.id_map, forgetAdjStar_counit_app] at hi

/-- `Over.star X : C ⥤ Over X` preserves epimorphisms whenever `X ⨯ -` does (in particular when
epimorphisms in `C` are stable under base change). -/
instance preservesEpimorphisms_star (X : C) [(prod.functor.obj X).PreservesEpimorphisms] :
    (star X).PreservesEpimorphisms where
  preserves f _ := (forget X).epi_of_epi_map ((prod.functor.obj X).map_epi f)

end HasBinaryProducts

end Over

end CategoryTheory
