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
# Base change in over categories: coherence, commuting squares, faithfulness, and epimorphisms

Mathlib identifies base change `Over.pullback` along an identity with the identity functor
(`Over.pullbackId`) and base change along a composite with the composite of base changes
(`Over.pullbackComp`). This file records that these identifications are coherent, up to the
equalities `f ≫ 𝟙 Y = f`, `𝟙 X ≫ f = f` and `f ≫ g ≫ h = (f ≫ g) ≫ h`:

* `CategoryTheory.Over.pullbackComp_id_inv_app_comp_eqToHom`: `pullbackComp f (𝟙 Y)` is the base
  change along `f` of `pullbackId`;
* `CategoryTheory.Over.pullbackComp_id_left_hom_app_comp_pullbackId`: `pullbackComp (𝟙 X) f`
  followed by `pullbackId` is the identity of base change along `f`;
* `CategoryTheory.Over.pullbackComp_comp_inv_app_comp_eqToHom`: the two identifications of base
  change along `f ≫ g ≫ h` with the composite of the three base changes agree;
* `CategoryTheory.Over.pullback_iso_triangle`: for an isomorphism `e : X ≅ Y`, the unit and
  counit built from `pullbackId` and `pullbackComp` satisfy the triangle identity for
  `pullback e.hom` and `pullback e.inv`.

For a commuting square `i' ≫ g = t ≫ i`, the natural isomorphism
`CategoryTheory.Over.pullbackPullbackIsoOfComm` identifies base change along `g` and then along
`i'` with base change along `i` and then along `t`;
when `i` and `i'` are points, this says the fiber at `i'` of the base change along `g` is the base
change along `t` of the fiber at `i`.

It also establishes faithfulness and epimorphism preservation for the base-change functors
`Over.pullback f : Over Y ⥤ Over X` and `Over.star X : C ⥤ Over X`:

* `CategoryTheory.Over.preservesEpimorphisms_pullback`: when epimorphisms in `C` are stable under
  base change and `Over.forget Y` preserves epimorphisms, `Over.pullback f` preserves epimorphisms;
* `CategoryTheory.Over.faithful_star` and `CategoryTheory.Over.jointlyFaithful_star`: `Over.star X`
  is faithful when the second projections `X ⨯ Y ⟶ Y` are epimorphisms (and jointly faithful for a
  family `U` whose second projections are jointly epimorphic);
* `CategoryTheory.Over.preservesEpimorphisms_star`: `Over.star X` preserves epimorphisms whenever
  `X ⨯ -` does (in particular when epimorphisms in `C` are stable under base change).

For a monomorphism `g`, the unit of `Over.map g ⊣ Over.pullback g` is an isomorphism
(`CategoryTheory.Over.isIso_mapPullbackAdj_unit_app`).

Finally, `CategoryTheory.IsPullback.overPullbackCompMapIso` is the Beck–Chevalley isomorphism of a
pullback square `fst ≫ f = snd ≫ g`: `Over.pullback fst ⋙ Over.map snd ≅ Over.map f ⋙
Over.pullback g`.
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

/-- Base change along `f` followed by base change along `𝟙 X` is base change along `𝟙 X ≫ f`: the
composition isomorphism `pullbackComp (𝟙 X) f` followed by `pullbackId` is the identity, up to the
equality `𝟙 X ≫ f = f`. -/
@[reassoc]
theorem pullbackComp_id_left_hom_app_comp_pullbackId {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    (A : Over Y) :
    (pullbackComp (𝟙 X) f).hom.app A ≫ pullbackId.hom.app ((pullback f).obj A) =
      eqToHom (by simp) := by
  -- As above, the identity is checked on the two projections out of `A ×_Y X`.
  ext1
  apply pullback.hom_ext
  · simp [pullbackComp, pullbackId, eqToHom_comp_pullback_fst A.hom (Category.id_comp f)]
  · simp [pullbackComp, pullbackId, eqToHom_comp_pullback_snd A.hom (Category.id_comp f)]

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

section CommSquare

variable {S S' s s' : C} {g : S' ⟶ S} {i : s ⟶ S} {i' : s' ⟶ S'} {t : s' ⟶ s}
  [HasPullbacksAlong g] [HasPullbacksAlong i] [HasPullbacksAlong i'] [HasPullbacksAlong t]

/-- For a commuting square `i' ≫ g = t ≫ i`, base change along `g : S' ⟶ S` and then along
`i' : s' ⟶ S'` is naturally isomorphic to base change along `i : s ⟶ S` and then along
`t : s' ⟶ s`. When `i` and `i'` are points, this is the **fiber of a base change**: the fiber at
`i'` of the base change of `A` along `g` is the base change along `t` of the fiber of `A` at `i`. -/
noncomputable def pullbackPullbackIsoOfComm (h : i' ≫ g = t ≫ i) :
    pullback g ⋙ pullback i' ≅ pullback i ⋙ pullback t :=
  (pullbackComp i' g).symm ≪≫ eqToIso (by simp only [h]) ≪≫ pullbackComp t i

/-- `pullbackPullbackIsoOfComm` is `pullbackComp i' g` inverted, followed by `pullbackComp t i`,
up to the equality `i' ≫ g = t ≫ i`. -/
theorem pullbackPullbackIsoOfComm_hom_app (h : i' ≫ g = t ≫ i) (A : Over S) :
    (pullbackPullbackIsoOfComm h).hom.app A =
      (pullbackComp i' g).inv.app A ≫ eqToHom (by simp only [h]) ≫
        (pullbackComp t i).hom.app A := by
  simp [pullbackPullbackIsoOfComm, eqToHom_app]

/-- `pullbackPullbackIsoOfComm` commutes with the projections to `A`. -/
@[reassoc (attr := simp)]
theorem pullbackPullbackIsoOfComm_hom_app_left_fst (h : i' ≫ g = t ≫ i) (A : Over S) :
    ((pullbackPullbackIsoOfComm h).hom.app A).left ≫ pullback.fst (pullback.snd A.hom i) t ≫
        pullback.fst A.hom i =
      pullback.fst (pullback.snd A.hom g) i' ≫ pullback.fst A.hom g := by
  simp only [pullbackPullbackIsoOfComm_hom_app, comp_left, eqToHom_left, Category.assoc]
  have h₁ : ((pullbackComp t i).hom.app A).left ≫ pullback.fst (pullback.snd A.hom i) t ≫
      pullback.fst A.hom i = pullback.fst A.hom (t ≫ i) := by
    simp [pullbackComp]
  have h₂ : ((pullbackComp i' g).inv.app A).left ≫ pullback.fst A.hom (i' ≫ g) =
      pullback.fst (pullback.snd A.hom g) i' ≫ pullback.fst A.hom g := by
    simp [pullbackComp]
  rw [h₁, eqToHom_comp_pullback_fst A.hom h, h₂]

/-- `pullbackPullbackIsoOfComm` commutes with the projections to `s'`. -/
@[reassoc (attr := simp)]
theorem pullbackPullbackIsoOfComm_hom_app_left_snd (h : i' ≫ g = t ≫ i) (A : Over S) :
    ((pullbackPullbackIsoOfComm h).hom.app A).left ≫ pullback.snd (pullback.snd A.hom i) t =
      pullback.snd (pullback.snd A.hom g) i' :=
  Over.w ((pullbackPullbackIsoOfComm h).hom.app A)

end CommSquare

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

/-- For a monomorphism `g`, the unit `A ⟶ g^*(g_! A)` of `Over.map g ⊣ Over.pullback g` is an
isomorphism: the square with sides `𝟙 A`, `A ⟶ X`, `A ⟶ Y` and `g` is a pullback. -/
instance isIso_mapPullbackAdj_unit_app {X Y : C} (g : X ⟶ Y) [HasPullbacksAlong g] [Mono g]
    (A : Over X) : IsIso ((mapPullbackAdj g).unit.app A) := by
  have h : IsPullback (𝟙 A.left) A.hom (A.hom ≫ g) g :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have hl : ((mapPullbackAdj g).unit.app A).left = h.isoPullback.hom := by
    apply pullback.hom_ext <;> simp
  have : IsIso ((forget X).map ((mapPullbackAdj g).unit.app A)) := by
    rw [forget_map, hl]
    infer_instance
  exact isIso_of_reflects_iso _ (forget X)

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

namespace IsPullback

variable {C : Type u} [Category.{v} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
  {g : Y ⟶ Z} [HasPullbacksAlong fst] [HasPullbacksAlong g]

/-- The Beck–Chevalley isomorphism of a pullback square `fst ≫ f = snd ≫ g`: base change along
`fst` followed by composition with `snd` is composition with `f` followed by base change along
`g`. On an object `A ⟶ X` it identifies `A ×_X P`, regarded over `Y` through `snd`, with
`A ×_Z Y`. -/
noncomputable def overPullbackCompMapIso (sq : IsPullback fst snd f g) :
    Over.pullback fst ⋙ Over.map snd ≅ Over.map f ⋙ Over.pullback g :=
  NatIso.ofComponents
    (fun A ↦ Over.isoMk ((IsPullback.of_hasPullback A.hom fst).paste_vert sq).isoPullback
      (by simp))
    (fun u ↦ by ext1; apply pullback.hom_ext <;> simp)

@[reassoc (attr := simp)]
theorem overPullbackCompMapIso_hom_app_left_fst (sq : IsPullback fst snd f g) (A : Over X) :
    (sq.overPullbackCompMapIso.hom.app A).left ≫ pullback.fst (A.hom ≫ f) g =
      pullback.fst A.hom fst := by
  simp [overPullbackCompMapIso]

@[reassoc (attr := simp)]
theorem overPullbackCompMapIso_hom_app_left_snd (sq : IsPullback fst snd f g) (A : Over X) :
    (sq.overPullbackCompMapIso.hom.app A).left ≫ pullback.snd (A.hom ≫ f) g =
      pullback.snd A.hom fst ≫ snd := by
  simp [overPullbackCompMapIso]

end IsPullback

end CategoryTheory
