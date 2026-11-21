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
  `X ⨯ -` does (in particular when epimorphisms in `C` are stable under base change);
* `CategoryTheory.Over.isPullback_pullback_obj` and `CategoryTheory.Over.pullback_map_left_fst`:
  the pullback square defining `(Over.pullback f).obj A` and the first-projection equation for
  `(Over.pullback f).map k`;
* `CategoryTheory.Over.pullback_map_injective_of_fac_iso` and
  `CategoryTheory.Over.pullback_map_surjective_of_fac_iso`: injectivity and surjectivity of
  `(Over.pullback j).map` on morphisms over `X` follow from those of `(Over.pullback i).map`
  whenever `j = e.hom ≫ i` for an isomorphism `e`.
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

/-- The pullback square defining `(Over.pullback f).obj A`. -/
theorem isPullback_pullback_obj {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] (A : Over Y) :
    IsPullback (Limits.pullback.fst A.hom f) ((pullback f).obj A).hom A.hom f := by
  simpa only [pullback_obj_hom] using IsPullback.of_hasPullback A.hom f

/-- The pullback square defining `(Over.pullback f).obj (Over.mk g)`. -/
theorem isPullback_pullback_obj_mk {X Y Z : C} (f : X ⟶ Y) [HasPullbacksAlong f] (g : Z ⟶ Y) :
    IsPullback (Limits.pullback.fst g f) ((pullback f).obj (mk g)).hom g f := by
  simpa only [mk_hom] using isPullback_pullback_obj f (mk g)

/-- The first projection of `(Over.pullback f).map k` commutes with `k.left`. -/
@[reassoc]
theorem pullback_map_left_fst {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] {A B : Over Y}
    (k : A ⟶ B) :
    ((pullback f).map k).left ≫ Limits.pullback.fst B.hom f =
      Limits.pullback.fst A.hom f ≫ k.left :=
  (isPullback_pullback_map_left f k).w

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

section

attribute [local instance] hasPullback_of_right_iso

private lemma exists_equiv_pullback_map_of_fac_iso {X X₀ X₀' : C} {i : X₀' ⟶ X} {j : X₀ ⟶ X}
    [HasPullbacksAlong i] [HasPullbacksAlong j] (e : X₀ ≅ X₀') (he : e.hom ≫ i = j)
    (Y Z : Over X) :
    ∃ Φ : ((pullback i).obj Y ⟶ (pullback i).obj Z) ≃
        ((pullback j).obj Y ⟶ (pullback j).obj Z),
      ∀ g : Y ⟶ Z, (pullback j).map g = Φ ((pullback i).map g) := by
  subst he
  have : (pullback e.hom).IsEquivalence :=
    (mapPullbackAdj e.hom).isEquivalence_right_of_isEquivalence_left
  let hiso : pullback (e.hom ≫ i) ≅ pullback i ⋙ pullback e.hom :=
    pullbackComp e.hom i
  refine ⟨(Functor.FullyFaithful.ofFullyFaithful (pullback e.hom)).homEquiv.trans
    (Iso.homCongr (hiso.app Y).symm (hiso.app Z).symm), fun g ↦ ?_⟩
  simp only [Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply, Iso.homCongr_apply,
    Iso.symm_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  have hnat := hiso.hom.naturality g
  simp only [Functor.comp_map] at hnat
  rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- Pulling back morphisms in `Over X` along `j = e.hom ≫ i` (for an isomorphism `e`) is injective
if pulling back along `i` is injective. -/
theorem pullback_map_injective_of_fac_iso {X X₀ X₀' : C} {i : X₀' ⟶ X} {j : X₀ ⟶ X}
    [HasPullbacksAlong i] [HasPullbacksAlong j] (e : X₀ ≅ X₀') (he : e.hom ≫ i = j)
    {Y Z : Over X}
    (hi : Function.Injective (fun g : Y ⟶ Z ↦ (pullback i).map g)) :
    Function.Injective (fun g : Y ⟶ Z ↦ (pullback j).map g) := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_pullback_map_of_fac_iso e he Y Z
  intro g₁ g₂ h
  apply hi
  apply Φ.injective
  rwa [← hΦ g₁, ← hΦ g₂]

/-- Pulling back morphisms in `Over X` along `j = e.hom ≫ i` (for an isomorphism `e`) is surjective
if pulling back along `i` is surjective. -/
theorem pullback_map_surjective_of_fac_iso {X X₀ X₀' : C} {i : X₀' ⟶ X} {j : X₀ ⟶ X}
    [HasPullbacksAlong i] [HasPullbacksAlong j] (e : X₀ ≅ X₀') (he : e.hom ≫ i = j)
    {Y Z : Over X}
    (hi : Function.Surjective (fun g : Y ⟶ Z ↦ (pullback i).map g)) :
    Function.Surjective (fun g : Y ⟶ Z ↦ (pullback j).map g) := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_pullback_map_of_fac_iso e he Y Z
  intro g₀
  obtain ⟨g, hg⟩ := hi (Φ.symm g₀)
  dsimp only at hg
  exact ⟨g, (hΦ g).trans (by rw [hg, Equiv.apply_symm_apply])⟩

end

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
