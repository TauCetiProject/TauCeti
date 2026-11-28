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

* `CategoryTheory.Over.pullbackComp_hom_app_left_fst_fst`,
  `CategoryTheory.Over.pullbackComp_hom_app_left_fst_snd`,
  `CategoryTheory.Over.pullbackComp_inv_app_left_fst`, and
  `CategoryTheory.Over.pullbackComp_inv_app_left_snd`: projection identities for `pullbackComp`;
* `CategoryTheory.Over.pullbackComp_id_inv_app_comp_eqToHom`: `pullbackComp f (𝟙 Y)` is the base
  change along `f` of `pullbackId`;
* `CategoryTheory.Over.pullbackComp_id_left_hom_app_comp_pullbackId`: `pullbackComp (𝟙 X) f`
  followed by `pullbackId` is the identity of base change along `f`;
* `CategoryTheory.Over.pullbackCompIsoOfEq_hom_app_eq`: the two identifications of base
  change along `f ≫ g ≫ h` with the composite of the three base changes agree;
* `CategoryTheory.Over.pullback_iso_triangle`: for an isomorphism `e : X ≅ Y`, the unit and
  counit built from `pullbackId` and `pullbackComp` satisfy the triangle identity for
  `pullback e.hom` and `pullback e.inv`.

For a commuting square `i' ≫ g = t ≫ i`, the natural isomorphism
`CategoryTheory.Over.pullbackPullbackIsoOfComm` identifies base change along `g` and then along
`i'` with base change along `i` and then along `t`;
when `i` and `i'` are points, this says the fiber at `i'` of the base change along `g` is the base
change along `t` of the fiber at `i`. For a commuting triangle `a ≫ b = d`, the natural isomorphism
`CategoryTheory.Over.pullbackCompIsoOfEq` identifies base change along `b` and then along `a` with
base change along `d`, coherently for three composable morphisms
(`CategoryTheory.Over.pullbackCompIsoOfEq_hom_app_eq`); in particular, morphisms which agree after
base change along `b` agree after base change along `d`
(`CategoryTheory.Over.pullback_map_eq_map_of_comp_eq`). For a cone `c` over a diagram `D`, the
predicate `CategoryTheory.Limits.Cone.LiftsAlong` says that a morphism between base changes to the
cone point is, up to these identifications, the base change of a morphism between base changes to a
member of `D`; lifts are stable under passage to later members
(`CategoryTheory.Limits.Cone.LiftsAlong.precomp`) and under composition
(`CategoryTheory.Limits.Cone.liftsAlong_comp`).

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

/-- Under `(Over.pullbackComp t s).hom`, the iterated first projection from `(A ×_X Y) ×_Y Z` to
`A` is the first projection from `A ×_X Z`. -/
@[reassoc (attr := simp)]
theorem pullbackComp_hom_app_left_fst_fst {X Y Z : C}
    (t : Z ⟶ Y) (s : Y ⟶ X) [HasPullbacksAlong t] [HasPullbacksAlong s] (A : Over X) :
    ((pullbackComp t s).hom.app A).left ≫
        pullback.fst (pullback.snd A.hom s) t ≫ pullback.fst A.hom s =
      pullback.fst A.hom (t ≫ s) := by
  simp [pullbackComp]

/-- Under `(Over.pullbackComp t s).hom`, the `Y`-coordinate of the first projection from
`(A ×_X Y) ×_Y Z` to `A ×_X Y` is the `Z`-coordinate of `A ×_X Z` mapped along `t`. -/
@[reassoc (attr := simp)]
theorem pullbackComp_hom_app_left_fst_snd {X Y Z : C}
    (t : Z ⟶ Y) (s : Y ⟶ X) [HasPullbacksAlong t] [HasPullbacksAlong s] (A : Over X) :
    ((pullbackComp t s).hom.app A).left ≫
        pullback.fst (pullback.snd A.hom s) t ≫ pullback.snd A.hom s =
      pullback.snd A.hom (t ≫ s) ≫ t := by
  simp [pullbackComp]

/-- Under `(Over.pullbackComp t s).inv`, the first projection from `A ×_X Z` to `A` is the
iterated first projection from `(A ×_X Y) ×_Y Z`. -/
@[reassoc (attr := simp)]
theorem pullbackComp_inv_app_left_fst {X Y Z : C}
    (t : Z ⟶ Y) (s : Y ⟶ X) [HasPullbacksAlong t] [HasPullbacksAlong s] (A : Over X) :
    ((pullbackComp t s).inv.app A).left ≫ pullback.fst A.hom (t ≫ s) =
      pullback.fst (pullback.snd A.hom s) t ≫ pullback.fst A.hom s := by
  simp [pullbackComp]

/-- Under `(Over.pullbackComp t s).inv`, the second projection from `A ×_X Z` to `Z` is the second
projection from `(A ×_X Y) ×_Y Z`. -/
@[reassoc (attr := simp)]
theorem pullbackComp_inv_app_left_snd {X Y Z : C}
    (t : Z ⟶ Y) (s : Y ⟶ X) [HasPullbacksAlong t] [HasPullbacksAlong s] (A : Over X) :
    ((pullbackComp t s).inv.app A).left ≫ pullback.snd A.hom (t ≫ s) =
      pullback.snd (pullback.snd A.hom s) t := by
  simp [pullbackComp]

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
  rw [pullbackComp_hom_app_left_fst_fst, eqToHom_comp_pullback_fst A.hom h,
    pullbackComp_inv_app_left_fst]

/-- `pullbackPullbackIsoOfComm` commutes with the projections to `s'`. -/
@[reassoc (attr := simp)]
theorem pullbackPullbackIsoOfComm_hom_app_left_snd (h : i' ≫ g = t ≫ i) (A : Over S) :
    ((pullbackPullbackIsoOfComm h).hom.app A).left ≫ pullback.snd (pullback.snd A.hom i) t =
      pullback.snd (pullback.snd A.hom g) i' :=
  Over.w ((pullbackPullbackIsoOfComm h).hom.app A)

end CommSquare

section Triangle

variable {X Y Z : C} {a : X ⟶ Y} {b : Y ⟶ Z} {d : X ⟶ Z} [HasPullbacksAlong a]
  [HasPullbacksAlong b] [HasPullbacksAlong d]

/-- For a commuting triangle `a ≫ b = d`, base change along `b` and then along `a` is naturally
isomorphic to base change along `d`. This is `pullbackComp a b`, inverted and transported along
the equality `a ≫ b = d`. -/
noncomputable def pullbackCompIsoOfEq (h : a ≫ b = d) : pullback b ⋙ pullback a ≅ pullback d :=
  (pullbackComp a b).symm ≪≫ eqToIso (by subst h; rfl)

/-- For a reflexive triangle, the comparison is the inverse of `pullbackComp`. -/
@[simp]
theorem pullbackCompIsoOfEq_rfl :
    pullbackCompIsoOfEq (a := a) (b := b) rfl = (pullbackComp a b).symm := by
  simp [pullbackCompIsoOfEq]

/-- The component of the triangle comparison is `pullbackComp` inverted, followed by transport
along the triangle equality. -/
theorem pullbackCompIsoOfEq_hom_app (h : a ≫ b = d) (A : Over Z) :
    (pullbackCompIsoOfEq h).hom.app A =
      (pullbackComp a b).inv.app A ≫ eqToHom (by subst h; rfl) := by
  simp [pullbackCompIsoOfEq, eqToHom_app]

/-- The inverse component of the triangle comparison is transport along the triangle equality,
followed by `pullbackComp`. -/
theorem pullbackCompIsoOfEq_inv_app (h : a ≫ b = d) (A : Over Z) :
    (pullbackCompIsoOfEq h).inv.app A =
      eqToHom (by subst h; rfl) ≫ (pullbackComp a b).hom.app A := by
  simp [pullbackCompIsoOfEq, eqToHom_app]

/-- `pullbackCompIsoOfEq` commutes with the projections to `A`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIsoOfEq_hom_app_left_fst (h : a ≫ b = d) (A : Over Z) :
    ((pullbackCompIsoOfEq h).hom.app A).left ≫ pullback.fst A.hom d =
      pullback.fst (pullback.snd A.hom b) a ≫ pullback.fst A.hom b := by
  subst h
  simp [pullbackCompIsoOfEq, pullbackComp]

/-- `pullbackCompIsoOfEq` commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIsoOfEq_hom_app_left_snd (h : a ≫ b = d) (A : Over Z) :
    ((pullbackCompIsoOfEq h).hom.app A).left ≫ pullback.snd A.hom d =
      pullback.snd (pullback.snd A.hom b) a :=
  Over.w ((pullbackCompIsoOfEq h).hom.app A)

/-- The inverse of `pullbackCompIsoOfEq` commutes with the projections to `A`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIsoOfEq_inv_app_left_fst_fst (h : a ≫ b = d) (A : Over Z) :
    ((pullbackCompIsoOfEq h).inv.app A).left ≫ pullback.fst (pullback.snd A.hom b) a ≫
      pullback.fst A.hom b = pullback.fst A.hom d := by
  subst h
  simp [pullbackCompIsoOfEq, pullbackComp]

/-- The inverse of `pullbackCompIsoOfEq` commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIsoOfEq_inv_app_left_snd (h : a ≫ b = d) (A : Over Z) :
    ((pullbackCompIsoOfEq h).inv.app A).left ≫ pullback.snd (pullback.snd A.hom b) a =
      pullback.snd A.hom d :=
  Over.w ((pullbackCompIsoOfEq h).inv.app A)

/-- The identifications `pullbackCompIsoOfEq` are coherent for three composable morphisms
`x ≫ a ≫ b`: identifying base change along `x ≫ (a ≫ b)` in one step agrees with identifying it
first along `a ≫ b` and then along `(x ≫ a) ≫ b`. -/
theorem pullbackCompIsoOfEq_hom_app_eq {W : C} {x : W ⟶ X} {y : W ⟶ Y} {v : X ⟶ Z} {w : W ⟶ Z}
    [HasPullbacksAlong x] [HasPullbacksAlong y] [HasPullbacksAlong v] [HasPullbacksAlong w]
    (hxa : x ≫ a = y) (hab : a ≫ b = v) (hyb : y ≫ b = w) (hxv : x ≫ v = w) (A : Over Z) :
    (pullbackCompIsoOfEq hxv).hom.app A =
      (pullback x).map ((pullbackCompIsoOfEq hab).inv.app A) ≫
        (pullbackCompIsoOfEq hxa).hom.app ((pullback b).obj A) ≫
          (pullbackCompIsoOfEq hyb).hom.app A := by
  -- The identity is checked on the two projections out of `A ×_Z W`; the projection lemmas for
  -- the middle factor are stated for `A ×_Z Y` as an object of `Over Y`.
  have h₁ := pullbackCompIsoOfEq_hom_app_left_fst_assoc hxa ((pullback b).obj A)
    (pullback.fst A.hom b)
  have h₂ := pullbackCompIsoOfEq_hom_app_left_snd hxa ((pullback b).obj A)
  dsimp only [pullback_obj_hom] at h₁ h₂
  ext1
  apply pullback.hom_ext
  · simp [h₁]
  · simp [h₂]

/-- For a commuting triangle `a ≫ b = d`, morphisms which agree after base change along `b` agree
after base change along `d`. -/
theorem pullback_map_eq_map_of_comp_eq (h : a ≫ b = d) {A B : Over Z} {u v : A ⟶ B}
    (huv : (pullback b).map u = (pullback b).map v) : (pullback d).map u = (pullback d).map v := by
  rw [← cancel_epi ((pullbackCompIsoOfEq h).hom.app A), ← (pullbackCompIsoOfEq h).hom.naturality,
    ← (pullbackCompIsoOfEq h).hom.naturality]
  simp [huv]

end Triangle

/-- Two arrows agree after base change precisely when their underlying arrows agree after
precomposition with the projection from the base-changed source. -/
theorem pullback_map_eq_map_iff {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    {A B : Over Y} (u v : A ⟶ B) :
    (pullback f).map u = (pullback f).map v ↔
      pullback.fst A.hom f ≫ u.left = pullback.fst A.hom f ≫ v.left := by
  constructor
  · intro h
    simpa using congrArg (fun w ↦ w.left ≫ pullback.fst B.hom f) h
  · intro h
    ext1
    apply pullback.hom_ext
    · simpa using h
    · simp

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

namespace Limits.Cone

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {J : Type*} [Category* J] {D : J ⥤ C}

section LiftsAlong

variable (c : Cone D)

/-- The morphism `u` between base changes to the cone point lifts to a morphism between the base
changes to `D.obj k` along `g : k ⟶ i`: the base change of the lift to the cone point is `u`, up to
the comparison isomorphisms `Over.pullbackCompIsoOfEq`. -/
def LiftsAlong {i : J} {A B : Over (D.obj i)}
    (u : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj B) {k : J}
    (g : k ⟶ i) : Prop :=
  ∃ v : (Over.pullback (D.map g)).obj A ⟶ (Over.pullback (D.map g)).obj B,
    (Over.pullback (c.π.app k)).map v ≫ (Over.pullbackCompIsoOfEq (c.w g)).hom.app B =
      (Over.pullbackCompIsoOfEq (c.w g)).hom.app A ≫ u

variable {c}

/-- A lift is a morphism whose base change agrees with the given arrow under the canonical
comparison isomorphisms. -/
theorem liftsAlong_iff {i : J} {A B : Over (D.obj i)}
    (u : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj B) {k : J}
    (g : k ⟶ i) : c.LiftsAlong u g ↔
      ∃ v : (Over.pullback (D.map g)).obj A ⟶ (Over.pullback (D.map g)).obj B,
        (Over.pullback (c.π.app k)).map v ≫ (Over.pullbackCompIsoOfEq (c.w g)).hom.app B =
          (Over.pullbackCompIsoOfEq (c.w g)).hom.app A ≫ u := Iff.rfl

/-- Identity morphisms lift along every morphism to `i`. -/
@[simp]
theorem liftsAlong_id {i : J} (A : Over (D.obj i)) {k : J} (g : k ⟶ i) :
    c.LiftsAlong (𝟙 ((Over.pullback (c.π.app i)).obj A)) g :=
  ⟨𝟙 _, by simp⟩

/-- Lifts of two composable morphisms along the same morphism to `i` compose to a lift of their
composite. -/
theorem liftsAlong_comp {i : J} {A B E : Over (D.obj i)}
    {u : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj B}
    {u' : (Over.pullback (c.π.app i)).obj B ⟶ (Over.pullback (c.π.app i)).obj E} {k : J}
    {g : k ⟶ i} (hu : c.LiftsAlong u g) (hu' : c.LiftsAlong u' g) :
    c.LiftsAlong (u ≫ u') g := by
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := hu'
  exact ⟨v ≫ v', by simp [hv', reassoc_of% hv]⟩

/-- A lift along `g` base changes to a lift along `h ≫ g`. -/
theorem LiftsAlong.precomp {i : J} {A B : Over (D.obj i)}
    {u : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj B} {k l : J}
    {g : k ⟶ i} (h : l ⟶ k) (hg : c.LiftsAlong u g) : c.LiftsAlong u (h ≫ g) := by
  obtain ⟨v, hv⟩ := hg
  let C := Over.pullbackCompIsoOfEq (D.map_comp h g).symm
  refine ⟨C.inv.app A ≫ (Over.pullback (D.map h)).map v ≫ C.hom.app B, ?_⟩
  have hcoh (Z : Over (D.obj i)) := Over.pullbackCompIsoOfEq_hom_app_eq (c.w h)
    (D.map_comp h g).symm (c.w g) (c.w (h ≫ g)) Z
  have hnat := (Over.pullbackCompIsoOfEq (c.w h)).hom.naturality v
  dsimp only [Functor.comp_map] at hnat
  rw [hcoh, hcoh]
  simp [C, reassoc_of% hnat, hv]

end LiftsAlong

end Limits.Cone

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
