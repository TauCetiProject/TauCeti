/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Restriction and sheafification for sheaves of modules

For a continuous and cocontinuous functor between sites, this file identifies pushforward of the
sheafification of a presheaf of modules with sheafification after pushforward. Restriction to a
slice site is the special case given by `Over.forget X`.

Pushforward of sheaves of modules is additive, as is its specialization to restriction to a slice
site.

The comparison is obtained from the unit of Mathlib's sheafification adjunction. Its underlying
morphism of presheaves of abelian groups is the sheafification map whiskered by the functor between
sites. Cocontinuity preserves its local injectivity and surjectivity, so Mathlib's localization
theorem makes the comparison an isomorphism after sheafification. No formalization is vendored for
that comparison: the ingredients are Mathlib's `PresheafOfModules.sheafificationAdjunction`,
`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`, and
`Presheaf.isLocallyInjective_whisker`/`Presheaf.isLocallySurjective_whisker`.

The iterated-slice comparison `iteratedSliceEquivalence` identifies two successive restrictions
with restriction to the underlying object; its unit-sheaf and restricted-object isomorphisms make
that identification usable for transporting local bases. The construction is adapted from
[Brian Nugent's implementation](https://github.com/leanprover-community/mathlib4/blob/d58ff62e7a9df910516798545083fcd91b20dda6/Mathlib/Algebra/Category/ModuleCat/Sheaf/Generators.lean).

## Main declarations

* `SheafOfModules.pushforwardSheafificationIso` is the sheafification-pushforward comparison for
  a continuous and cocontinuous functor;
* `SheafOfModules.overSheafificationIso` is its specialization to a slice site;
* `SheafOfModules.iteratedSliceEquivalence` identifies restriction to an iterated slice
  with restriction to the underlying object, with
  `SheafOfModules.iteratedSliceEquivalenceUnitSheafIso` and
  `SheafOfModules.iteratedSliceEquivalenceInverseObjIso` as the two comparisons it
  provides on unit sheaves and on restrictions of a sheaf of modules;
* `SheafOfModules.pushforward` and `SheafOfModules.overFunctor` are additive.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible sheaves on a
scheme; the Picard group `Pic X` under `⊗`", by providing the restriction compatibility needed to
compare local trivializations on refinements.
-/

public section

open CategoryTheory Category Opposite

namespace TauCeti

universe u v v₁ v₂ u₁ u₂

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
variable (R : Sheaf J RingCat.{u}) in
/-- Restriction along `Over.iteratedSliceEquiv Y`, as an equivalence between sheaves of modules on
the slice over `Y.left` and sheaves of modules on the iterated slice over `Y`. -/
noncomputable def _root_.SheafOfModules.iteratedSliceEquivalence {Z : C} (Y : Over Z) :
    SheafOfModules.{v} (R.over Y.left) ≌ SheafOfModules.{v} ((R.over Z).over Y) :=
  pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv Y)
    (S := (R.over Z).over Y) (R := R.over Y.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- The forward direction of `iteratedSliceEquivalence` is restriction along
`(Over.iteratedSliceEquiv Y).functor`. -/
@[simp]
theorem _root_.SheafOfModules.iteratedSliceEquivalence_functor
    (R : Sheaf J RingCat.{u}) {Z : C} (Y : Over Z) :
    (iteratedSliceEquivalence R Y).functor =
      _root_.SheafOfModules.pushforward.{v} (F := (Over.iteratedSliceEquiv Y).functor) (𝟙 _) :=
  (rfl)

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- The backward direction of `iteratedSliceEquivalence` is restriction along
`(Over.iteratedSliceEquiv Y).inverse`. -/
@[simp]
theorem _root_.SheafOfModules.iteratedSliceEquivalence_inverse
    (R : Sheaf J RingCat.{u}) {Z : C} (Y : Over Z) :
    (iteratedSliceEquivalence R Y).inverse =
      _root_.SheafOfModules.pushforward.{v} (F := (Over.iteratedSliceEquiv Y).inverse) (𝟙 _) :=
  (rfl)

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- The comparison of *unit sheaves* (each structure sheaf as a module over itself) used when
transporting generating sections off an iterated slice: the unit sheaf on the slice over `Y.left`
and the restriction along `(iteratedSliceEquivalence R Y).inverse` of the unit sheaf on the
iterated slice over `Y` are definitionally equal. -/
noncomputable def _root_.SheafOfModules.iteratedSliceEquivalenceUnitSheafIso
    (R : Sheaf J RingCat.{u}) {Z : C}
    (Y : Over Z) :
    _root_.SheafOfModules.unit (R.over Y.left) ≅
      (iteratedSliceEquivalence R Y).inverse.obj
        (_root_.SheafOfModules.unit ((R.over Z).over Y)) :=
  eqToIso (show _root_.SheafOfModules.unit (R.over Y.left) =
    (iteratedSliceEquivalence R Y).inverse.obj
      (_root_.SheafOfModules.unit ((R.over Z).over Y)) by
    rw [iteratedSliceEquivalence_inverse]
    rfl)

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- The unit-sheaf comparison is the identity. -/
@[simp]
theorem _root_.SheafOfModules.iteratedSliceEquivalenceUnitSheafIso_hom
    (R : Sheaf J RingCat.{u}) {Z : C} (Y : Over Z) :
    (iteratedSliceEquivalenceUnitSheafIso R Y).hom =
      eqToHom (by rw [iteratedSliceEquivalence_inverse]; rfl) :=
  (rfl)

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- The inverse of the unit-sheaf comparison is the reverse equality morphism. -/
@[simp]
theorem _root_.SheafOfModules.iteratedSliceEquivalenceUnitSheafIso_inv
    (R : Sheaf J RingCat.{u}) {Z : C} (Y : Over Z) :
    (iteratedSliceEquivalenceUnitSheafIso R Y).inv =
      eqToHom (by rw [iteratedSliceEquivalence_inverse]; rfl) :=
  (rfl)

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- The inverse of the unit isomorphism of `iteratedSliceEquivalence` at `M.over Y.left`, composed
with the equality isomorphism that identifies `(iteratedSliceEquivalence R Y).functor.obj
(M.over Y.left)` with `(M.over Z).over Y`. -/
noncomputable def _root_.SheafOfModules.iteratedSliceEquivalenceInverseObjIso
    (R : Sheaf J RingCat.{u}) {Z : C}
    (Y : Over Z) (M : SheafOfModules.{v} R) :
    (iteratedSliceEquivalence R Y).inverse.obj ((M.over Z).over Y) ≅ M.over Y.left :=
  -- Both objects restrict `M` along `Over.forget` twice; the equality is made explicit here
  -- because the equivalence is opaque outside its characteristic equations.
  (iteratedSliceEquivalence R Y).inverse.mapIso
      (eqToIso (show (M.over Z).over Y =
        (iteratedSliceEquivalence R Y).functor.obj (M.over Y.left) by
          rw [iteratedSliceEquivalence_functor]
          rfl)) ≪≫
    (iteratedSliceEquivalence R Y).unitIso.symm.app (M.over Y.left)

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- `iteratedSliceEquivalenceInverseObjIso` is the inverse unit isomorphism composed with the
equality isomorphism supplied by `iteratedSliceEquivalence_functor`. -/
theorem _root_.SheafOfModules.iteratedSliceEquivalenceInverseObjIso_def
    (R : Sheaf J RingCat.{u}) {Z : C} (Y : Over Z)
    (M : SheafOfModules.{v} R) :
    iteratedSliceEquivalenceInverseObjIso R Y M =
      (iteratedSliceEquivalence R Y).inverse.mapIso
          (eqToIso (show (M.over Z).over Y =
            (iteratedSliceEquivalence R Y).functor.obj (M.over Y.left) by
              rw [iteratedSliceEquivalence_functor]
              rfl)) ≪≫
        (iteratedSliceEquivalence R Y).unitIso.symm.app (M.over Y.left) :=
  (rfl)

section Additive

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The pushforward of sheaves of modules is additive. -/
instance : (_root_.SheafOfModules.pushforward.{v} φ).Additive where
  map_add := rfl

/-- Restriction to a slice site is additive. -/
instance (R : Sheaf J RingCat.{u}) (X : C) :
    (_root_.SheafOfModules.overFunctor.{v} R X).Additive :=
  inferInstanceAs (_root_.SheafOfModules.pushforward _).Additive

end Additive

section General

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
variable (R : Sheaf K RingCat.{u})
variable [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}] in
private abbrev pushedRing : Sheaf J RingCat.{u} :=
  (F.sheafPushforwardContinuous RingCat.{u} J K).obj R

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- The underlying presheaf of the continuous pushforward is precomposition by the functor
between sites. -/
abbrev pushforwardRingIso : F.op ⋙ R.obj ≅
    ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj :=
  Iso.refl _

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}] in
private abbrev presheafPushforward :
    PresheafOfModules.{v} R.obj ⥤
      PresheafOfModules.{v} (pushedRing (J := J) (K := K) F R).obj :=
  PresheafOfModules.pushforward (F := F)
    (pushforwardRingIso (J := J) (K := K) F R).inv

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}] in
private abbrev sheafPushforward :
    SheafOfModules.{v} R ⥤
      SheafOfModules.{v} (pushedRing (J := J) (K := K) F R) :=
  SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [F.IsCocontinuous J K] in
/-- The pushforward of a sheafification unit, as a map of presheaves of modules. This is the
canonical comparison whose sheafification is inverted by `pushforwardSheafificationIso`. -/
def pushforwardToSheafify (P : PresheafOfModules.{v} R.obj) :
    (PresheafOfModules.pushforward (F := F)
        (pushforwardRingIso (J := J) (K := K) F R).inv).obj P ⟶
      ((SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)).obj
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P)).val :=
  (presheafPushforward F R).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P)

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [F.IsCocontinuous J K] in
/-- Pushforward of the sheafification unit becomes whiskering on underlying presheaves. -/
private theorem toPresheaf_map_pushforwardToSheafify_def
    (P : PresheafOfModules.{v} R.obj) :
    (PresheafOfModules.toPresheaf _).map
        (pushforwardToSheafify (J := J) (K := K) F R P) =
      Functor.whiskerLeft F.op
        ((PresheafOfModules.toPresheaf _).map
          ((PresheafOfModules.sheafificationAdjunction (R := R)
            (𝟙 R.obj)).unit.app P)) := by
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [F.IsCocontinuous J K] in
/-- On underlying presheaves of abelian groups, `pushforwardToSheafify` is the canonical
sheafification map whiskered by the functor between sites. -/
theorem toPresheaf_map_pushforwardToSheafify
    (P : PresheafOfModules.{v} R.obj) :
    (PresheafOfModules.toPresheaf _).map
        (pushforwardToSheafify (J := J) (K := K) F R P) =
      Functor.whiskerLeft F.op (CategoryTheory.toSheafify K P.presheaf) := by
  rw [toPresheaf_map_pushforwardToSheafify_def,
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{v}] in
private theorem W_toPresheaf_map_pushforwardToSheafify
    (P : PresheafOfModules.{v} R.obj) :
    J.W ((PresheafOfModules.toPresheaf _).map
      (pushforwardToSheafify (J := J) (K := K) F R P)) := by
  rw [toPresheaf_map_pushforwardToSheafify]
  exact (J.W_iff_isLocallyBijective _).mpr
    ⟨Presheaf.isLocallyInjective_whisker J K F _,
      Presheaf.isLocallySurjective_whisker J K F _⟩

private instance isIso_sheafification_map_pushforwardToSheafify
    (P : PresheafOfModules.{v} R.obj) :
    IsIso ((PresheafOfModules.sheafification
      (R := pushedRing (J := J) (K := K) F R)
      (𝟙 (pushedRing (J := J) (K := K) F R).obj)).map
        (pushforwardToSheafify (J := J) (K := K) F R P)) := by
  -- `IsIso` is the inverse image of the isomorphism morphism property under sheafification.
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification
      (R := pushedRing (J := J) (K := K) F R)
      (𝟙 (pushedRing (J := J) (K := K) F R).obj)))
        (pushforwardToSheafify (J := J) (K := K) F R P)
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact W_toPresheaf_map_pushforwardToSheafify (J := J) (K := K) F R P

/-- For each presheaf of modules, pushforward along a continuous and cocontinuous functor of its
sheafification is isomorphic to sheafification after pushforward. -/
def pushforwardSheafificationIso (P : PresheafOfModules.{v} R.obj) :
    (SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)).obj
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P) ≅
      (PresheafOfModules.sheafification
        (R := (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj)).obj
          ((PresheafOfModules.pushforward (F := F)
            (pushforwardRingIso (J := J) (K := K) F R).inv).obj P) :=
  (sheafificationIso (pushedRing (J := J) (K := K) F R)
      ((sheafPushforward (J := J) (K := K) F R).obj
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P))).symm ≪≫
    (asIso ((PresheafOfModules.sheafification
      (R := pushedRing (J := J) (K := K) F R)
      (𝟙 (pushedRing (J := J) (K := K) F R).obj)).map
        (pushforwardToSheafify (J := J) (K := K) F R P))).symm

/-- The inverse of `pushforwardSheafificationIso` is the canonical comparison obtained from the
sheafification unit and counit. -/
@[simp]
theorem pushforwardSheafificationIso_inv (P : PresheafOfModules.{v} R.obj) :
    (pushforwardSheafificationIso F R P).inv =
      (PresheafOfModules.sheafification
        (R := (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj)).map
          (pushforwardToSheafify (J := J) (K := K) F R P) ≫
        (sheafificationIso ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
          ((SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)).obj
            ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P))).hom := by
  simp [pushforwardSheafificationIso]

end General

/-- For each presheaf of modules and object of the site, restriction of its sheafification is
isomorphic to the sheafification of its restriction. -/
def overSheafificationIso (R : Sheaf J RingCat.{u})
    (P : PresheafOfModules.{v} R.obj) (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{v}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{v}] :
    ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P).over X ≅
      (PresheafOfModules.sheafification (R := R.over X) (𝟙 (R.over X).obj)).obj
        ((PresheafOfModules.pushforward (F := Over.forget X)
          (pushforwardRingIso (J := J.over X) (K := J) (Over.forget X) R).inv).obj P) :=
  pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X) R P

/-- The inverse of `overSheafificationIso` is the canonical comparison obtained from the
sheafification unit and counit, as in `pushforwardSheafificationIso_inv`. -/
@[simp]
theorem overSheafificationIso_inv (R : Sheaf J RingCat.{u})
    (P : PresheafOfModules.{v} R.obj) (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{v}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{v}] :
    (overSheafificationIso R P X).inv =
      (PresheafOfModules.sheafification (R := R.over X) (𝟙 (R.over X).obj)).map
          (pushforwardToSheafify (J := J.over X) (K := J) (Over.forget X) R P) ≫
        (sheafificationIso (R.over X)
          (((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P).over X)).hom :=
  pushforwardSheafificationIso_inv (J := J.over X) (K := J) (Over.forget X) R P

end SheafOfModules

end

end TauCeti
