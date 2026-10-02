/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Basic
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor

/-!
# Monoidal restriction along functors of sites

Restriction along a continuous and cocontinuous functor of sites is strong monoidal when
its coefficient sheaf is the restriction of the original coefficient sheaf. The tensorator
descends the sectionwise tensor map of precomposition through sheafification.
Cocontinuity ensures that restriction commutes with sheafification, making this map invertible.

This applies both to slice sites and to the sites of opens of open subspaces. It allows exact
pairings of sheaves of modules to be restricted without choosing new evaluation maps.

The descent uses Mathlib's `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`
and `lifting_isMonoidal`, applied to the existing
`TauCeti.SheafOfModules.pushforwardSheafificationIso`.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.SheafOfModules

universe u

noncomputable section

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
  (R : Sheaf K CommRingCat.{u})

local notation "sourceSheafification" =>
  PresheafOfModules.sheafification (R := ringCatSheaf R)
    (𝟙 (ObjectProperty.FullSubcategory.obj (ringCatSheaf R)))
local notation "targetSheafification" =>
  PresheafOfModules.sheafification
    (R := Functor.obj (F.sheafPushforwardContinuous RingCat J K) (ringCatSheaf R))
    (𝟙 (ObjectProperty.FullSubcategory.obj
      (Functor.obj (F.sheafPushforwardContinuous RingCat J K) (ringCatSheaf R))))
local notation "presheafRestriction" =>
  PresheafOfModules.pushforward (F := F)
    (Iso.inv (pushforwardRingIso (J := J) (K := K) F (ringCatSheaf R)))
local notation "restrictionSheafification" => presheafRestriction ⋙ targetSheafification
local notation "sourceW" => MorphismProperty.inverseImage (K.W (A := AddCommGrpCat))
  (PresheafOfModules.toPresheaf (ObjectProperty.FullSubcategory.obj (ringCatSheaf R)))

/-- The restricted coefficient presheaf carries the sectionwise monoidal structure. -/
local instance : MonoidalCategory (PresheafOfModules.{u}
    (Functor.obj (F.sheafPushforwardContinuous RingCat.{u} J K) (ringCatSheaf R)).obj) :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := F.op ⋙ R.obj)

/-- The restricted coefficient sheaf carries the sheafified monoidal structure. -/
local instance : MonoidalCategory (_root_.SheafOfModules.{u}
    (Functor.obj (F.sheafPushforwardContinuous RingCat.{u} J K) (ringCatSheaf R))) :=
  monoidalCategory (pushforwardCommRing (J := J) (K := K) F R)

/-- Sheafification over the restricted coefficients is strong monoidal. -/
local instance : (targetSheafification).Monoidal :=
  sheafificationMonoidal (pushforwardCommRing (J := J) (K := K) F R)

/-- Sheaf restriction lifts presheaf restriction followed by sheafification through the
source sheafification localization. -/
local instance restrictionLifting : CategoryTheory.Localization.Lifting
    sourceSheafification sourceW restrictionSheafification
      (pushforwardModule (J := J) (K := K) F R) where
  iso := pushforwardSheafificationNatIso F (ringCatSheaf R)

/-- Presheaf restriction is strong monoidal because its coefficient comparison is the identity. -/
local instance presheafRestrictionMonoidal : (presheafRestriction).Monoidal := by
  -- The coefficient comparison is the identity, so this is precomposition of presheaves.
  change (PresheafOfModules.pushforward₀OfCommRingCat F R.obj).Monoidal
  infer_instance

/-- Presheaf restriction followed by target sheafification is strong monoidal. -/
local instance restrictionSheafificationMonoidal : (restrictionSheafification).Monoidal :=
  @Functor.Monoidal.instComp _ _ _ _ _ _ _ _ _
    presheafRestriction targetSheafification (presheafRestrictionMonoidal F R)
      (sheafificationMonoidal (pushforwardCommRing (J := J) (K := K) F R))

/-- Restriction to a continuous and cocontinuous site is strong monoidal. Its tensor and
unit comparisons descend those of presheaf restriction through sheafification. -/
instance pushforwardModuleMonoidal :
    (pushforwardModule (J := J) (K := K) F R).Monoidal :=
  @CategoryTheory.Localization.Monoidal.functorMonoidalOfComp
    _ _ _ _ _ _ _ _ _ sourceSheafification sourceW _ _
    (pushforwardModule (J := J) (K := K) F R) restrictionSheafification
    (restrictionSheafificationMonoidal F R) _ (restrictionLifting F R)

/-- The sheafification comparison respects tensor and unit maps. This identifies restriction's
monoidal structure with precomposition and sheafification of presheaves. -/
instance pushforwardSheafificationNatIso_isMonoidal :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (pushforwardSheafificationNatIso (J := J) (K := K) F (ringCatSheaf R)).hom
      (inferInstanceAs (sourceSheafification ⋙
        pushforwardModule (J := J) (K := K) F R).LaxMonoidal)
      (restrictionSheafificationMonoidal F R).toLaxMonoidal :=
  @CategoryTheory.Localization.Monoidal.lifting_isMonoidal
    _ _ _ _ _ _ _ _ _ sourceSheafification sourceW _ _
    (pushforwardModule (J := J) (K := K) F R) restrictionSheafification
    (restrictionSheafificationMonoidal F R) _ (restrictionLifting F R)

end

end TauCeti.SheafOfModules
