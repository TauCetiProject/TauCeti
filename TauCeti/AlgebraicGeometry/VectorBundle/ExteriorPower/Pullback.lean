/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower

/-!
# Pullback of exterior powers of free sheaves

The exterior power of a finite free sheaf is free on the subsets indexing its wedge basis.
Pullback preserves this description, providing the chart comparison for pullback compatibility
of exterior powers of finite locally free sheaves.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

universe u

open _root_.AlgebraicGeometry

variable {X Y : _root_.AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- Pullback commutes with exterior powers of a finite free sheaf, by identifying both sides with
the free sheaf on subsets of the chosen basis. -/
noncomputable def pullbackExteriorPowerFreeIso (I : Type u) [Finite I] (n : ℕ) :
    (pullback f).obj ((exteriorPower Y n).obj (free Y I)) ≅
      (exteriorPower X n).obj ((pullback f).obj (free Y I)) := by
  classical
  let _ : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let eY : (exteriorPower Y n).obj (free Y I) ≅
      free Y (Set.powersetCard I n) :=
    ObjectProperty.isoMk _
      (eqToIso (by simp only [exteriorPower_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.exteriorPowerFreeIso (R := Y.sheaf) I n ≪≫
        eqToIso (free_obj Y (Set.powersetCard I n)).symm)
  let eX : (exteriorPower X n).obj (free X I) ≅
      free X (Set.powersetCard I n) :=
    ObjectProperty.isoMk _
      (eqToIso (by simp only [exteriorPower_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.exteriorPowerFreeIso (R := X.sheaf) I n ≪≫
        eqToIso (free_obj X (Set.powersetCard I n)).symm)
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  let pI : (pullback f).obj (free Y I) ≅ free X I :=
    ObjectProperty.isoMk _
      (eqToIso (by rw [pullback_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I ≪≫
        eqToIso (free_obj X I).symm)
  let pExterior : (pullback f).obj (free Y (Set.powersetCard I n)) ≅
      free X (Set.powersetCard I n) :=
    ObjectProperty.isoMk _
      (eqToIso (by rw [pullback_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Set.powersetCard I n) ≪≫
        eqToIso (free_obj X (Set.powersetCard I n)).symm)
  exact ((pullback f).mapIso eY ≪≫ pExterior) ≪≫
    ((exteriorPower X n).mapIso pI ≪≫ eX).symm

/-- The forward map of the pullback comparison is the composite of the free-sheaf
identifications on both sides. -/
theorem pullbackExteriorPowerFreeIso_hom (I : Type u) [Finite I] (n : ℕ) :
    (pullbackExteriorPowerFreeIso f I n).hom =
      (let _ : LinearOrder I := by classical exact linearOrderOfSTO WellOrderingRel
       let eY : (exteriorPower Y n).obj (free Y I) ≅
           free Y (Set.powersetCard I n) :=
         ObjectProperty.isoMk _
           (eqToIso (by simp only [exteriorPower_obj_obj, free_obj]; rfl) ≪≫
             SheafOfModules.exteriorPowerFreeIso (R := Y.sheaf) I n ≪≫
             eqToIso (free_obj Y (Set.powersetCard I n)).symm)
       let eX : (exteriorPower X n).obj (free X I) ≅
           free X (Set.powersetCard I n) :=
         ObjectProperty.isoMk _
           (eqToIso (by simp only [exteriorPower_obj_obj, free_obj]; rfl) ≪≫
             SheafOfModules.exteriorPowerFreeIso (R := X.sheaf) I n ≪≫
             eqToIso (free_obj X (Set.powersetCard I n)).symm)
       letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
         inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
       let pI : (pullback f).obj (free Y I) ≅ free X I :=
         ObjectProperty.isoMk _
           (eqToIso (by rw [pullback_obj_obj, free_obj]; rfl) ≪≫
             SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I ≪≫
             eqToIso (free_obj X I).symm)
       let pExterior : (pullback f).obj (free Y (Set.powersetCard I n)) ≅
           free X (Set.powersetCard I n) :=
         ObjectProperty.isoMk _
           (eqToIso (by rw [pullback_obj_obj, free_obj]; rfl) ≪≫
             SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom
               (Set.powersetCard I n) ≪≫
             eqToIso (free_obj X (Set.powersetCard I n)).symm)
       (((pullback f).mapIso eY ≪≫ pExterior) ≪≫
         ((exteriorPower X n).mapIso pI ≪≫ eX).symm).hom) := by
  classical
  rfl

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

end
