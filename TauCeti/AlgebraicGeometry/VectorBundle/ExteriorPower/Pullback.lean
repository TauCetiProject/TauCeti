/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower.Basic

/-!
# A basis-dependent isomorphism for pullbacks of exterior powers

The exterior power of a finite free sheaf is free on the finite subsets of its basis. Pullback
preserves this description, giving an isomorphism between the two resulting free sheaves. The
isomorphism below is constructed through chosen bases and an order on the index type; it is an
objectwise identification for free sheaves, not the canonical pullback comparison needed to glue
comparisons for finite locally free sheaves.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

universe u

open _root_.AlgebraicGeometry

variable {X Y : _root_.AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- The pullback of the exterior power of a finite free sheaf is isomorphic to the exterior power
of its pullback. This objectwise isomorphism is constructed through the chosen free bases; it does
not assert compatibility with maps between free sheaves. -/
noncomputable def pullbackExteriorPowerFreeIso (I : Type u) [Finite I] (n : ℕ) :
      (pullback f).obj ((exteriorPower Y n).obj (free Y I)) ≅
      (exteriorPower X n).obj ((pullback f).obj (free Y I)) := by
  classical
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let eY : (exteriorPower Y n).obj (free Y I) ≅ free Y (Set.powersetCard I n) :=
    ObjectProperty.isoMk _
      (eqToIso (by simp only [exteriorPower_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.exteriorPowerFreeIso (R := Y.sheaf) I n ≪≫
        eqToIso (free_obj Y (Set.powersetCard I n)).symm)
  let eX : (exteriorPower X n).obj (free X I) ≅ free X (Set.powersetCard I n) :=
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
  let pSub : (pullback f).obj (free Y (Set.powersetCard I n)) ≅
      free X (Set.powersetCard I n) :=
    ObjectProperty.isoMk _
      (eqToIso (by rw [pullback_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Set.powersetCard I n) ≪≫
        eqToIso (free_obj X (Set.powersetCard I n)).symm)
  exact ((pullback f).mapIso eY ≪≫ pSub) ≪≫
    ((exteriorPower X n).mapIso pI ≪≫ eX).symm

end FiniteLocallyFreeSheaf

end AlgebraicGeometry

end TauCeti
