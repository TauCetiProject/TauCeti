/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import TauCeti.AlgebraicGeometry.VectorBundle.SymmetricPower.Basic

/-!
# Pullback of symmetric powers of free sheaves

The symmetric power of a finite free sheaf is free on the multisets indexing its monomial basis.
Pullback preserves this description, giving the chart comparison needed for pullback compatibility
of symmetric powers of finite locally free sheaves.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

universe u

open _root_.AlgebraicGeometry

variable {X Y : _root_.AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- Pullback commutes with symmetric powers of a finite free sheaf, by identifying both sides with
the free sheaf on degree-`n` multisets in the basis. -/
noncomputable def pullbackSymmetricPowerFreeIso (I : Type u) [Finite I] (n : ℕ) :
    (pullback f).obj ((symmetricPower Y n).obj (free Y I)) ≅
      (symmetricPower X n).obj ((pullback f).obj (free Y I)) := by
  classical
  let eY : (symmetricPower Y n).obj (free Y I) ≅ free Y (Sym I n) :=
    ObjectProperty.isoMk _
      (eqToIso (by simp only [symmetricPower_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.symmetricPowerFreeIso (R := Y.sheaf) I n ≪≫
        eqToIso (free_obj Y (Sym I n)).symm)
  let eX : (symmetricPower X n).obj (free X I) ≅ free X (Sym I n) :=
    ObjectProperty.isoMk _
      (eqToIso (by simp only [symmetricPower_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.symmetricPowerFreeIso (R := X.sheaf) I n ≪≫
        eqToIso (free_obj X (Sym I n)).symm)
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  let pI : (pullback f).obj (free Y I) ≅ free X I :=
    ObjectProperty.isoMk _
      (eqToIso (by rw [pullback_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I ≪≫
        eqToIso (free_obj X I).symm)
  let pSym : (pullback f).obj (free Y (Sym I n)) ≅ free X (Sym I n) :=
    ObjectProperty.isoMk _
      (eqToIso (by rw [pullback_obj_obj, free_obj]; rfl) ≪≫
        SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Sym I n) ≪≫
        eqToIso (free_obj X (Sym I n)).symm)
  exact ((pullback f).mapIso eY ≪≫ pSym) ≪≫
    ((symmetricPower X n).mapIso pI ≪≫ eX).symm

/-- The forward map of the pullback comparison is the composite of the free-sheaf
identifications on both sides. -/
theorem pullbackSymmetricPowerFreeIso_hom (I : Type u) [Finite I] (n : ℕ) :
    (pullbackSymmetricPowerFreeIso f I n).hom =
      (let eY : (symmetricPower Y n).obj (free Y I) ≅ free Y (Sym I n) :=
          ObjectProperty.isoMk _
            (eqToIso (by simp only [symmetricPower_obj_obj, free_obj]; rfl) ≪≫
              SheafOfModules.symmetricPowerFreeIso (R := Y.sheaf) I n ≪≫
              eqToIso (free_obj Y (Sym I n)).symm)
       let eX : (symmetricPower X n).obj (free X I) ≅ free X (Sym I n) :=
          ObjectProperty.isoMk _
            (eqToIso (by simp only [symmetricPower_obj_obj, free_obj]; rfl) ≪≫
              SheafOfModules.symmetricPowerFreeIso (R := X.sheaf) I n ≪≫
              eqToIso (free_obj X (Sym I n)).symm)
       letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
          inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
       let pI : (pullback f).obj (free Y I) ≅ free X I :=
          ObjectProperty.isoMk _
            (eqToIso (by rw [pullback_obj_obj, free_obj]; rfl) ≪≫
              SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I ≪≫
              eqToIso (free_obj X I).symm)
       let pSym : (pullback f).obj (free Y (Sym I n)) ≅ free X (Sym I n) :=
          ObjectProperty.isoMk _
            (eqToIso (by rw [pullback_obj_obj, free_obj]; rfl) ≪≫
              SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Sym I n) ≪≫
              eqToIso (free_obj X (Sym I n)).symm)
       (((pullback f).mapIso eY ≪≫ pSym) ≪≫
         ((symmetricPower X n).mapIso pI ≪≫ eX).symm).hom) := by
  classical
  rfl

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

end
