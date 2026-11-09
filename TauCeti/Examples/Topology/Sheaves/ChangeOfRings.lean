/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Exactness
import TauCeti.Topology.Sheaves.Stalks
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Checks for scalar extension of module sheaves

The native sheafified tensor functor preserves short exact sequences for `ℤ → ℚ`.
On a point, its stalk comparison sends the integral skyscraper to `ℚ` and preserves
`ℤ/2` under the identity coefficient map. The germ identity tests the direction of the
comparison, while naturality tests its action on maps without unfolding its construction.

The last check records the obstruction to asserting exactness without flatness:
extending multiplication by `2` from `ℤ` to `ℤ/2` gives the zero map.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open CategoryTheory Limits TopCat TopCat.Presheaf TopologicalSpace Opposite

-- Flat extension applies to arbitrary short exact sequences, not just sectionwise exact ones.
example {X : TopCat} (T : ShortComplex (X.Sheaf (ModuleCat ℤ))) (hT : T.ShortExact) :
    (T.map (Sheaf.composeAndSheafify (Opens.grothendieckTopology X)
      (ModuleCat.extendScalars (Int.castRingHom ℚ)))).ShortExact := by
  have hflat : (Int.castRingHom ℚ).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat ℚ (nonZeroDivisors ℤ))
  exact (Int.castRingHom ℚ).shortExact_map_sheafExtendScalars hflat hT

-- A nonzero torsion module is retained by the identity map; flatness is not needed here.
example :
    stalk ((Sheaf.composeAndSheafify (Opens.grothendieckTopology (TopCat.of PUnit))
      (ModuleCat.extendScalars (RingHom.id (ZMod 2)))).obj
        (skyscraperSheaf (X := TopCat.of PUnit) PUnit.unit (ModuleCat.of (ZMod 2) (ZMod 2)))).obj
      PUnit.unit ≅ ModuleCat.of (ZMod 2) (ZMod 2) :=
  ((ModuleCat.extendScalars (RingHom.id (ZMod 2))).stalkComposeAndSheafifyIso
    (X := TopCat.of PUnit) PUnit.unit).app _ ≪≫
    (ModuleCat.extendScalarsId (ZMod 2)).app _ ≪≫
      skyscraperPresheafStalkOfSpecializes (X := TopCat.of PUnit) PUnit.unit _ (specializes_refl _)

-- The free integral stalk becomes the rational module, rather than remaining integral.
example :
    stalk ((Sheaf.composeAndSheafify (Opens.grothendieckTopology (TopCat.of PUnit))
      (ModuleCat.extendScalars (Int.castRingHom ℚ))).obj
        (skyscraperSheaf (X := TopCat.of PUnit) PUnit.unit (ModuleCat.of ℤ ℤ))).obj
      PUnit.unit ≅ ModuleCat.of ℚ ℚ :=
  ((ModuleCat.extendScalars (Int.castRingHom ℚ)).stalkComposeAndSheafifyIso
    (X := TopCat.of PUnit) PUnit.unit).app _ ≪≫
    (ModuleCat.extendScalars (Int.castRingHom ℚ)).mapIso
      (skyscraperPresheafStalkOfSpecializes (X := TopCat.of PUnit)
        PUnit.unit _ (specializes_refl _)) ≪≫
    ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of ℤ ℤ) ≪≫
      (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toModuleIso

example {X : TopCat} {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    {F H : X.Sheaf (ModuleCat R)} (α : F ⟶ H) (x : X) :
    (stalkFunctor (ModuleCat S) x).map
        (((Sheaf.composeAndSheafify (Opens.grothendieckTopology X)
          (ModuleCat.extendScalars φ)).map α).hom) ≫
        ((ModuleCat.extendScalars φ).stalkComposeAndSheafifyIso x).hom.app H =
      ((ModuleCat.extendScalars φ).stalkComposeAndSheafifyIso x).hom.app F ≫
        (ModuleCat.extendScalars φ).map ((stalkFunctor (ModuleCat R) x).map α.hom) :=
  ((ModuleCat.extendScalars φ).stalkComposeAndSheafifyIso x).hom.naturality α

example {X : TopCat} {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (F : X.Sheaf (ModuleCat R)) (U : Opens X) (x : X) (hx : x ∈ U) :
    (toSheafify (Opens.grothendieckTopology X)
        (F.obj ⋙ ModuleCat.extendScalars φ)).app (op U) ≫
      germ ((Sheaf.composeAndSheafify (Opens.grothendieckTopology X)
        (ModuleCat.extendScalars φ)).obj F).obj U x hx ≫
      ((ModuleCat.extendScalars φ).stalkComposeAndSheafifyIso x).hom.app F =
        (ModuleCat.extendScalars φ).map (F.presheaf.germ U x hx) :=
  (ModuleCat.extendScalars φ).germ_stalkComposeAndSheafifyIso_hom_app x F U hx

-- This coefficient map kills the integral injection given by multiplication by two.
example : (ModuleCat.extendScalars (Int.castRingHom (ZMod 2))).map
    ((2 : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)) = 0 := by
  rw [TauCeti.ModuleCat.extendScalars_map_smul_id]
  have h2 : (Int.castRingHom (ZMod 2)) (2 : ℤ) = 0 := by decide
  rw [h2, zero_smul]
