/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Condensed.Light.Monoidal

import TauCeti.CategoryTheory.Monoidal.Closed.Preadditive
import TauCeti.CategoryTheory.Monoidal.FunctorCategory
import TauCeti.CategoryTheory.Sites.Linear

/-!
# Additivity and linearity of light condensed tensor products

The tensor product of light condensed modules is additive and linear in both variables.
Additivity follows from the closed symmetric monoidal structure. Linearity is transported from
presheaves through linear sheafification.
-/

public section

universe u

open CategoryTheory Category MonoidalCategory

namespace LightCondensed

variable {R : Type u} [CommRing R]

/-- The tensor product of light condensed modules is additive in both variables. -/
instance monoidalPreadditive : MonoidalPreadditive (LightCondMod R) := by
  have : Limits.HasBinaryCoproducts (LightCondMod R) :=
    Limits.hasBinaryCoproducts_of_hasBinaryBiproducts
  exact TauCeti.monoidalPreadditive_of_isLeftAdjoint _

/-- The tensor product of light condensed modules is linear in both variables. -/
instance monoidalLinear : MonoidalLinear R (LightCondMod R) := by
  have (A : LightCondMod R) : (tensorLeft A).Linear R := by
    let J := coherentTopology LightProfinite.{u}
    let I := sheafToPresheaf J (ModuleCat.{u} R)
    let Q := presheafToSheaf J (ModuleCat.{u} R)
    let adj : Q ⊣ I := sheafificationAdjunction J (ModuleCat.{u} R)
    have e : (I ⋙ tensorLeft (I.obj A)) ⋙ Q ≅ tensorLeft A :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft I (Functor.Monoidal.commTensorLeft Q (I.obj A)).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso adj.counit) _ ≪≫
        Functor.leftUnitor _ ≪≫
        (tensoringLeft _).mapIso (asIso (adj.counit.app A))
    exact Functor.linear_of_iso _ e
  exact
    { whiskerLeft_smul A {_ _} r f := (tensorLeft A).map_smul r f
      smul_whiskerRight r {_ _} f A := by
        have := Functor.linear_of_iso R (BraidedCategory.tensorLeftIsoTensorRight A)
        exact (tensorRight A).map_smul r f }

end LightCondensed
