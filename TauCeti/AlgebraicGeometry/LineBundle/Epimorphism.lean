/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Stalk
import Mathlib.RingTheory.PicardGroup

/-!
# Epimorphisms of line bundles

An invertible sheaf has no proper invertible quotient. On stalks this is the fact that a
surjective linear map between invertible modules is bijective.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- An epimorphism between invertible sheaves is an isomorphism. -/
theorem Hom.isIso_of_epi_of_isInvertible {X : Scheme.{u}} {M N : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X N] (φ : M ⟶ N) [Epi φ] : IsIso φ := by
  have hb (x : X) : Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab x).map φ.mapPresheaf) := by
    rw [← φ.coe_stalkₗ x]
    have (L : X.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L] :
        Module.Invertible (X.presheaf.stalk x) (L.presheaf.stalk x) :=
      .congr (nonempty_linearEquiv_stalk_of_isInvertible L x).some
    exact Module.Invertible.bijective_of_surjective (f := φ.stalkₗ x) (φ.stalkₗ_surjective_of_epi x)
  let ψ := (TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf X).map φ
  refine Hom.isIso_iff_isIso_app.mpr fun U ↦ (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective ψ U fun x _ ↦ hb x

end AlgebraicGeometry.Scheme.Modules
