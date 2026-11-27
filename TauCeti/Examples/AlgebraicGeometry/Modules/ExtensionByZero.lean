/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.Modules.Restriction.ProjectionFormula
import Mathlib.Algebra.Homology.Additive

/-!
# Checks for extension by zero and its projection formula

Restriction recovers extension by zero for the empty and full opens as well as for arbitrary
opens. On the distinguished open `D(2)` of `Spec ℤ`, the projection formula also gives the
comparison for a structure sheaf placed in degree `-3`, after applying extension by zero
degreewise. This tests the ordinary formula on single complexes; tensor totalization of
arbitrary complexes requires an additional comparison.
-/

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Scheme.Modules

universe u

/-- Recovery on the empty open does not require a nonemptiness assumption. -/
example (X : Scheme.{u}) (N : (⊥ : X.Opens).toScheme.Modules) :
    (restrictFunctor (⊥ : X.Opens).ι).obj ((extensionByZero (⊥ : X.Opens)).obj N) ≅ N :=
  (extensionByZeroCompRestrictIso (⊥ : X.Opens)).app N

/-- Recovery on the full open uses the same unit isomorphism. -/
example (X : Scheme.{u}) (N : (⊤ : X.Opens).toScheme.Modules) :
    (restrictFunctor (⊤ : X.Opens).ι).obj ((extensionByZero (⊤ : X.Opens)).obj N) ≅ N :=
  (extensionByZeroCompRestrictIso (⊤ : X.Opens)).app N

/-- Extension by zero on the full open is an equivalence. -/
example (X : Scheme.{u}) : (extensionByZero (⊤ : X.Opens)).IsEquivalence := by
  have : (restrictFunctor (⊤ : X.Opens).ι).IsEquivalence := by
    let e : (restrictEquivalence X.topIso).functor ≅ restrictFunctor (⊤ : X.Opens).ι :=
      eqToIso (restrictEquivalence_functor X.topIso) ≪≫
        restrictFunctorCongr (Scheme.topIso_hom X)
    exact Functor.isEquivalence_of_iso e
  exact (extensionByZeroAdjunction (⊤ : X.Opens)).isEquivalence_left_of_isEquivalence_right

/-- The projection formula on `D(2)` can be used without unfolding extension by zero. -/
example :
    let X := Spec (.of ℤ)
    let U := X.basicOpen ((Scheme.ΓSpecIso (.of ℤ)).inv 2)
    (extensionByZero U).obj ((restrictFunctor U.ι).obj (𝟙_ X.Modules) ⊗
      (𝟙_ U.toScheme.Modules)) ≅
        (𝟙_ X.Modules) ⊗ (extensionByZero U).obj (𝟙_ U.toScheme.Modules) :=
  (extensionByZeroProjectionIso _ _).app _

/-- Degreewise extension by zero of the projection formula, with the structure sheaf in
degree `-3`, agrees with applying the single-complex functor to the ordinary formula. -/
example :
    let X := Spec (.of ℤ)
    let U := X.basicOpen ((Scheme.ΓSpecIso (.of ℤ)).inv 2)
    ((extensionByZero U).mapHomologicalComplex (.up ℤ)).obj
        ((HomologicalComplex.single U.toScheme.Modules (.up ℤ) (-3)).obj
          ((restrictFunctor U.ι).obj (𝟙_ X.Modules) ⊗ (𝟙_ U.toScheme.Modules))) ≅
      (HomologicalComplex.single X.Modules (.up ℤ) (-3)).obj
        ((𝟙_ X.Modules) ⊗ (extensionByZero U).obj (𝟙_ U.toScheme.Modules)) :=
  (HomologicalComplex.singleMapHomologicalComplex _ (.up ℤ) (-3)).app _ ≪≫
    (HomologicalComplex.single _ (.up ℤ) (-3)).mapIso
      ((extensionByZeroProjectionIso _ _).app _)

end
