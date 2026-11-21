/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Derived.Restrict

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Data.ZMod.Basic
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-!
# Tests for derived restriction to open subschemes

On `X = Spec ℤ` with the open `U = D(2)`, derived restriction sends `(ℤ/2)~[0]` to zero, because
`2` is invertible on `U` and kills `ℤ/2`, while `(ℤ/2)~[0]` itself is non-zero in `D(𝒪_X)`. It
sends `𝒪_X[0]` to `𝒪_U[0]`. Derived restriction to the open `⊤` is an equivalence.
-/

open CategoryTheory Limits DerivedCategory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Coherent

universe w w' u

variable [HasDerivedCategory.{w} (Spec (.of ℤ)).Modules]
  [HasDerivedCategory.{w'}
    ((Spec (.of ℤ)).basicOpen ((Scheme.ΓSpecIso (.of ℤ)).inv 2)).toScheme.Modules]

/-- Derived restriction to `U = D(2)` sends `(ℤ/2)~[0]` to zero: its support `{(2)}` misses `U`,
since the sections of `(ℤ/2)~` over `D(2)` form the localization `(ℤ/2)[1/2] = 0`. -/
example : IsZero
    (((Spec (.of ℤ)).basicOpen ((Scheme.ΓSpecIso (.of ℤ)).inv 2)).ι.derivedRestrict.obj
      ((singleFunctor _ 0).obj ((tilde.functor (.of ℤ)).obj (.of _ (ZMod 2))))) := by
  have := subsingleton_tilde_basicOpen_of_smul_eq_zero (R := .of ℤ) (M := .of _ (ZMod 2)) 2
    fun m ↦ by rw [two_smul]; exact CharTwo.add_self_eq_zero (R := ZMod 2) m
  rw [← basicOpen_eq_of_affine, ← Scheme.Opens.ι_image_top
    ((Spec (.of ℤ)).basicOpen ((Scheme.ΓSpecIso (.of ℤ)).inv 2))] at this
  -- Transport along the identification of the sections of the restriction over `⊤` with those
  -- over the image of `⊤`.
  have := @Equiv.subsingleton _ _ (Scheme.Modules.restrictAppIso
    ((Spec (.of ℤ)).basicOpen ((Scheme.ΓSpecIso (.of ℤ)).inv 2)).ι
    ((tilde.functor (.of ℤ)).obj (.of _ (ZMod 2))) ⊤).addCommGroupIsoToAddEquiv.toEquiv this
  exact ((singleFunctor _ 0).map_isZero
    (Scheme.Modules.isZero_of_subsingleton_sections_top _)).of_iso
    (((Scheme.Modules.restrictFunctor _).mapDerivedCategorySingleFunctor 0).app _)

/-- `(ℤ/2)~[0]` is non-zero in `D(𝒪_{Spec ℤ})`, so the identity of `D(𝒪_{Spec ℤ})`, which keeps
the stalk at `(2)`, does not kill it. -/
example : ¬ IsZero ((singleFunctor (Spec (.of ℤ)).Modules 0).obj
    ((tilde.functor (.of ℤ)).obj (.of _ (ZMod 2)))) := fun h ↦ by
  have := ModuleCat.subsingleton_of_isZero (IsZero.of_full_of_faithful_of_isZero
    (tilde.functor _) _ (IsZero.of_full_of_faithful_of_isZero (singleFunctor _ 0) _ h))
  exact zero_ne_one (Subsingleton.elim (0 : ZMod 2) 1)

/-- Derived restriction to `U = D(2)` sends `𝒪_X[0]` to `𝒪_U[0]`. -/
example : Nonempty
    (((Spec (.of ℤ)).basicOpen ((Scheme.ΓSpecIso (.of ℤ)).inv 2)).ι.derivedRestrict.obj
      ((singleFunctor _ 0).obj (SheafOfModules.unit (Spec (.of ℤ)).ringCatSheaf)) ≅
    (singleFunctor _ 0).obj (SheafOfModules.unit
      ((Spec (.of ℤ)).basicOpen ((Scheme.ΓSpecIso (.of ℤ)).inv 2)).toScheme.ringCatSheaf)) :=
  ⟨((Scheme.Modules.restrictFunctor _).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (singleFunctor _ 0).mapIso (Scheme.Modules.restrictUnitIso _)⟩

/-- Derived restriction to the open `⊤` of a scheme is an equivalence. -/
example (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules]
    [HasDerivedCategory.{w'} (⊤ : X.Opens).toScheme.Modules] :
    (⊤ : X.Opens).ι.derivedRestrict.IsEquivalence :=
  have : IsIso (⊤ : X.Opens).ι := X.topIso.isIso_hom
  inferInstance

end TauCeti.AlgebraicGeometry.Coherent
