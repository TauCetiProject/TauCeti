/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.CategoryTheory.Exact.Abelian
import TauCeti.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Closure of finitely generated modules under quotients, extensions and Serre classes

Over any ring `R`, `ModuleCat.isFG R` is closed under quotients and extensions (via
`CategoryTheory.ObjectProperty.IsClosedUnderExtensions`, and equivalently for the canonical exact
structure of the abelian category `ModuleCat R` via `TauCeti.isExtensionClosed_finiteModules`).
Combined with subobject closure over a Noetherian ring (`ModuleCat.isFG_isClosedUnderSubobjects`),
this makes `ModuleCat.isFG R` a Serre class (`CategoryTheory.ObjectProperty.IsSerreClass`).

## Main statements

* `ModuleCat.isFG R` has instances of `CategoryTheory.ObjectProperty.IsClosedUnderQuotients`,
  `CategoryTheory.ObjectProperty.IsClosedUnderExtensions`, and (over `[IsNoetherianRing R]`)
  `CategoryTheory.ObjectProperty.IsSerreClass`.
* `TauCeti.isExtensionClosed_finiteModules`: `ModuleCat.isFG R` is extension closed for
  `ExactStructure.abelian (ModuleCat R)`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

variable (R : Type u) [Ring R]

/-- Quotients of finitely generated modules are finitely generated. -/
instance : (ModuleCat.isFG.{v, u} R).IsClosedUnderQuotients where
  prop_of_epi {M N} f _ hM := by
    have : Module.Finite R M := (ModuleCat.isFG_iff M).mp hM
    exact (ModuleCat.isFG_iff N).mpr
      (Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp inferInstance))

/-- Extensions of finitely generated modules are finitely generated. -/
instance : (ModuleCat.isFG.{v, u} R).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have : Module.Finite R S.X₁ := (ModuleCat.isFG_iff S.X₁).mp h₁
    have : Module.Finite R S.X₃ := (ModuleCat.isFG_iff S.X₃).mp h₃
    exact (ModuleCat.isFG_iff S.X₂).mpr hS.moduleCat_finite_X₂

/-- Over a Noetherian ring, finitely generated modules form a Serre class. -/
instance [IsNoetherianRing R] : (ModuleCat.isFG.{v, u} R).IsSerreClass where

/-- **The finitely generated modules are extension closed**: the middle term of a short exact
sequence with finitely generated ends is finitely generated. -/
theorem isExtensionClosed_finiteModules :
    (ExactStructure.abelian (ModuleCat.{v} R)).IsExtensionClosed (ModuleCat.isFG R) :=
  (ExactStructure.isExtensionClosed_abelian_iff _).mpr inferInstance

end TauCeti
