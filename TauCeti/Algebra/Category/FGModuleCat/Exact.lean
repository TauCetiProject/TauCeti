/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.CategoryTheory.Exact.Abelian
import TauCeti.Algebra.Category.ModuleCat.Finrank

/-!
# Closure of finitely generated modules under quotients, subobjects and extensions

Over any ring `R`, `ModuleCat.isFG R` is closed under quotients, and closed under extensions for
the canonical exact structure of the abelian category `ModuleCat R`
(`CategoryTheory.ShortComplex.ShortExact.moduleCat_finite_X₂`). Over a Noetherian ring `R`, it is
also closed under subobjects.

## Main statements

* `TauCeti.isExtensionClosed_finiteModules`: `ModuleCat.isFG R` is extension closed.
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

/-- Over a Noetherian ring, submodules of finitely generated modules are finitely generated. -/
instance [IsNoetherianRing R] : (ModuleCat.isFG.{v, u} R).IsClosedUnderSubobjects where
  prop_of_mono {M N} f _ hN := by
    have : Module.Finite R N := (ModuleCat.isFG_iff N).mp hN
    exact (ModuleCat.isFG_iff M).mpr
      (Module.Finite.of_injective f.hom ((ModuleCat.mono_iff_injective f).mp inferInstance))

/-- **The finitely generated modules are extension closed**: the middle term of a short exact
sequence with finitely generated ends is finitely generated. -/
theorem isExtensionClosed_finiteModules :
    (ExactStructure.abelian (ModuleCat.{v} R)).IsExtensionClosed (ModuleCat.isFG R) where
  prop_X₂ {S} hS h₁ h₃ := by
    rw [ExactStructure.abelian_conflation] at hS
    have : Module.Finite R S.X₁ := (ModuleCat.isFG_iff S.X₁).mp h₁
    have : Module.Finite R S.X₃ := (ModuleCat.isFG_iff S.X₃).mp h₃
    exact (ModuleCat.isFG_iff S.X₂).mpr hS.moduleCat_finite_X₂

end TauCeti
