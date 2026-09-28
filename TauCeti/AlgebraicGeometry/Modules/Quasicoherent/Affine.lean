/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# Quasi-coherent modules on an affine scheme

The category of quasi-coherent modules on `Spec R` is abelian. Mathlib's tilde equivalence
identifies it with `ModuleCat R`, so kernels and cokernels can be computed using modules.
It also has enough injectives, transported from the module category. These are the category
theoretic inputs for deriving the exact global-sections functor on an affine scheme.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- Quasi-coherent modules on an affine scheme form an abelian category. -/
noncomputable instance (R : CommRingCat.{u}) :
    Abelian (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory := by
  letI : Limits.HasFiniteProducts
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    ⟨fun _ =>
      Adjunction.hasLimitsOfShape_of_equivalence (tildeEquiv (R := R)).inverse⟩
  exact abelianOfEquivalence (tildeEquiv (R := R)).inverse

/-- Quasi-coherent modules on an affine scheme admit injective resolutions. -/
noncomputable instance (R : CommRingCat.{u}) :
    EnoughInjectives
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory := by
  let : EnoughInjectives (ModuleCat R) := ModuleCat.enoughInjectives R
  exact EnoughInjectives.of_equivalence (tildeEquiv (R := R)).inverse

end AlgebraicGeometry

end TauCeti
