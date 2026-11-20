/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.KFlat
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivabilityStructure
public import TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor

/-!
# Tests for derived tensor products of sheaves of modules

On a scheme `X`, K-flat complexes of `𝒪_X`-modules form a left derivability structure, so the
derived tensor product `K ⊗^L L` exists on the unbounded derived category `D(𝒪_X)`, whichever
model `HasDerivedCategory` of it is chosen. The structure sheaf placed in degree `0` is a unit on
both sides: `𝒪_X[0] ⊗^L K ≅ K ≅ K ⊗^L 𝒪_X[0]`, naturally in `K`. The same construction gives the
derived tensor product of complexes of abelian groups, with unit `ℤ[0]`.
-/

open CategoryTheory MonoidalCategory TauCeti.SheafOfModules

noncomputable section

namespace TauCeti

universe u

section Scheme

variable (X : AlgebraicGeometry.Scheme.{u})

/-- K-flat complexes of `𝒪_X`-modules form a left derivability structure. -/
example : (CochainComplex.KFlat.localizerMorphism
    (SheafOfModules.{u} (ringCatSheaf X.sheaf))).IsLeftDerivabilityStructure :=
  inferInstance

variable [HasDerivedCategory (SheafOfModules.{u} (ringCatSheaf X.sheaf))]

/-- The unit of the derived tensor product is the structure sheaf `𝒪_X` in degree `0`. -/
example : 𝟙_ (SheafOfModules.{u} (ringCatSheaf X.sheaf)) =
    SheafOfModules.unit (ringCatSheaf X.sheaf) :=
  tensorUnit_eq X.sheaf

/-- Derived tensor product with `𝒪_X[0]` on the left fixes the other factor. -/
example (K : DerivedCategory (SheafOfModules.{u} (ringCatSheaf X.sheaf))) :
    ((derivedTensor _).obj ((DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (ringCatSheaf X.sheaf)))).obj K ≅ K := by
  rw [← tensorUnit_eq X.sheaf]
  exact (derivedTensorLeftUnitor _).app K

/-- Derived tensor product with `𝒪_X[0]` on the right fixes the other factor. -/
example (K : DerivedCategory (SheafOfModules.{u} (ringCatSheaf X.sheaf))) :
    ((derivedTensor _).obj K).obj ((DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (ringCatSheaf X.sheaf))) ≅ K := by
  rw [← tensorUnit_eq X.sheaf]
  exact (derivedTensorRightUnitor _).app K

end Scheme

section AbelianGroups

variable [HasDerivedCategory (ModuleCat.{0} ℤ)]

/-- Derived tensor product of complexes of abelian groups with `ℤ[0]` fixes the other factor. -/
example (K : DerivedCategory (ModuleCat.{0} ℤ)) :
    ((derivedTensor _).obj ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of ℤ ℤ))).obj K ≅
      K :=
  (derivedTensorLeftUnitor _).app K

end AbelianGroups

end TauCeti

end
