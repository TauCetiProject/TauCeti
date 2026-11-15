/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product

/-!
# The symmetric monoidal category of finitely presented sheaves

The site-level closure of finitely presented sheaves of modules under tensor products and the
monoidal unit (`TauCeti.SheafOfModules.isMonoidal_isFinitePresentation`) specializes to an arbitrary
scheme `X`: the structure sheaf `𝒪_X` is finitely presented, and the tensor product `M ⊗ N` of
finitely presented `𝒪_X`-modules is finitely presented. Consequently, `FinitelyPresentedSheaf X`
inherits a symmetric monoidal category structure from `X.Modules` as a monoidal full subcategory.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorObj` and
  `AlgebraicGeometry.Scheme.Modules.isMonoidal_isFinitePresentation`: tensor products of finitely
  presented `𝒪_X`-modules are finitely presented, so finite presentation is a monoidal property of
  `𝒪_X`-modules;
* `TauCeti.AlgebraicGeometry.isFinitePresentation_unit` and
  `TauCeti.AlgebraicGeometry.isFinitePresentation_structureSheaf`: the structure sheaf `𝒪_X`,
  viewed as a module over itself, is finitely presented in monoidal-unit and explicit-unit
  notation;
* `MonoidalCategory (FinitelyPresentedSheaf X)` and `SymmetricCategory (FinitelyPresentedSheaf X)`:
  the symmetric monoidal structure inherited from `X.Modules`.

## References

* [The Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE).
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

variable (X : Scheme.{u})

/-- The tensor product of two finitely presented `𝒪_X`-modules is finitely presented. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorObj
    (M N : X.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation] :
    (M ⊗ N).IsFinitePresentation :=
  SheafOfModules.isFinitePresentation_tensorObj (R := X.sheaf)

/-- Finite presentation is a monoidal property of `𝒪_X`-modules, so finitely presented
`𝒪_X`-modules form a monoidal full subcategory of `X.Modules`. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isMonoidal_isFinitePresentation :
    ObjectProperty.IsMonoidal (C := X.Modules)
      (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf) :=
  SheafOfModules.isMonoidal_isFinitePresentation (R := X.sheaf)

/-- The structure sheaf, viewed as a module over itself, is finitely presented. -/
instance AlgebraicGeometry.isFinitePresentation_unit :
    (𝟙_ X.Modules).IsFinitePresentation :=
  @ObjectProperty.prop_unit X.Modules _ (Scheme.Modules.instMonoidalCategory X)
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf)
    (Scheme.Modules.isMonoidal_isFinitePresentation X).toContainsUnit

/-- The explicit structure-sheaf module is finitely presented.
This instance also supports goals that do not use monoidal-unit notation. -/
instance AlgebraicGeometry.isFinitePresentation_structureSheaf :
    (_root_.SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
  AlgebraicGeometry.isFinitePresentation_unit X

namespace AlgebraicGeometry

/-- The monoidal structure of `X.Modules`, stated for the unfolded type
`SheafOfModules X.ringCatSheaf`, which typeclass search does not see through `Scheme.Modules`. -/
local instance monoidalCategorySheafOfModulesForFP :
    MonoidalCategory (_root_.SheafOfModules X.ringCatSheaf) :=
  _root_.AlgebraicGeometry.Scheme.Modules.instMonoidalCategory X

/-- The symmetry of `X.Modules`, stated for the unfolded type `SheafOfModules X.ringCatSheaf`. -/
local instance symmetricCategorySheafOfModulesForFP :
    SymmetricCategory (_root_.SheafOfModules X.ringCatSheaf) :=
  _root_.AlgebraicGeometry.Scheme.Modules.instSymmetricCategory X

/-- Finite presentation is a monoidal property of `SheafOfModules X.ringCatSheaf`, stated for that
unfolded type rather than for `X.Modules`. -/
local instance isMonoidalIsFinitePresentation :
    ObjectProperty.IsMonoidal (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf) :=
  _root_.AlgebraicGeometry.Scheme.Modules.isMonoidal_isFinitePresentation X

/-- The monoidal structure on finitely presented sheaves inherited from `X.Modules`. -/
instance : MonoidalCategory (FinitelyPresentedSheaf X) :=
  @ObjectProperty.fullMonoidalSubcategory X.Modules _
    (_root_.AlgebraicGeometry.Scheme.Modules.instMonoidalCategory X)
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf)
    (_root_.AlgebraicGeometry.Scheme.Modules.isMonoidal_isFinitePresentation X)

/-- The symmetric monoidal structure on finitely presented sheaves inherited from `X.Modules`. -/
instance : SymmetricCategory (FinitelyPresentedSheaf X) :=
  ObjectProperty.fullSymmetricSubcategory _

end AlgebraicGeometry

end

end TauCeti
