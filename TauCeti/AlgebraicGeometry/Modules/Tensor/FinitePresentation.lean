/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.FiniteType
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product

/-!
# Tensor products of finite-type and finitely presented `𝒪ₓ`-modules

Specializing the site-level closure results for tensor products of sheaves of modules
(`TauCeti.SheafOfModules.isFiniteType_tensorObj`,
`TauCeti.SheafOfModules.isFinitePresentation_tensorObj`, and
`TauCeti.SheafOfModules.isMonoidal_isFinitePresentation`) to the structure sheaf of a scheme `X`,
tensor products of `𝒪ₓ`-modules preserve finite type and finite presentation.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isFiniteType_tensorObj`: the tensor product of two
  `𝒪ₓ`-modules of finite type is of finite type;
* `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorObj`: the tensor product of two
  finitely presented `𝒪ₓ`-modules is finitely presented;
* `AlgebraicGeometry.Scheme.Modules.isMonoidal_isFinitePresentation`: finite presentation is a
  monoidal property of `𝒪ₓ`-modules.
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace TauCeti

universe v

noncomputable section

variable (X : Scheme.{v})

/-- The tensor product of two `𝒪ₓ`-modules of finite type is of finite type. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isFiniteType_tensorObj (M N : X.Modules)
    [M.IsFiniteType] [N.IsFiniteType] : (M ⊗ N).IsFiniteType :=
  SheafOfModules.isFiniteType_tensorObj (R := X.sheaf)

/-- The tensor product of two finitely presented `𝒪ₓ`-modules is finitely presented. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorObj (M N : X.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation] : (M ⊗ N).IsFinitePresentation :=
  SheafOfModules.isFinitePresentation_tensorObj (R := X.sheaf)

/-- Finite presentation is a monoidal property of `𝒪ₓ`-modules. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isMonoidal_isFinitePresentation :
    ObjectProperty.IsMonoidal (C := X.Modules)
      (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf) :=
  SheafOfModules.isMonoidal_isFinitePresentation (R := X.sheaf)

end

end TauCeti
