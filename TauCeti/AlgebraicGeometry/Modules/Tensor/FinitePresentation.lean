/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Monoidal
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product

/-!
# Tensor products of finitely presented `𝒪ₓ`-modules

Specializing the site-level closure result for tensor products of sheaves of modules
(`TauCeti.SheafOfModules.isFinitePresentation_tensorObj`) to the structure sheaf of a scheme `X`,
tensor products of `𝒪ₓ`-modules preserve finite presentation.

## Main declaration

* `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorObj`: the tensor product of two
  finitely presented `𝒪ₓ`-modules is finitely presented.
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace TauCeti

universe v

noncomputable section

variable (X : Scheme.{v})

/-- The tensor product of two finitely presented `𝒪ₓ`-modules is finitely presented. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorObj (M N : X.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation] : (M ⊗ N).IsFinitePresentation :=
  SheafOfModules.isFinitePresentation_tensorObj (R := X.sheaf)

end

end TauCeti
