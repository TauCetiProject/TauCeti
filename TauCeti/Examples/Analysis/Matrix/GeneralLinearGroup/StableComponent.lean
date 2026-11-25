/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.GeneralLinearGroup.StableComponent.FiniteDimensional

/-!
# Checks for the stable component group of finite-dimensional C⋆-algebras

For a finite-dimensional C⋆-algebra `A` every unitary is joined to `1`, so `K₁(A) = 0`; here for
`ℂ³` and for `M₂(ℂ)`.
-/

public section

-- `CStarMatrix (Fin 2) (Fin 2) ℂ` is a C⋆-algebra for the order on `ℂ`.
open scoped ComplexOrder

namespace TauCeti.StableComponentExample

/-- The stable component group of the finite-dimensional C⋆-algebra `ℂ³` is trivial. -/
example : Subsingleton (StableComponentGroup (Fin 3 → ℂ)) :=
  inferInstance

/-- The stable component group of the finite-dimensional C⋆-algebra `M₂(ℂ)` is trivial. -/
example : Subsingleton (StableComponentGroup (CStarMatrix (Fin 2) (Fin 2) ℂ)) :=
  inferInstance

end TauCeti.StableComponentExample
