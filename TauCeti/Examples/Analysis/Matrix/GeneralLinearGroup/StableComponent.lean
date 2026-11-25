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
`ℂ³` and for `M₂(ℂ)`. The polar unitary of the invertible element `2 ∈ ℂ` is `1`.
-/

public section

open scoped ComplexOrder

namespace TauCeti.StableComponentExample

/-- The stable component group of the finite-dimensional C⋆-algebra `ℂ³` is trivial. -/
example : Subsingleton (StableComponentGroup (Fin 3 → ℂ)) :=
  StableComponentGroup.subsingleton_of_finiteDimensional

/-- The stable component group of the finite-dimensional C⋆-algebra `M₂(ℂ)` is trivial. -/
example : Subsingleton (StableComponentGroup (CStarMatrix (Fin 2) (Fin 2) ℂ)) := by
  have : FiniteDimensional ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
    LinearEquiv.finiteDimensional (CStarMatrix.ofMatrixₗ (R := ℂ))
  exact StableComponentGroup.subsingleton_of_finiteDimensional

/-- The polar unitary of the invertible element `2 ∈ ℂ` is `1`. -/
example : (Units.mk0 (2 : ℂ) two_ne_zero).polarUnitary = 1 :=
  Units.polarUnitary_eq_one (by norm_num)

end TauCeti.StableComponentExample
