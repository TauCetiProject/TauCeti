/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.RingTheory.SplitAlgebra.Basic

/-!
# Examples of split algebras

Evaluation at zero splits a polynomial algebra, and first projection splits a diagonal
product algebra. Real part splits the complex numbers over the reals, despite not being
multiplicative. The product example also illustrates stability under base change and tensor
purity.
-/

public section

open TauCeti TensorProduct

example (R : Type*) [CommSemiring R] : SplitAlgebra R (Polynomial R) :=
  SplitAlgebra.of_map_one (Polynomial.aeval (0 : R)).toLinearMap (by simp)

example (R : Type*) [CommSemiring R] : SplitAlgebra R (R × R) :=
  SplitAlgebra.of_map_one (LinearMap.fst R R R) rfl

example : Function.LeftInverse Complex.reLm (algebraMap ℝ ℂ) ∧
    Complex.reLm (Complex.I * Complex.I) ≠ Complex.reLm Complex.I * Complex.reLm Complex.I :=
  ⟨fun r ↦ by simp, by simp⟩

example (R : Type*) [CommSemiring R] :
    SplitAlgebra R (Polynomial R × Polynomial R) := by
  have h : SplitAlgebra R (Polynomial R) :=
    SplitAlgebra.of_map_one (Polynomial.aeval (0 : R)).toLinearMap (by simp)
  exact SplitAlgebra.of_algHom (AlgHom.fst R (Polynomial R) (Polynomial R)) h

example (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] :
    SplitAlgebra A (A ⊗[R] (R × R)) := by
  have h : SplitAlgebra R (R × R) :=
    SplitAlgebra.of_map_one (LinearMap.fst R R R) rfl
  exact SplitAlgebra.baseChange A h

example (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M] :
    Function.Injective (fun m : M ↦ m ⊗ₜ[R] (1 : R × R)) := by
  have h : SplitAlgebra R (R × R) :=
    SplitAlgebra.of_map_one (LinearMap.fst R R R) rfl
  exact h.tmul_one_injective M
