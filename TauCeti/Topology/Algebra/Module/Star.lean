/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Algebra.Module.Star

/-!
# Continuity of the imaginary part on complex star modules

In a topological complex star module `A` with continuous star operation, subtraction, and complex
scalar multiplication, the imaginary part `ℑ : A →ₗ[ℝ] selfAdjoint A` is continuous.

## Main results

* `TauCeti.continuous_imaginaryPart`: continuity of `imaginaryPart : A →ₗ[ℝ] selfAdjoint A`.
-/

public section

open scoped ComplexStarModule

namespace TauCeti

/-- The imaginary part `ℑ : A →ₗ[ℝ] selfAdjoint A` is continuous on any complex star module with
continuous subtraction, star operation, and complex scalar multiplication. -/
@[fun_prop]
theorem continuous_imaginaryPart {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A]
    [StarModule ℂ A] [TopologicalSpace A] [ContinuousSub A] [ContinuousStar A]
    [ContinuousConstSMul ℂ A] : Continuous (imaginaryPart (A := A)) := by
  have : ContinuousConstSMul ℝ A :=
    ⟨fun r => by simpa only [← Complex.coe_smul] using continuous_const_smul (r : ℂ)⟩
  have hnegI : Continuous (skewAdjoint.negISMul (A := A)) :=
    ((continuous_const_smul (-Complex.I)).comp continuous_subtype_val).subtype_mk _
  exact hnegI.comp (continuous_skewAdjointPart ℝ A)

end TauCeti
