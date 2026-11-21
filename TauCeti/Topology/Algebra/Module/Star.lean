/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Algebra.Module.Star

/-!
# Continuity of real and imaginary parts on complex star modules

In a topological complex star module `A` with continuous star operation, addition, subtraction,
and scalar multiplication, the real part `ℜ : A →ₗ[ℝ] selfAdjoint A` and imaginary part
`ℑ : A →ₗ[ℝ] selfAdjoint A` are continuous.

## Main results

* `continuous_realPart`: continuity of `realPart : A →ₗ[ℝ] selfAdjoint A`.
* `continuous_imaginaryPart`: continuity of `imaginaryPart : A →ₗ[ℝ] selfAdjoint A`.
-/

public section

open scoped ComplexStarModule

/-- The real part `ℜ : A →ₗ[ℝ] selfAdjoint A` is continuous on any complex star module with
continuous addition, star operation, and real scalar multiplication. -/
@[fun_prop]
theorem continuous_realPart {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A]
    [StarModule ℂ A] [TopologicalSpace A] [ContinuousAdd A] [ContinuousStar A]
    [ContinuousConstSMul ℝ A] : Continuous (realPart (A := A)) :=
  continuous_selfAdjointPart ℝ A

/-- The imaginary part `ℑ : A →ₗ[ℝ] selfAdjoint A` is continuous on any complex star module with
continuous subtraction, star operation, and complex scalar multiplication. -/
@[fun_prop]
theorem continuous_imaginaryPart {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A]
    [StarModule ℂ A] [TopologicalSpace A] [ContinuousSub A] [ContinuousStar A]
    [ContinuousConstSMul ℂ A] : Continuous (imaginaryPart (A := A)) :=
  continuous_induced_rng.mpr <| by
    have h : ((↑) : selfAdjoint A → A) ∘ (imaginaryPart (A := A)) =
        fun a => (-Complex.I) • ((2⁻¹ : ℝ) : ℂ) • (a - star a) := by
      ext a
      rw [Function.comp_apply, imaginaryPart_apply_coe, Complex.coe_smul]
    rw [h]
    exact (continuous_const_smul (-Complex.I)).comp
      ((continuous_const_smul ((2⁻¹ : ℝ) : ℂ)).comp (continuous_id.sub continuous_star))
