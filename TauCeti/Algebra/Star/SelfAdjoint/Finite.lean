/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The self-adjoint part of a finite star module is finite

When `2` is invertible in the scalars, the self-adjoint part `x ↦ ½ (x + star x)`
(`selfAdjointPart`) is a surjective linear map from a star module onto its self-adjoint elements,
so the self-adjoint elements of a finite module form a finite module. In particular, over `ℝ` the
Hermitian (or symmetric) matrices form a finite-dimensional real vector space.
-/

public section

/-- When `2` is invertible in the scalars, the self-adjoint elements of a finite star module form
a finite module: they are the image of the self-adjoint part. -/
instance selfAdjoint.instModuleFinite {R A : Type*} [Semiring R] [StarMul R] [TrivialStar R]
    [Invertible (2 : R)] [AddCommGroup A] [Module R A] [StarAddMonoid A] [StarModule R A]
    [Module.Finite R A] : Module.Finite R (selfAdjoint A) :=
  .of_surjective (selfAdjointPart R) fun x ↦ ⟨x, x.property.selfAdjointPart_apply R⟩
