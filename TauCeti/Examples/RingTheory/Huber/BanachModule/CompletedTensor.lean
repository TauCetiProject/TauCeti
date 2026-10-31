/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.BanachModule.CompletedTensor
public import Mathlib.Algebra.Algebra.Bilinear

/-!
# Checks for the completed tensor product of topological modules

The elementary tensor map is the completion image of the algebraic tensor, so it respects signs
and vanishes on a zero factor. Lifting multiplication of a complete nonarchimedean ring evaluates
products, the zero bilinear map lifts to zero, and the functor `map` cancels two signs and kills a
zero factor on the whole completion.
-/

public section

open TensorProduct TauCeti.Huber BanachModule

section Generic

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  {V : Type*} [AddCommGroup V] [Module A V] [TopologicalSpace V]
  {W : Type*} [AddCommGroup W] [Module A W] [TopologicalSpace W]

/-- A zero first factor gives the zero tensor. -/
example (w : W) : CompletedTensor.tmul A V W 0 w = 0 := by
  simp

/-- The difference of two elementary tensors is the completion image of the algebraic difference,
with the same signs. -/
example (v₁ v₂ : V) (w₁ w₂ : W) :
    CompletedTensor.tmul A V W v₁ w₁ - CompletedTensor.tmul A V W v₂ w₂ =
      CompletedTensor.toCompletion A V W (v₁ ⊗ₜ[A] w₁ - v₂ ⊗ₜ[A] w₂) := by
  simp

variable [IsTopologicalRing A] [IsTopologicalAddGroup V] [IsTopologicalAddGroup W]

/-- Negating both factors sends `v ⊗ w` back to `v ⊗ w`. -/
example (v : V) (w : W) :
    CompletedTensor.map (-ContinuousLinearMap.id A V) (-ContinuousLinearMap.id A W)
      (CompletedTensor.tmul A V W v w) = CompletedTensor.tmul A V W v w := by
  simp

/-- Tensoring a zero map with the identity is zero on the whole completion. -/
example : CompletedTensor.map (0 : V →L[A] V) (ContinuousLinearMap.id A W) = 0 :=
  CompletedTensor.ext fun v w ↦ by simp

end Generic

section Ring

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A] [T2Space A]

/-- Lifting the multiplication of a complete nonarchimedean ring sends `a ⊗ b - c ⊗ d` to
`ab - cd`. -/
example (a b c d : A) :
    CompletedTensor.lift (LinearMap.mul A A) (continuous_mul.congr fun _ ↦ rfl)
      (CompletedTensor.tmul A A A a b - CompletedTensor.tmul A A A c d) = a * b - c * d := by
  simp

/-- The zero bilinear map lifts to the zero map on the whole completion. -/
example :
    CompletedTensor.lift (0 : A →ₗ[A] A →ₗ[A] A) (continuous_const.congr fun _ ↦ rfl) = 0 :=
  CompletedTensor.ext fun v w ↦ by simp

end Ring
