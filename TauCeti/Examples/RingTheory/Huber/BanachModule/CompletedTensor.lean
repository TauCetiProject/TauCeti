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
zero factor on the whole completion. The unit isomorphism `lid` evaluates scalar multiples and
kills everything when the module is zero; the comparison `finiteProjectiveEquiv` is zero in rank
zero, recovers Mathlib's algebraic unit map in rank one, and keeps signs in rank two.
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
    CompletedTensor.lift (LinearMap.mul A A) (continuous_mul.congr fun _ ↦ by simp)
      (CompletedTensor.tmul A A A a b - CompletedTensor.tmul A A A c d) = a * b - c * d := by
  simp

/-- The zero bilinear map lifts to the zero map on the whole completion. -/
example :
    CompletedTensor.lift (0 : A →ₗ[A] A →ₗ[A] A) (continuous_zero.congr fun _ ↦ by simp) = 0 :=
  CompletedTensor.ext fun v w ↦ by simp

end Ring

section Unit

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  {M : Type*} [AddCommGroup M] [Module A M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [ContinuousSMul A M] [CompleteSpace M] [T0Space M]

/-- The completed tensor unit map sends `a ⊗ v - b ⊗ w` to `a • v - b • w`. -/
example (a b : A) (v w : M) :
    CompletedTensor.lid A M (CompletedTensor.tmul A A M a v - CompletedTensor.tmul A A M b w) =
      a • v - b • w := by
  simp

/-- The inverse of the unit map sends `w` to `1 ⊗ w`. -/
example (w : M) : (CompletedTensor.lid A M).symm w = CompletedTensor.tmul A A M 1 w := by
  simp

/-- For a zero module, every completed tensor and its image under the unit map are zero. -/
example [Subsingleton M] (x : CompletedTensor A A M) : x = 0 ∧ CompletedTensor.lid A M x = 0 :=
  ⟨(CompletedTensor.lid A M).injective (Subsingleton.elim _ _), Subsingleton.elim _ _⟩

variable [IsTopologicalRing A]

/-- In rank zero, the comparison sends the only algebraic tensor to zero. -/
example (x : (Fin 0 → A) ⊗[A] M) :
    CompletedTensor.finiteProjectiveEquiv A (Fin 0 → A) M x = 0 := by
  rw [Subsingleton.elim x 0, map_zero]

/-- In rank one, following the comparison by the completed unit map is Mathlib's algebraic unit
map. -/
example (x : A ⊗[A] M) :
    CompletedTensor.lid A M (CompletedTensor.finiteProjectiveEquiv A A M x) =
      TensorProduct.lid A M x := by
  simp

/-- In rank two, the comparison sends `e₀ ⊗ v - e₁ ⊗ w` to the same two completed elementary
tensors, with their signs. -/
example (v w : M) :
    CompletedTensor.finiteProjectiveEquiv A (Fin 2 → A) M
        (Pi.single 0 1 ⊗ₜ v - Pi.single 1 1 ⊗ₜ w) =
      CompletedTensor.tmul A (Fin 2 → A) M (Pi.single 0 1) v -
        CompletedTensor.tmul A (Fin 2 → A) M (Pi.single 1 1) w := by
  simp

end Unit
