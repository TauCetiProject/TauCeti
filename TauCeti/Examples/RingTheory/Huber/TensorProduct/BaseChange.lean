/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.BaseChange

/-!
# Checks for successive completed base change

These checks exercise the comparison from an importing module: its formula on differences
of tensors, its inverse, zero factors, and preservation of arbitrary plus rings. The discrete
example uses the first projection `ℤ × ℤ → ℤ`; an intermediate scalar in its kernel dies,
whereas the other coordinate survives.
-/

public section

namespace TauCeti.Examples.CompletedTensorBaseChange

open TensorProduct Topology TauCeti.Huber CompletedTensor

attribute [local instance] CompletedTensor.rightAlgebra CompletedTensor.isAdicHom_rightAlgebra

section Generic

variable (A B C D : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D] [Algebra C D] [IsScalarTower A C D]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C] [IsTopologicalRing D]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [IsAdicHom (algebraMap C D)]

example (b₁ b₂ : B) (c₁ c₂ : C) (d₁ d₂ : D) :
    let _ : IsAdicHom (algebraMap A D) := by
      rw [IsScalarTower.algebraMap_eq A C D]
      exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
    cancelBaseChange A B C D
      (toCompletion C (CompletedTensor A B C) D
          (toCompletion A B C (b₁ ⊗ₜ[A] c₁) ⊗ₜ[C] d₁) -
        toCompletion C (CompletedTensor A B C) D
          (toCompletion A B C (b₂ ⊗ₜ[A] c₂) ⊗ₜ[C] d₂)) =
      toCompletion A B D (b₁ ⊗ₜ[A] (algebraMap C D c₁ * d₁)) -
        toCompletion A B D (b₂ ⊗ₜ[A] (algebraMap C D c₂ * d₂)) := by
  intro hAD
  simp only [map_sub, cancelBaseChange_tmul]

example (b : B) (d : D) :
    let _ : IsAdicHom (algebraMap A D) := by
      rw [IsScalarTower.algebraMap_eq A C D]
      exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
    (cancelBaseChange A B C D).symm (toCompletion A B D (b ⊗ₜ[A] d)) =
      toCompletion C (CompletedTensor A B C) D
        (toCompletion A B C (b ⊗ₜ[A] (1 : C)) ⊗ₜ[C] d) := by
  intro hAD
  exact cancelBaseChange_symm_tmul A B C D b d

example [Subsingleton B] (x : CompletedTensor C (CompletedTensor A B C) D) :
    cancelBaseChange A B C D x = 0 := by
  have : IsAdicHom (algebraMap A D) := by
    rw [IsScalarTower.algebraMap_eq A C D]
    exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
  have := (inl A B D).codomain_trivial
  exact Subsingleton.elim _ _

example [IsHuberRing B] [IsHuberRing C] [IsHuberRing D]
    (S : Pair B) (T : Pair C) (U : Pair D)
    (hCD : T.plus ≤ U.plus.comap (algebraMap C D)) :
    let _ : IsAdicHom (algebraMap A D) := by
      rw [IsScalarTower.algebraMap_eq A C D]
      exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
    ∀ x : CompletedTensor A B D,
      (cancelBaseChange A B C D).symm x ∈ ((S.completedTensor A T).completedTensor C U).plus ↔
      x ∈ (S.completedTensor A U).plus := by
  intro hAD x
  simpa using (Pair.completedTensor.cancelBaseChange_mem_plus A B C D S T U hCD
    ((cancelBaseChange A B C D).symm x)).symm

end Generic

section Projection

/-- The first projection supplies the noninjective scalar extension in these checks. -/
local instance projectionAlgebra : Algebra (ℤ × ℤ) ℤ := (RingHom.fst ℤ ℤ).toAlgebra

local instance : IsAdicHom (algebraMap ℤ ℤ) := by
  simpa using (IsAdicHom.id (A := ℤ))

local instance : IsAdicHom (algebraMap ℤ (ℤ × ℤ)) :=
  IsAdicHom.of_discrete_iff.mpr inferInstance

local instance : IsAdicHom (algebraMap (ℤ × ℤ) ℤ) :=
  IsAdicHom.of_discrete_iff.mpr inferInstance

-- Cancellation uses the specified coefficient homomorphism, not an identity on scalars.
example :
    cancelBaseChange ℤ ℤ (ℤ × ℤ) ℤ
      (inl (ℤ × ℤ) (CompletedTensor ℤ ℤ (ℤ × ℤ)) ℤ (inr ℤ ℤ (ℤ × ℤ) (0, 1))) = 0 := by
  simp [RingHom.algebraMap_toAlgebra]

example :
    cancelBaseChange ℤ ℤ (ℤ × ℤ) ℤ
      (inl (ℤ × ℤ) (CompletedTensor ℤ ℤ (ℤ × ℤ)) ℤ (inr ℤ ℤ (ℤ × ℤ) (1, 0))) ≠ 0 := by
  have := (lift (A := ℤ) (RingHom.id ℤ) (RingHom.id ℤ) rfl
    continuous_of_discreteTopology continuous_of_discreteTopology).domain_nontrivial
  simp [RingHom.algebraMap_toAlgebra]

end Projection

end TauCeti.Examples.CompletedTensorBaseChange
