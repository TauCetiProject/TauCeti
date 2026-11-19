/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Symmetry
public import Mathlib.Topology.Instances.Int

/-!
# Checks for completed tensor symmetry

Exchange twice fixes every completed tensor, and exchange preserves the order of subtraction.
The generic checks preserve arbitrary factor plus rings and allow a zero factor. A discrete
product-ring example detects an exchange that is not the identity by evaluating at two
different coordinates.
-/

public section

open TensorProduct TauCeti.Huber

section Generic

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

example (x : CompletedTensor A B C) :
    (CompletedTensor.comm A B C).symm (CompletedTensor.comm A B C x) = x := by
  simp

example (x : CompletedTensor A C B) :
    CompletedTensor.comm A B C ((CompletedTensor.comm A B C).symm x) = x := by
  simp

example (b : B) :
    CompletedTensor.comm A B C (CompletedTensor.inl A B C b) =
      CompletedTensor.inr A C B b := by
  simp

example (c : C) :
    CompletedTensor.comm A B C (CompletedTensor.inr A B C c) =
      CompletedTensor.inl A C B c := by
  simp

example : Continuous (CompletedTensor.comm A B C) :=
  CompletedTensor.continuous_comm A B C

example : IsHomeomorph (CompletedTensor.comm A B C) :=
  CompletedTensor.isHomeomorph_comm A B C

example (x : CompletedTensor A B C) :
    CompletedTensor.comm A C B (CompletedTensor.comm A B C x) = x := by
  rw [← CompletedTensor.comm_symm]
  simp

example (b₁ b₂ : B) (c₁ c₂ : C) :
    CompletedTensor.comm A B C
      (CompletedTensor.toCompletion A B C (b₁ ⊗ₜ[A] c₁) -
        CompletedTensor.toCompletion A B C (b₂ ⊗ₜ[A] c₂)) =
      CompletedTensor.toCompletion A C B (c₁ ⊗ₜ[A] b₁) -
        CompletedTensor.toCompletion A C B (c₂ ⊗ₜ[A] b₂) := by
  simp only [map_sub, CompletedTensor.comm_tmul]

example [Subsingleton B] (x : CompletedTensor A B C) :
    CompletedTensor.comm A B C x = 0 := by
  have := (CompletedTensor.inr A C B).codomain_trivial
  exact Subsingleton.elim _ _

example [IsHuberRing B] [IsHuberRing C] (S : Pair B) (T : Pair C)
    (x : CompletedTensor A B C) :
    CompletedTensor.comm A B C x ∈ (T.completedTensor A S).plus ↔
      x ∈ (S.completedTensor A T).plus := by
  simp

example [IsHuberRing B] [IsHuberRing C] (S : Pair B) (T : Pair C) :
    (S.completedTensor A T).plus.map (CompletedTensor.comm A B C).toRingHom =
      (T.completedTensor A S).plus :=
  Pair.completedTensor.comm_plus A S T

end Generic

section Product

local instance : IsAdicHom (algebraMap ℤ (ℤ × ℤ)) :=
  IsAdicHom.of_discrete_iff.mpr inferInstance

-- Two different coordinate evaluations distinguish exchange from the identity.
example : ∃ x : CompletedTensor ℤ (ℤ × ℤ) (ℤ × ℤ),
    CompletedTensor.comm ℤ (ℤ × ℤ) (ℤ × ℤ) x ≠ x := by
  let φ := RingHom.fst ℤ ℤ
  let ψ := RingHom.snd ℤ ℤ
  have h : φ.comp (algebraMap ℤ (ℤ × ℤ)) = ψ.comp (algebraMap ℤ (ℤ × ℤ)) := by
    ext n
    simp [φ, ψ]
  let χ := CompletedTensor.lift φ ψ h continuous_of_discreteTopology
    continuous_of_discreteTopology
  refine ⟨CompletedTensor.inl ℤ (ℤ × ℤ) (ℤ × ℤ) (0, 1), ?_⟩
  intro heq
  have := congrArg χ heq
  simp [χ, φ, ψ] at this

end Product
