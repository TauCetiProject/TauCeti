/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Map

/-!
# Using the functoriality of completed tensor products

The induced map of completed tensor rings computes on algebraic tensors through the public
`simp` set, fixes every element for identity data, and is zero when the target has a zero
factor.
-/

public section

open TensorProduct TauCeti.Huber

variable {A B C A' B' C' : Type*}
  [CommRing A] [CommRing B] [CommRing C] [CommRing A'] [CommRing B'] [CommRing C']
  [Algebra A B] [Algebra A C] [Algebra A' B'] [Algebra A' C']
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [TopologicalSpace A'] [TopologicalSpace B'] [TopologicalSpace C']
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsTopologicalRing A'] [IsTopologicalRing B'] [IsTopologicalRing C']
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [IsAdicHom (algebraMap A' B')] [IsAdicHom (algebraMap A' C')]
  (α : A →+* A') (φ : B →+* B') (ψ : C →+* C')
  (hφ : φ.comp (algebraMap A B) = (algebraMap A' B').comp α)
  (hψ : ψ.comp (algebraMap A C) = (algebraMap A' C').comp α)
  (hφc : Continuous φ) (hψc : Continuous ψ)

-- A difference of pure tensors maps to the difference of the image tensors, in order.
example (b₁ b₂ : B) (c₁ c₂ : C) :
    CompletedTensor.map α φ ψ hφ hψ hφc hψc
        (CompletedTensor.toCompletion A B C (b₁ ⊗ₜ c₁ - b₂ ⊗ₜ c₂)) =
      CompletedTensor.toCompletion A' B' C' (φ b₁ ⊗ₜ ψ c₁ - φ b₂ ⊗ₜ ψ c₂) := by
  simp

-- Identity data fix every element of the completed tensor ring, not only algebraic tensors.
example (x : CompletedTensor A B C) :
    CompletedTensor.map (RingHom.id A) (RingHom.id B) (RingHom.id C) rfl rfl continuous_id
      continuous_id x = x := by
  simp

-- A zero right target factor forces the induced map to be zero.
example [Subsingleton C'] (x : CompletedTensor A B C) :
    CompletedTensor.map α φ ψ hφ hψ hφc hψc x = 0 :=
  haveI := (CompletedTensor.inr A' B' C').codomain_trivial
  Subsingleton.elim _ _
