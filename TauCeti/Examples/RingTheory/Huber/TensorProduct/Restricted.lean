/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Restricted

/-!
# Checks for completed base change of weighted restricted power series

The isomorphism `A⟨X⟩_T ⊗̂_A B ≃ B⟨X⟩_{λ(T)}` computes on completed pure tensors, sends
constants to the right factor, fixes the variables, and is inverse to its symmetric map. The
checks are stated for arbitrary weights, and use the simp normal forms of the API.
-/

public section

open UniformSpace TensorProduct TauCeti.Huber

section Generic

variable {k : ℕ} {A : Type*} (B : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [Algebra A B] [hAB : IsAdicHom (algebraMap A B)] {T : Fin k → Set A} (hT : IsWeightFamily T)

-- A completed pure tensor `f ⊗ b` goes to `λ(f) · b`.
example (f : Completion (weightedRestrictedSubring T hT)) (b : B) :
    CompletedTensor.weightedRestrictedEquiv B hT
        (CompletedTensor.toCompletion _ _ _ (f ⊗ₜ[A] b)) =
      weightedMapCompletion hAB.continuous hT (hAB.isWeightFamily_image hT)
          (fun _ ↦ subset_rfl) f *
        algebraMap B (Completion (weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
          (hAB.isWeightFamily_image hT))) b := by
  simp

-- The inverse, read on the structure map of `B`, is the right coprojection.
example (b : B) :
    (CompletedTensor.weightedRestrictedEquiv B hT).symm
        (algebraMap B (Completion (weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
          (hAB.isWeightFamily_image hT))) b) =
      CompletedTensor.inr A (Completion (weightedRestrictedSubring T hT)) B b := by
  simp

-- The variable `Xᵢ ⊗ 1` goes to `Xᵢ`.
example (i : Fin k) :
    CompletedTensor.weightedRestrictedEquiv B hT
        (CompletedTensor.inl A (Completion (weightedRestrictedSubring T hT)) B
          (weightedX T hT i : weightedRestrictedSubring T hT)) =
      (weightedX _ (hAB.isWeightFamily_image hT) i :
        weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
          (hAB.isWeightFamily_image hT)) := by
  simp

example (x : CompletedTensor A (Completion (weightedRestrictedSubring T hT)) B) :
    (CompletedTensor.weightedRestrictedEquiv B hT).symm
      (CompletedTensor.weightedRestrictedEquiv B hT x) = x := by
  simp

example : IsHomeomorph (CompletedTensor.weightedRestrictedEquiv B hT) :=
  CompletedTensor.isHomeomorph_weightedRestrictedEquiv B hT

end Generic
