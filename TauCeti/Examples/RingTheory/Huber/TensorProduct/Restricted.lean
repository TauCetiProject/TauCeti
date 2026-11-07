/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Restricted.Pair

/-!
# Checks for completed base change of weighted restricted power series

The isomorphism `A⟨X⟩_T ⊗̂_A B ≃ B⟨X⟩_{λ(T)}` computes on completed pure tensors, sends
constants to the right factor, fixes the variables, and is inverse to its symmetric map. The
checks are stated for arbitrary weights, and use the simp normal forms of the API.
The plus-ring checks retain arbitrary compatible coefficient plus rings and test the inverse
comparison on constants and on differences of weighted variables.
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

variable (S : Pair A) (U : Pair B)
  (hplus : S.plus ≤ U.plus.comap (algebraMap A B))

-- The bundled maps are inverse morphisms, not only inverse functions.
example :
    (Pair.completedTensor.ofWeighted S U hT).comp
      (Pair.completedTensor.toWeighted S U hT hplus) = Pair.Hom.id _ := by
  simp

example :
    (Pair.completedTensor.toWeighted S U hT hplus).comp
      (Pair.completedTensor.ofWeighted S U hT) = Pair.Hom.id _ := by
  simp

-- The projection API computes without unfolding the bundled maps.
example (b : B) :
    (Pair.completedTensor.toWeighted S U hT hplus).toRingHom
        (CompletedTensor.inr A (Completion (weightedRestrictedSubring T hT)) B b) =
      algebraMap B (Completion (weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
        (hAB.isWeightFamily_image hT))) b := by
  simp

-- Membership is reflected on the entire completion, not only on elementary tensors.
example (y : Completion (weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
    (hAB.isWeightFamily_image hT))) :
    (CompletedTensor.weightedRestrictedEquiv B hT).symm y ∈
        (((S.weighted hT).completion).completedTensor A U).plus ↔
      y ∈ (U.weighted (hAB.isWeightFamily_image hT)).completion.plus := by
  simp only [Pair.mem_completedTensor_plus_iff_weightedRestrictedEquiv S U hT hplus,
    RingEquiv.apply_symm_apply]

-- A constant from the new coefficient plus ring lifts to the tensor plus ring.
example {b : B} (hb : b ∈ U.plus) :
    (CompletedTensor.weightedRestrictedEquiv B hT).symm
        (weightedC _ (hAB.isWeightFamily_image hT) b : weightedRestrictedSubring _ _) ∈
      (((S.weighted hT).completion).completedTensor A U).plus := by
  rw [Pair.mem_completedTensor_plus_iff_weightedRestrictedEquiv S U hT hplus,
    RingEquiv.apply_symm_apply]
  exact U.weightedC_mem_weighted_completion_plus _ hb

-- The comparison transports differences of weighted variables, retaining their signs.
example (i j : Fin k) {t u : A} (ht : t ∈ T i) (hu : u ∈ T j) :
    (CompletedTensor.weightedRestrictedEquiv B hT).symm
        ((weightedC _ (hAB.isWeightFamily_image hT) (algebraMap A B t) *
          weightedX _ (hAB.isWeightFamily_image hT) i -
          weightedC _ (hAB.isWeightFamily_image hT) (algebraMap A B u) *
          weightedX _ (hAB.isWeightFamily_image hT) j : weightedRestrictedSubring _ _) :
          Completion _) ∈ (((S.weighted hT).completion).completedTensor A U).plus := by
  rw [Pair.mem_completedTensor_plus_iff_weightedRestrictedEquiv S U hT hplus,
    RingEquiv.apply_symm_apply, Completion.coe_sub]
  exact sub_mem (U.weightedC_mul_weightedX_mem_weighted_completion_plus _ ⟨t, ht, rfl⟩)
    (U.weightedC_mul_weightedX_mem_weighted_completion_plus _ ⟨u, hu, rfl⟩)

end Generic
