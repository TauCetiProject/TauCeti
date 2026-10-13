/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Completion.Basic
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Basic

/-!
# Completed weighted Huber pairs

The structure morphism into the completion of a weighted restricted power-series pair is the
constant-series morphism followed by completion. Its plus ring is the smallest closed,
integrally closed subring containing the constants from the coefficient plus ring and the
weighted variables. Consequently, continuous ring maps out of the completion preserve plus
rings once they do so on these generators. In particular, coefficientwise maps preserve the
completed weighted plus rings.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark and Definition 8.41.
-/

public section

open UniformSpace

namespace TauCeti.Huber.Pair

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {S : Pair A} {k : ℕ} {T : Fin k → Set A}

variable (S) in
/-- **The structure map `(A, A⁺) → (A⟨X⟩_T, A⟨X⟩_T⁺)^`** into the completion of the weighted
restricted power-series pair: the constant series, followed by the completion map. -/
noncomputable def weightedCompletionHom (hT : IsWeightFamily T) :
    Hom S (S.weighted hT).completion :=
  (S.weighted hT).completionHom.comp (S.weightedHom hT)

variable (S) in
/-- The underlying ring homomorphism of the structure map into the completed weighted pair is the
structure map of the `A`-algebra `Â⟨X⟩_T`. -/
@[simp]
theorem Hom.toRingHom_weightedCompletionHom (hT : IsWeightFamily T) :
    (S.weightedCompletionHom hT).toRingHom =
      algebraMap A (Completion (weightedRestrictedSubring T hT)) := by
  ext a
  simp [weightedCompletionHom]

/-! ### The plus ring of a completed weighted pair -/

section CompletedPlus

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  (S : Pair A) {k : ℕ} {T : Fin k → Set A} (hT : IsWeightFamily T)

/-- The completed plus ring of `(A⟨X⟩_T, A⟨X⟩_T⁺)^` contains the constants from `A⁺`. -/
theorem weightedC_mem_weighted_completion_plus {a : A} (ha : a ∈ S.plus) :
    ((weightedC T hT a : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)) ∈ (S.weighted hT).completion.plus := by
  rw [completion_plus]
  exact map_mem_completionPlus (S.weightedC_mem_weighted_plus hT ha)

/-- The completed plus ring of `(A⟨X⟩_T, A⟨X⟩_T⁺)^` contains the weighted variables `t Xᵢ` with
`t ∈ Tᵢ`. -/
theorem weightedC_mul_weightedX_mem_weighted_completion_plus {i : Fin k} {t : A} (ht : t ∈ T i) :
    ((weightedC T hT t * weightedX T hT i : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)) ∈ (S.weighted hT).completion.plus := by
  rw [completion_plus]
  exact map_mem_completionPlus (S.weightedC_mul_weightedX_mem_weighted_plus hT ht)

/-- **The plus ring of the completed pair `(A⟨X⟩_T, A⟨X⟩_T⁺)^` is the smallest closed, integrally
closed subring of the completion containing the constants from `A⁺` and the weighted variables
`t Xᵢ` with `t ∈ Tᵢ`.** Completed form of `TauCeti.Huber.Pair.weighted_plus_le`. -/
theorem weighted_completion_plus_le {Q : Subring (Completion (weightedRestrictedSubring T hT))}
    (hQ : IsClosed (Q : Set (Completion (weightedRestrictedSubring T hT))))
    [IsIntegrallyClosedIn Q (Completion (weightedRestrictedSubring T hT))]
    (hC : ∀ a ∈ S.plus, ((weightedC T hT a : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)) ∈ Q)
    (hX : ∀ i, ∀ t ∈ T i, ((weightedC T hT t * weightedX T hT i : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)) ∈ Q) :
    (S.weighted hT).completion.plus ≤ Q := by
  rw [completion_plus, completionPlus_def]
  exact Subring.topologicalClosure_minimal _ (Subring.map_le_iff_le_comap.mpr <|
    S.weighted_plus_le hT (hQ.preimage (Completion.continuous_coe _)) hC hX) hQ

/-- **Morphisms out of the completed pair `(A⟨X⟩_T, A⟨X⟩_T⁺)^`**: a continuous ring homomorphism
carrying the constants from `A⁺` and the weighted variables `t Xᵢ` (`t ∈ Tᵢ`) into the plus ring
of a Huber pair `(B, B⁺)` carries the whole completed plus ring into `B⁺`. Completed form of
`TauCeti.Huber.Pair.weighted_plus_le_comap`. -/
theorem weighted_completion_plus_le_comap (S' : Pair B)
    {ψ : Completion (weightedRestrictedSubring T hT) →+* B} (hψ : Continuous ψ)
    (hC : ∀ a ∈ S.plus, ψ (weightedC T hT a : weightedRestrictedSubring T hT) ∈ S'.plus)
    (hX : ∀ i, ∀ t ∈ T i,
      ψ (weightedC T hT t * weightedX T hT i : weightedRestrictedSubring T hT) ∈ S'.plus) :
    (S.weighted hT).completion.plus ≤ S'.plus.comap ψ := by
  have := S'.isRingOfIntegralElements.isIntegrallyClosedIn
  exact S.weighted_completion_plus_le hT
    ((S'.plus.toAddSubgroup.isClosed_of_isOpen S'.isRingOfIntegralElements.isOpen).preimage hψ)
    hC hX

variable {S} in
/-- **A morphism of Huber pairs, applied coefficientwise, preserves the completed weighted plus
rings**: for `f : (A, A⁺) → (B, B⁺)` and weights with `f(Tᵢ) ⊆ T'ᵢ`, the induced map
`Â⟨X⟩_T → B̂⟨X⟩_{T'}` carries the plus ring of `(A⟨X⟩_T, A⟨X⟩_T⁺)^` into that of
`(B⟨X⟩_{T'}, B⟨X⟩_{T'}⁺)^`. -/
theorem weighted_completion_plus_le_comap_weightedMapCompletion {U : Pair B} (f : Hom S U)
    {T' : Fin k → Set B} (hT' : IsWeightFamily T') (hTT' : ∀ i, f.toRingHom '' T i ⊆ T' i) :
    (S.weighted hT).completion.plus ≤ (U.weighted hT').completion.plus.comap
      (weightedMapCompletion f.continuous_toRingHom hT hT' hTT') :=
  S.weighted_completion_plus_le_comap hT _ (continuous_weightedMapCompletion ..)
    (fun a ha ↦ by
      rw [weightedMapCompletion_coe, weightedMap_weightedC]
      exact U.weightedC_mem_weighted_completion_plus hT' (f.map_mem_plus a ha))
    (fun i t ht ↦ by
      rw [weightedMapCompletion_coe, map_mul, weightedMap_weightedC, weightedMap_weightedX]
      exact U.weightedC_mul_weightedX_mem_weighted_completion_plus hT' (hTT' i ⟨t, ht, rfl⟩))

end CompletedPlus

end TauCeti.Huber.Pair
