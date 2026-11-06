/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Restricted.Basic
public import TauCeti.RingTheory.Huber.TensorProduct.Pair
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Completion

/-!
# Completed base change of weighted restricted Huber pairs

The topological ring equivalence `CompletedTensor.weightedRestrictedEquiv` identifies
`A⟨X⟩_T ⊗̂_A B` with `B⟨X⟩_{λ(T)}` for an adic coefficient map `λ : A → B`.
This file proves that it identifies their specified rings of integral elements as well,
provided `λ` preserves the coefficient plus rings. Thus the comparison is one of complete
Huber pairs, not just of topological rings. The mutually inverse pair morphisms
`completedTensor.toWeighted` and `completedTensor.ofWeighted` bundle this comparison.
This is the restricted-series model for base change of affinoid presentations.

The proof uses the existing generator criteria for the two plus rings: constants from
the coefficient plus ring and the weighted variables generate the completed weighted
plus ring as a closed integrally closed subring. Neither uniformity nor sheafiness is
assumed, and neither plus ring is replaced by the full power-bounded subring.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Lemma 3.5(i) and the proof of Proposition 3.7.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, §1.2,
  proof of Proposition 1.2.2.
-/

public section

open UniformSpace

namespace TauCeti.Huber.Pair

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [Algebra A B] [hAB : IsAdicHom (algebraMap A B)] {T : Fin k → Set A}
  (S : Pair A) (U : Pair B) (hT : IsWeightFamily T)
  (hplus : S.plus ≤ U.plus.comap (algebraMap A B))

namespace completedTensor

/-- Completed base change of weighted restricted series as a morphism of Huber pairs,
for a coefficient map preserving the chosen plus rings. -/
noncomputable def toWeighted :
    Hom (((S.weighted hT).completion).completedTensor A U)
      (U.weighted (hAB.isWeightFamily_image hT)).completion where
  toRingHom := (CompletedTensor.weightedRestrictedEquiv B hT).toRingHom
  continuous_toRingHom := CompletedTensor.continuous_weightedRestrictedEquiv B hT
  map_mem_plus := by
    let V := (U.weighted (hAB.isWeightFamily_image hT)).completion
    -- The forward map preserves the plus rings of both tensor factors.
    have := V.isRingOfIntegralElements.isIntegrallyClosedIn
    refine ((S.weighted hT).completion).completedTensor_plus_le_comap U
      (V.plus.toAddSubgroup.isClosed_of_isOpen V.isRingOfIntegralElements.isOpen)
      (CompletedTensor.continuous_weightedRestrictedEquiv B hT) ?_ ?_
    · intro f hf
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [CompletedTensor.weightedRestrictedEquiv_inl]
      let φ : Hom S U :=
        { toRingHom := algebraMap A B
          continuous_toRingHom := hAB.continuous
          map_mem_plus := hplus }
      exact weighted_completion_plus_le_comap_weightedMapCompletion hT φ
        (hAB.isWeightFamily_image hT) (fun _ ↦ subset_rfl) hf
    · intro b hb
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [CompletedTensor.weightedRestrictedEquiv_inr,
        algebraMap_completion_weightedRestrictedSubring_apply]
      exact U.weightedC_mem_weighted_completion_plus _ hb

/-- The inverse restricted-series comparison as a morphism of Huber pairs.
It preserves plus rings without a compatibility assumption on the coefficient plus rings. -/
noncomputable def ofWeighted :
    Hom (U.weighted (hAB.isWeightFamily_image hT)).completion
      (((S.weighted hT).completion).completedTensor A U) where
  toRingHom := (CompletedTensor.weightedRestrictedEquiv B hT).symm.toRingHom
  continuous_toRingHom := CompletedTensor.continuous_weightedRestrictedEquiv_symm B hT
  map_mem_plus := by
    let W := ((S.weighted hT).completion).completedTensor A U
    -- Test the inverse on integral constants and weighted variables.
    refine U.weighted_completion_plus_le_comap _ W
      (CompletedTensor.continuous_weightedRestrictedEquiv_symm B hT) ?_ ?_
    · intro b hb
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [CompletedTensor.weightedRestrictedEquiv_symm_weightedC]
      exact ((S.weighted hT).completion).inr_mem_completedTensor_plus U hb
    · rintro i _ ⟨t, ht, rfl⟩
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      -- A base scalar has the same image through either tensor inclusion, so the
      -- inverse of the weighted variable λ(t)Xᵢ is the left image of tXᵢ.
      have he : (CompletedTensor.weightedRestrictedEquiv B hT).symm
          ((weightedC _ (hAB.isWeightFamily_image hT) (algebraMap A B t) *
            weightedX _ (hAB.isWeightFamily_image hT) i :
            weightedRestrictedSubring _ (hAB.isWeightFamily_image hT)) : Completion _) =
          CompletedTensor.inl A (Completion (weightedRestrictedSubring T hT)) B
            (weightedC T hT t * weightedX T hT i : weightedRestrictedSubring T hT) := by
        simp only [Completion.coe_mul, map_mul,
          CompletedTensor.weightedRestrictedEquiv_symm_weightedC,
          CompletedTensor.weightedRestrictedEquiv_symm_weightedX,
          CompletedTensor.inr_algebraMap, ← CompletedTensor.inl_algebraMap,
          algebraMap_completion_weightedRestrictedSubring_apply]
      rw [he]
      exact ((S.weighted hT).completion).inl_mem_completedTensor_plus U
        (S.weightedC_mul_weightedX_mem_weighted_completion_plus hT ht)

/-- The underlying ring map of the forward restricted-series comparison. -/
@[simp]
theorem toRingHom_toWeighted :
    (toWeighted S U hT hplus).toRingHom =
      (CompletedTensor.weightedRestrictedEquiv B hT).toRingHom := (rfl)

/-- The underlying ring map of the inverse restricted-series comparison. -/
@[simp]
theorem toRingHom_ofWeighted :
    (ofWeighted S U hT).toRingHom =
      (CompletedTensor.weightedRestrictedEquiv B hT).symm.toRingHom := (rfl)

/-- The inverse comparison is a left inverse as a morphism of Huber pairs. -/
@[simp]
theorem ofWeighted_comp_toWeighted :
    (ofWeighted S U hT).comp (toWeighted S U hT hplus) = Hom.id _ := by
  ext x
  simp

/-- The inverse comparison is a right inverse as a morphism of Huber pairs. -/
@[simp]
theorem toWeighted_comp_ofWeighted :
    (toWeighted S U hT hplus).comp (ofWeighted S U hT) = Hom.id _ := by
  ext x
  simp

end completedTensor

include hplus

/-- The restricted-series base-change equivalence maps the completed tensor plus ring
onto the completed weighted-series plus ring. -/
theorem map_plus_weightedRestrictedEquiv :
    (((S.weighted hT).completion).completedTensor A U).plus.map
        (CompletedTensor.weightedRestrictedEquiv B hT).toRingHom =
      (U.weighted (hAB.isWeightFamily_image hT)).completion.plus := by
  apply le_antisymm (Subring.map_le_iff_le_comap.mpr
    (completedTensor.toWeighted S U hT hplus).map_mem_plus)
  intro y hy
  exact ⟨(CompletedTensor.weightedRestrictedEquiv B hT).symm y,
    (completedTensor.ofWeighted S U hT).map_mem_plus y hy,
    (CompletedTensor.weightedRestrictedEquiv B hT).apply_symm_apply y⟩

/-- Membership in the tensor plus ring is tested in the completed weighted-series plus ring
using the restricted-series comparison. -/
@[simp]
theorem mem_completedTensor_plus_iff_weightedRestrictedEquiv
    (x : CompletedTensor A (Completion (weightedRestrictedSubring T hT)) B) :
    x ∈ (((S.weighted hT).completion).completedTensor A U).plus ↔
      CompletedTensor.weightedRestrictedEquiv B hT x ∈
        (U.weighted (hAB.isWeightFamily_image hT)).completion.plus := by
  rw [← map_plus_weightedRestrictedEquiv S U hT hplus]
  exact (CompletedTensor.weightedRestrictedEquiv B hT).injective.mem_set_image.symm

end TauCeti.Huber.Pair
