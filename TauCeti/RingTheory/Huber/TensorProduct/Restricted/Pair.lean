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
Huber pairs, not just of topological rings. This is the restricted-series model for base
change of affinoid presentations.

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

include hplus

/-- The restricted-series base-change equivalence maps the completed tensor plus ring
onto the completed weighted-series plus ring. -/
theorem map_plus_weightedRestrictedEquiv :
    (((S.weighted hT).completion).completedTensor A U).plus.map
        (CompletedTensor.weightedRestrictedEquiv B hT).toRingHom =
      (U.weighted (hAB.isWeightFamily_image hT)).completion.plus := by
  let V := (U.weighted (hAB.isWeightFamily_image hT)).completion
  let W := ((S.weighted hT).completion).completedTensor A U
  let e := CompletedTensor.weightedRestrictedEquiv B hT
  -- The forward map preserves the plus rings of both tensor factors.
  have hforward : W.plus ≤ V.plus.comap e.toRingHom := by
    have := V.isRingOfIntegralElements.isIntegrallyClosedIn
    refine ((S.weighted hT).completion).completedTensor_plus_le_comap U
      (V.plus.toAddSubgroup.isClosed_of_isOpen V.isRingOfIntegralElements.isOpen)
      (CompletedTensor.continuous_weightedRestrictedEquiv B hT) ?_ ?_
    · intro f hf
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e]
      rw [CompletedTensor.weightedRestrictedEquiv_inl]
      let φ : Hom S U :=
        { toRingHom := algebraMap A B
          continuous_toRingHom := hAB.continuous
          map_mem_plus := hplus }
      exact weighted_completion_plus_le_comap_weightedMapCompletion hT φ
        (hAB.isWeightFamily_image hT) (fun _ ↦ subset_rfl) hf
    · intro b hb
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e]
      rw [CompletedTensor.weightedRestrictedEquiv_inr,
        algebraMap_completion_weightedRestrictedSubring_apply]
      exact U.weightedC_mem_weighted_completion_plus _ hb
  -- Conversely, test the inverse on integral constants and weighted variables.
  have hbackward : V.plus ≤ W.plus.comap e.symm.toRingHom := by
    refine U.weighted_completion_plus_le_comap _ W
      (CompletedTensor.continuous_weightedRestrictedEquiv_symm B hT) ?_ ?_
    · intro b hb
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e]
      rw [CompletedTensor.weightedRestrictedEquiv_symm_weightedC]
      exact ((S.weighted hT).completion).inr_mem_completedTensor_plus U hb
    · rintro i _ ⟨t, ht, rfl⟩
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e]
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
  apply le_antisymm (Subring.map_le_iff_le_comap.mpr hforward)
  intro y hy
  exact ⟨e.symm y, hbackward hy, e.apply_symm_apply y⟩

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
