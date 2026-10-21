/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate.Basic
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair

/-!
# Weighted iteration for Huber pairs

The weighted iteration isomorphism identifies the completed Huber pairs
`(A⟨X,Y⟩_U, A⟨X,Y⟩_U⁺)^` and `((A⟨X⟩_T, A⟨X⟩_T⁺)^⟨Y⟩_W)^`, when the first block of
weights is `T` and the second block maps to `W` under the structure map of `A⟨X⟩_T`.
In particular, it identifies the plus rings exactly, rather than merely sending one into
the other. This permits weighted finite-type presentations of Huber pairs to be iterated.

The maps `Pair.iterateSplitHom` and `Pair.iterateJoinHom` are mutually inverse morphisms of
Huber pairs. `Pair.map_iterateSplitHom_plus` identifies the plus rings, and
`Pair.isQuotientMapping_iterateSplitHom` makes the splitting usable in quotient presentations.
The weights need not be finite and the base need not be Tate, complete, or Hausdorff.

The underlying ring isomorphism is `TauCeti.Huber.iterateRingEquiv`, and the plus rings satisfy
the generator characterization `Pair.weighted_completion_plus_le_comap`.
`Pair.Hom.IsTopologicallyFiniteType.comp` uses the splitting to flatten iterated presentations.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark and Definition 8.41 and Proposition 8.46.
-/

public section

noncomputable section

open UniformSpace

namespace TauCeti.Huber.Pair

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (S : Pair A) {k m : ℕ} {T : Fin k → Set A} (hT : IsWeightFamily T)
  {W : Fin m → Set (Completion (weightedRestrictedSubring T hT))} (hW : IsWeightFamily W)
  {U : Fin (k + m) → Set A} (hU : IsWeightFamily U)
  (hTU : ∀ i, U (Fin.castAdd m i) = T i)
  (hUW : ∀ j, algebraMap A (Completion (weightedRestrictedSubring T hT)) '' U (Fin.natAdd k j) =
    W j)

include hTU in
/-- Including the first block carries its completed plus ring into the joint plus ring. -/
private theorem plus_le_comap_iterateFirstBlockHom :
    (S.weighted hT).completion.plus ≤ (S.weighted hU).completion.plus.comap
      (Huber.iterateFirstBlockHom hT hU hTU) := by
  apply S.weighted_completion_plus_le_comap hT _ (continuous_iterateFirstBlockHom ..)
  · intro a ha
    rw [iterateFirstBlockHom_coe_weightedC, algebraMap_completion_weightedRestrictedSubring_apply]
    exact S.weightedC_mem_weighted_completion_plus hU ha
  · intro i t ht
    simpa only [Completion.coe_mul, map_mul, iterateFirstBlockHom_coe_weightedC,
      iterateFirstBlockHom_coe_weightedX, algebraMap_completion_weightedRestrictedSubring_apply]
      using S.weightedC_mul_weightedX_mem_weighted_completion_plus hU (hTU i ▸ ht)

/-- Splitting the variables of a completed weighted algebra, as a morphism of Huber pairs. -/
def iterateSplitHom : Hom (S.weighted hU).completion
    (((S.weighted hT).completion).weighted hW).completion where
  toRingHom := Huber.iterateSplitHom hT hW hU hTU hUW
  continuous_toRingHom := continuous_iterateSplitHom ..
  map_mem_plus a ha := by
    refine S.weighted_completion_plus_le_comap hU
      (((S.weighted hT).completion).weighted hW).completion
      (continuous_iterateSplitHom hT hW hU hTU hUW) ?_ ?_ ha
    · intro a ha
      rw [iterateSplitHom_coe_weightedC, iterateStructureHom_apply]
      exact (S.weighted hT).completion.weightedC_mem_weighted_completion_plus hW
        (S.weightedC_mem_weighted_completion_plus hT ha)
    · intro l
      refine Fin.addCases (fun i t ht ↦ ?_) (fun j t ht ↦ ?_) l
      · simpa only [Completion.coe_mul, map_mul, iterateSplitHom_coe_weightedC,
          iterateSplitHom_coe_weightedX, iterateStructureHom_apply, iterateVar_castAdd]
          using (S.weighted hT).completion.weightedC_mem_weighted_completion_plus hW
            (S.weightedC_mul_weightedX_mem_weighted_completion_plus hT (hTU i ▸ ht))
      · simpa only [Completion.coe_mul, map_mul, iterateSplitHom_coe_weightedC,
          iterateSplitHom_coe_weightedX, iterateStructureHom_apply, iterateVar_natAdd,
          algebraMap_completion_weightedRestrictedSubring_apply]
          using (S.weighted hT).completion.weightedC_mul_weightedX_mem_weighted_completion_plus hW
            (hUW j ▸ Set.mem_image_of_mem _ ht)

/-- The splitting morphism has `TauCeti.Huber.iterateSplitHom` as its underlying ring map. -/
@[simp]
theorem Hom.toRingHom_iterateSplitHom :
    (S.iterateSplitHom hT hW hU hTU hUW).toRingHom =
      Huber.iterateSplitHom hT hW hU hTU hUW := (rfl)

/-- Joining the variables of an iterated completed weighted algebra, as a morphism of Huber pairs.
-/
def iterateJoinHom : Hom (((S.weighted hT).completion).weighted hW).completion
    (S.weighted hU).completion where
  toRingHom := Huber.iterateJoinHom hT hW hU hTU hUW
  continuous_toRingHom := continuous_iterateJoinHom ..
  map_mem_plus a ha := by
    refine (S.weighted hT).completion.weighted_completion_plus_le_comap hW
      (S.weighted hU).completion
      (continuous_iterateJoinHom hT hW hU hTU hUW) ?_ ?_ ha
    · intro a ha
      rw [iterateJoinHom_coe_weightedC]
      exact plus_le_comap_iterateFirstBlockHom S hT hU hTU ha
    · intro j w hw
      obtain ⟨t, ht, rfl⟩ := hUW j ▸ hw
      simpa only [Completion.coe_mul, map_mul, iterateJoinHom_coe_weightedC,
        iterateJoinHom_coe_weightedX, algebraMap_completion_weightedRestrictedSubring_apply,
        iterateFirstBlockHom_coe_weightedC]
        using S.weightedC_mul_weightedX_mem_weighted_completion_plus hU ht

/-- The joining morphism has `TauCeti.Huber.iterateJoinHom` as its underlying ring map. -/
@[simp]
theorem Hom.toRingHom_iterateJoinHom :
    (S.iterateJoinHom hT hW hU hTU hUW).toRingHom =
      Huber.iterateJoinHom hT hW hU hTU hUW := (rfl)

/-- Joining after splitting is the identity morphism of the joint completed weighted pair. -/
@[simp]
theorem iterateJoinHom_comp_iterateSplitHom :
    (S.iterateJoinHom hT hW hU hTU hUW).comp (S.iterateSplitHom hT hW hU hTU hUW) =
      Hom.id (S.weighted hU).completion := by
  apply Hom.ext
  simp

/-- Splitting after joining is the identity morphism of the iterated completed weighted pair. -/
@[simp]
theorem iterateSplitHom_comp_iterateJoinHom :
    (S.iterateSplitHom hT hW hU hTU hUW).comp (S.iterateJoinHom hT hW hU hTU hUW) =
      Hom.id (((S.weighted hT).completion).weighted hW).completion := by
  apply Hom.ext
  simp

/-- Weighted iteration maps the joint plus ring onto the iterated plus ring. -/
@[simp]
theorem map_iterateSplitHom_plus :
    (completionPlus (integralClosure (weightedSubring U hU S.plus)
      (weightedRestrictedSubring U hU)).toSubring).map
        (Huber.iterateSplitHom hT hW hU hTU hUW) =
      (((S.weighted hT).completion).weighted hW).completion.plus := by
  rw [← S.weighted_plus hU, ← completion_plus (S.weighted hU)]
  apply le_antisymm
  · exact Subring.map_le_iff_le_comap.mpr (S.iterateSplitHom hT hW hU hTU hUW).map_mem_plus
  · intro a ha
    refine Subring.mem_map.mpr ⟨Huber.iterateJoinHom hT hW hU hTU hUW a,
      (S.iterateJoinHom hT hW hU hTU hUW).map_mem_plus a ha, ?_⟩
    exact DFunLike.congr_fun (Huber.iterateSplitHom_comp_iterateJoinHom hT hW hU hTU hUW) a

/-- The splitting is a quotient mapping of Huber pairs. The exact plus-ring equality is
`map_iterateSplitHom_plus`. -/
theorem isQuotientMapping_iterateSplitHom :
    (S.iterateSplitHom hT hW hU hTU hUW).IsQuotientMapping := by
  apply (Hom.isQuotientMapping_iff_isOpenQuotientMap_and_isIntegral _).mpr
  refine ⟨?_, fun a ha ↦ ?_⟩
  · rw [Hom.toRingHom_iterateSplitHom]
    have he : (iterateRingEquiv hT hW hU hTU hUW : _ → _) =
        Huber.iterateSplitHom hT hW hU hTU hUW :=
      congrArg DFunLike.coe (iterateRingEquiv_coe hT hW hU hTU hUW)
    rw [← he]
    exact (Homeomorph.mk (iterateRingEquiv hT hW hU hTU hUW).toEquiv
      (continuous_iterateRingEquiv hT hW hU hTU hUW)
      (continuous_iterateRingEquiv_symm hT hW hU hTU hUW)).isOpenQuotientMap
  · rw [Hom.toRingHom_iterateSplitHom, completion_plus, weighted_plus, map_iterateSplitHom_plus]
    exact isIntegral_algebraMap
      (R := (((S.weighted hT).completion).weighted hW).completion.plus) (x := ⟨a, ha⟩)

/-- Weighted splitting commutes with the structure morphisms from the base pair. -/
@[simp]
theorem iterateSplitHom_comp_weightedCompletionHom :
    (S.iterateSplitHom hT hW hU hTU hUW).comp (S.weightedCompletionHom hU) =
      ((S.weighted hT).completion.weightedCompletionHom hW).comp
        (S.weightedCompletionHom hT) := by
  apply Hom.ext
  ext a
  simp [algebraMap_completion_weightedRestrictedSubring_apply]

end TauCeti.Huber.Pair
