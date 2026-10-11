/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Evaluation
public import TauCeti.RingTheory.Huber.LocalizationTopology.Pair
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair

/-!
# Finite-type presentations of rational localisation pairs

The evaluation map `A⟨X₁, …, Xₖ⟩ → A⟨T/s⟩`, sending `Xᵢ` to `tᵢ/s`, is a quotient
mapping of Huber pairs over a Tate ring when the listed fractions cover `T/s` and the
numerators together with `s` generate the unit ideal. Thus rational localisation is
topologically of finite type as a morphism of pairs, not just of underlying rings.
This is the affine input for refining finite-type charts by rational opens.

The plus-ring comparison uses the completed plus rings on both sides. The image of the
source plus ring is open because evaluation is open; its integral closure is consequently
closed. It contains the constants from `A⁺` and the fractions `T/s`, hence the closure of
the image of the integral closure of `A⁺[T/s]`, which is the localisation's plus ring.
No completeness or separation assumption on `A` is needed.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Example 6.38, Remark and Definition 8.41,
  Definition 8.42, and Proposition 8.50.
* The ring presentation is `TauCeti.Huber.PairOfDefinition.rationalEvalHom` from
  `TauCeti.RingTheory.Huber.LocalizationTopology.Evaluation`.
-/

public section

open Topology UniformSpace TauCeti.Localization

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
  [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)

variable {k : ℕ} (t : Fin k → A) (ht : ∀ i, t i ∈ T)

/-- Evaluation at `tᵢ/s` as a morphism from the completed restricted-series pair to the
rational localisation pair. The variables belong to the source plus ring and the fractions
belong to the target plus ring. -/
noncomputable def rationalEvalPairHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    Pair.Hom (U.weighted (isWeightFamily_one_weight (k := k))).completion
      (rationalLocalizationPair P U hP T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let V := rationalLocalizationPair P U hP T s S hden
  let π := rationalEvalHom P T s S hden t ht
  have hπ := continuous_rationalEvalHom P T s S hden t ht
  have hmap : (U.weighted isWeightFamily_one_weight).plus ≤
      V.plus.comap (π.comp Completion.coeRingHom) := by
    apply U.weighted_plus_le_comap isWeightFamily_one_weight V
      (hπ.comp Completion.continuous_coeRingHom)
    · intro a ha
      simpa [V, π, RingHom.comp_apply] using
        toCompletionLoc_mem_completedPlusSubring P U.plus T s S hden ha
    · intro i a ha
      obtain rfl : a = 1 := Set.mem_singleton_iff.mp ha
      simpa [V, π, RingHom.comp_apply] using
        divBy_mem_completedPlusSubring P U.plus T s S hden (ht i)
  refine ⟨π, hπ, fun x hx ↦ ?_⟩
  rw [Pair.completion_plus, completionPlus_def] at hx
  have hmap' : (U.weighted isWeightFamily_one_weight).plus.map Completion.coeRingHom ≤
      V.plus.comap π := Subring.map_le_iff_le_comap.mpr hmap
  exact Subring.topologicalClosure_minimal _ hmap'
    ((V.plus.toAddSubgroup.isClosed_of_isOpen V.isRingOfIntegralElements.isOpen).preimage hπ) hx

/-- The pair evaluation map is the existing rational evaluation on underlying rings. -/
@[simp]
theorem toRingHom_rationalEvalPairHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (rationalEvalPairHom P U hP T s S hden t ht).toRingHom =
      rationalEvalHom P T s S hden t ht := (rfl)

/-- Evaluation followed by the constant-series map is the rational localisation structure
map, as an equality of morphisms of Huber pairs. -/
@[simp]
theorem rationalEvalPairHom_comp_weightedCompletionHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (rationalEvalPairHom P U hP T s S hden t ht).comp
        (U.weightedCompletionHom isWeightFamily_one_weight) =
      toCompletionLocHom P U hP T s S hden := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  apply Pair.Hom.ext
  rw [Pair.Hom.toRingHom_comp, toRingHom_rationalEvalPairHom,
    Pair.Hom.toRingHom_weightedCompletionHom, toRingHom_toCompletionLocHom]
  exact rationalEvalHom_comp_algebraMap P T s S hden t ht

-- The algebraic generators of `A⁺[T/s]` lift to the completed source plus ring.
private theorem adjoin_plus_le_comap_map_rationalEvalPairHom
    (hTt : Set.range (fun y : ↥T ↦ (divBy (y : A) s : S)) ⊆
      Set.range fun i ↦ (divBy (t i) s : S)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (Algebra.adjoin U.plus (Set.range fun y : ↥T ↦ (divBy (y : A) s : S))).toSubring ≤
      (((U.weighted (isWeightFamily_one_weight (k := k))).completion.plus.map
        (rationalEvalPairHom P U hP T s S hden t ht).toRingHom).comap Completion.coeRingHom) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  rw [Algebra.adjoin_eq_ring_closure, Subring.closure_le]
  rintro a (⟨b, rfl⟩ | ⟨y, rfl⟩)
  · rw [SetLike.mem_coe, Subring.mem_comap, toRingHom_rationalEvalPairHom]
    rw [IsScalarTower.algebraMap_apply U.plus A S, Algebra.algebraMap_ofSubsemiring_apply]
    refine Subring.mem_map.mpr ⟨((weightedC (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight b : weightedRestrictedSubring _ _) :
        restrictedMvPowerSeriesCompletion k A), ?_, ?_⟩
    · rw [Pair.completion_plus]
      exact map_mem_completionPlus
        (U.weightedC_mem_weighted_plus isWeightFamily_one_weight b.2)
    · simp [toCompletionLoc_apply, Completion.coeRingHom]
  · obtain ⟨i, hi⟩ := hTt ⟨y, rfl⟩
    simp only at hi
    rw [SetLike.mem_coe, Subring.mem_comap, toRingHom_rationalEvalPairHom]
    dsimp only
    rw [← hi]
    refine Subring.mem_map.mpr ⟨((weightedX (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight i : weightedRestrictedSubring _ _) :
        restrictedMvPowerSeriesCompletion k A), ?_,
      rationalEvalHom_coe_weightedX P T s S hden t ht i⟩
    rw [Pair.completion_plus]
    apply map_mem_completionPlus
    simpa only [map_one, one_mul] using
      U.weightedC_mul_weightedX_mem_weighted_plus isWeightFamily_one_weight
        (i := i) (t := 1) (by simp)

end TauCeti.Huber.PairOfDefinition

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
  [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
  {k : ℕ} (t : Fin k → A) (ht : ∀ i, t i ∈ T)

/-- Over a Tate ring, rational evaluation is a quotient mapping of Huber pairs: its target
plus ring is exactly the integral closure of the image of the completed source plus ring. -/
theorem isQuotientMapping_rationalEvalPairHom
    (hspan : Ideal.span (insert s (Set.range t)) = ⊤)
    (hTt : Set.range (fun y : ↥T ↦ (divBy (y : A) s : S)) ⊆
      Set.range fun i ↦ (divBy (t i) s : S)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (rationalEvalPairHom P U hP T s S hden t ht).IsQuotientMapping := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let π := rationalEvalPairHom P U hP T s S hden t ht
  have hopen : IsOpenQuotientMap π.toRingHom := by
    rw [toRingHom_rationalEvalPairHom]
    exact isOpenQuotientMap_rationalEvalHom P T s S hden t ht hspan hTt
  let Bplus := (U.weighted (isWeightFamily_one_weight (k := k))).completion.plus
  let R := (integralClosure (Bplus.map π.toRingHom) (Completion S)).toSubring
  have hR : Bplus.map π.toRingHom ≤ R := fun x hx ↦
    isIntegral_algebraMap (R := Bplus.map π.toRingHom) (x := ⟨x, hx⟩)
  have hRclosed : IsClosed (R : Set (Completion S)) := by
    apply AddSubgroup.isClosed_of_isOpen R.toAddSubgroup
    have himage : IsOpen (Bplus.map π.toRingHom : Set (Completion S)) := by
      rw [Subring.coe_map]
      exact hopen.isOpenMap _
        (U.weighted isWeightFamily_one_weight).completion.isRingOfIntegralElements.isOpen
    exact AddSubgroup.isOpen_mono (H₁ := (Bplus.map π.toRingHom).toAddSubgroup) hR himage
  apply (Pair.Hom.isQuotientMapping_iff_isOpenQuotientMap_and_isIntegral π).mpr
  refine ⟨hopen, fun x hx ↦ ?_⟩
  have hle : completedPlusSubring P U.plus T s S hden ≤ R := by
    apply (completedPlusSubring_le_iff P U.plus T s S hden hRclosed).mpr
    have hbase : (Algebra.adjoin U.plus (Set.range fun y : ↥T ↦ (divBy (y : A) s : S))).toSubring ≤
        R.comap Completion.coeRingHom :=
      (adjoin_plus_le_comap_map_rationalEvalPairHom P U hP T s S hden t ht hTt).trans
        ((Subring.gc_map_comap Completion.coeRingHom).monotone_u hR)
    have hIC : (integralClosure
        ↥(Algebra.adjoin U.plus (Set.range fun y : ↥T ↦ (divBy (y : A) s : S))) S).toSubring ≤
        R.comap Completion.coeRingHom := Subring.integralClosure_le_iff.mpr fun a ↦ hbase a.2
    exact fun x hx ↦ hIC hx
  exact hle ((rationalLocalizationPair_plus P U hP T s S hden) ▸ hx)

/-- Rational localisation of a Tate Huber pair is topologically of finite type. The
numerators together with the denominator must generate the unit ideal; for a rational open
in a Tate spectrum this follows from openness of the numerator ideal. -/
theorem isTopologicallyFiniteType_toCompletionLocHom
    (hspan : Ideal.span (insert s (T : Set A)) = ⊤) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (toCompletionLocHom P U hP T s S hden).IsTopologicallyFiniteType := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let t : Fin T.card → A := fun i ↦ (T.equivFin.symm i : A)
  have ht : ∀ i, t i ∈ T := fun i ↦ (T.equivFin.symm i).2
  have hrange : Set.range t = (T : Set A) := by
    simpa [t, Function.comp_def] using
      T.equivFin.symm.surjective.range_comp (fun y : ↥T ↦ (y : A))
  have hTt : Set.range (fun y : ↥T ↦ (divBy (y : A) s : S)) ⊆
      Set.range fun i ↦ (divBy (t i) s : S) := by
    simpa only [t, Function.comp_def] using
      (T.equivFin.symm.surjective.range_comp (fun y : ↥T ↦ (divBy (y : A) s : S))).ge
  refine Pair.Hom.isTopologicallyFiniteType_iff.mpr
    ⟨T.card, fun _ ↦ {1}, fun _ ↦ Set.finite_singleton 1, isWeightFamily_one_weight,
      rationalEvalPairHom P U hP T s S hden t ht, ?_,
      rationalEvalPairHom_comp_weightedCompletionHom P U hP T s S hden t ht⟩
  apply isQuotientMapping_rationalEvalPairHom P U hP T s S hden t ht _ hTt
  rwa [hrange]

end TauCeti.Huber.PairOfDefinition
