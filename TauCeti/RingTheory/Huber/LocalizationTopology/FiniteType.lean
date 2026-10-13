/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.BaseChange
public import TauCeti.RingTheory.Huber.LocalizationTopology.Evaluation
public import TauCeti.RingTheory.Huber.LocalizationTopology.WeightedEvaluation
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair

import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Finite-type presentations of rational localisation pairs

Two presentations of a rational localisation pair `(A⟨T/s⟩, A_U⁺)` as a quotient of a completed
restricted power-series pair are compared with the plus rings included.

* Over a Tate ring, the evaluation map `A⟨X₁, …, Xₖ⟩ → A⟨T/s⟩`, sending `Xᵢ` to `tᵢ/s`, is a
  quotient mapping of Huber pairs when the listed fractions cover `T/s` and the numerators
  together with `s` generate the unit ideal.
* Over any Huber ring, the evaluation map `A⟨X⟩_{T ∪ {s}} → A⟨T/s⟩` out of the weighted
  restricted power series, sending `X` to `1/s`, is a quotient mapping of Huber pairs when
  `T ∪ {s}` generates an open ideal. Hence the structure morphism `(A, A⁺) → (A⟨T/s⟩, A_U⁺)` is
  topologically of finite type (`isTopologicallyFiniteType_toCompletionLocHom`) as a morphism of
  pairs, not just of underlying rings, with no Tate hypothesis.

This is the affine input for refining finite-type charts by rational opens.

The plus-ring comparison uses the completed plus rings on both sides. The image of the
source plus ring is open because evaluation is open; its integral closure is consequently
closed. It contains the constants from `A⁺` and the fractions `T/s`, hence the closure of
the image of the integral closure of `A⁺[T/s]`, which is the localisation's plus ring.
No completeness or separation assumption on `A` is needed.

Base change along a rational localisation also preserves topological finite type: if
`f : (A, A⁺) → (B, B⁺)` is topologically of finite type and `A` is Tate, then so is the base change
`(A⟨T/s⟩, A_U⁺) → (B⟨T'/f(s)⟩, B_V⁺)` of
`TauCeti.Huber.PairOfDefinition.completionLocPairMap`
(`isTopologicallyFiniteType_completionLocPairMap`). For `T'` with underlying set `f(T)` this is
the map of coordinate rings over a rational open `R(T/s)` of `Spa(A, A⁺)` and its preimage in
`Spa(B, B⁺)`, which is what restricting a chart of a morphism locally of finite type
(Wedhorn, Definition 8.48) to a rational open of its target needs.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Example 6.38, Remark and Definition 8.41,
  Definition 8.42, Proposition 8.46, Definition 8.48, and Proposition 8.50.
* The ring presentations are `TauCeti.Huber.PairOfDefinition.rationalEvalHom` from
  `TauCeti.RingTheory.Huber.LocalizationTopology.Evaluation` and
  `TauCeti.Huber.PairOfDefinition.weightedRationalEvalHom` from
  `TauCeti.RingTheory.Huber.LocalizationTopology.WeightedEvaluation`.
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

/-- **A criterion for quotient mappings onto a rational localisation pair**: a morphism of Huber
pairs `(B, B⁺) → (A⟨T/s⟩, A_U⁺)` whose underlying ring homomorphism is an open quotient map is a
quotient mapping as soon as the image of `B⁺` contains the generators `A⁺` and `T/s` of
`A⁺[T/s]`. -/
theorem isQuotientMapping_of_adjoin_le {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsHuberRing B] {W : Pair B} :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    ∀ π : Pair.Hom W (rationalLocalizationPair P U hP T s S hden),
      IsOpenQuotientMap π.toRingHom →
      (Algebra.adjoin U.plus (Set.range fun y : ↥T ↦ (divBy (y : A) s : S))).toSubring ≤
        (W.plus.map π.toRingHom).comap Completion.coeRingHom →
      π.IsQuotientMapping := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  intro π hopen hadj
  let R := (integralClosure (W.plus.map π.toRingHom) (Completion S)).toSubring
  have hR : W.plus.map π.toRingHom ≤ R := fun x hx ↦
    isIntegral_algebraMap (R := W.plus.map π.toRingHom) (x := ⟨x, hx⟩)
  have hRclosed : IsClosed (R : Set (Completion S)) := by
    apply AddSubgroup.isClosed_of_isOpen R.toAddSubgroup
    have himage : IsOpen (W.plus.map π.toRingHom : Set (Completion S)) := by
      rw [Subring.coe_map]
      exact hopen.isOpenMap _ W.isRingOfIntegralElements.isOpen
    exact AddSubgroup.isOpen_mono (H₁ := (W.plus.map π.toRingHom).toAddSubgroup) hR himage
  apply (Pair.Hom.isQuotientMapping_iff_isOpenQuotientMap_and_isIntegral π).mpr
  refine ⟨hopen, fun x hx ↦ ?_⟩
  have hle : completedPlusSubring P U.plus T s S hden ≤ R := by
    apply (completedPlusSubring_le_iff P U.plus T s S hden hRclosed).mpr
    have hbase : (Algebra.adjoin U.plus (Set.range fun y : ↥T ↦ (divBy (y : A) s : S))).toSubring ≤
        R.comap Completion.coeRingHom :=
      hadj.trans ((Subring.gc_map_comap Completion.coeRingHom).monotone_u hR)
    have hIC : (integralClosure
        ↥(Algebra.adjoin U.plus (Set.range fun y : ↥T ↦ (divBy (y : A) s : S))) S).toSubring ≤
        R.comap Completion.coeRingHom := Subring.integralClosure_le_iff.mpr fun a ↦ hbase a.2
    exact fun x hx ↦ hIC hx
  exact hle ((rationalLocalizationPair_plus P U hP T s S hden) ▸ hx)

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
  refine isQuotientMapping_of_adjoin_le P U hP T s S hden _ ?_
    (adjoin_plus_le_comap_map_rationalEvalPairHom P U hP T s S hden t ht hTt)
  rw [toRingHom_rationalEvalPairHom]
  exact isOpenQuotientMap_rationalEvalHom P T s S hden t ht hspan hTt

end TauCeti.Huber.PairOfDefinition

/-! ### Rational localisation over a Huber ring -/

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
  [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
  (hW : IsWeightFamily (rationalWeight T s))

/-- The evaluation `X ↦ 1/s` as a morphism from the completed weighted pair
`(A⟨X⟩_{T ∪ {s}}, A⟨X⟩_{T ∪ {s}}⁺)` to the rational localisation pair. The weighted variables
`t X` go to the fractions `t/s` and to `s/s = 1`, which lie in the target plus ring. -/
noncomputable def weightedRationalEvalPairHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    Pair.Hom (U.weighted hW).completion (rationalLocalizationPair P U hP T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let V := rationalLocalizationPair P U hP T s S hden
  let π := weightedRationalEvalHom P T s S hden hW
  have hπ := continuous_weightedRationalEvalHom P T s S hden hW
  have hmap : (U.weighted hW).plus ≤ V.plus.comap (π.comp Completion.coeRingHom) := by
    apply U.weighted_plus_le_comap hW V (hπ.comp Completion.continuous_coeRingHom)
    · intro a ha
      simpa [V, π, RingHom.comp_apply] using
        toCompletionLoc_mem_completedPlusSubring P U.plus T s S hden ha
    · intro i t ht
      have hcoe : (Completion.coeRingHom (weightedC _ hW t * weightedX _ hW i) :
          Completion (weightedRestrictedSubring _ hW)) =
            ((weightedC _ hW t : weightedRestrictedSubring _ hW) : Completion _) *
              ((weightedX _ hW i : weightedRestrictedSubring _ hW) : Completion _) :=
        Completion.coe_mul _ _
      rw [RingHom.comp_apply, hcoe, map_mul, weightedRationalEvalHom_coe_weightedC,
        weightedRationalEvalHom_coe_weightedX, toCompletionLoc_apply, ← Completion.coe_mul,
        mul_comm, invSelf_mul_algebraMap]
      rcases (rationalWeight_apply T s i ▸ ht : t ∈ insert s (T : Set A)) with ht | ht
      · rw [ht, divBy_self, Completion.coe_one]
        exact V.plus.one_mem
      · rw [rationalLocalizationPair_plus]
        exact divBy_mem_completedPlusSubring P U.plus T s S hden ht
  refine ⟨π, hπ, fun x hx ↦ ?_⟩
  rw [Pair.completion_plus, completionPlus_def] at hx
  have hmap' : (U.weighted hW).plus.map Completion.coeRingHom ≤ V.plus.comap π :=
    Subring.map_le_iff_le_comap.mpr hmap
  exact Subring.topologicalClosure_minimal _ hmap'
    ((V.plus.toAddSubgroup.isClosed_of_isOpen V.isRingOfIntegralElements.isOpen).preimage hπ) hx

/-- The pair evaluation map is `TauCeti.Huber.PairOfDefinition.weightedRationalEvalHom` on
underlying rings. -/
@[simp]
theorem toRingHom_weightedRationalEvalPairHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (weightedRationalEvalPairHom P U hP T s S hden hW).toRingHom =
      weightedRationalEvalHom P T s S hden hW := (rfl)

/-- Evaluation followed by the constant-series map is the structure morphism of the rational
localisation pair. -/
@[simp]
theorem weightedRationalEvalPairHom_comp_weightedCompletionHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (weightedRationalEvalPairHom P U hP T s S hden hW).comp (U.weightedCompletionHom hW) =
      toCompletionLocHom P U hP T s S hden := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  apply Pair.Hom.ext
  rw [Pair.Hom.toRingHom_comp, toRingHom_weightedRationalEvalPairHom,
    Pair.Hom.toRingHom_weightedCompletionHom, toRingHom_toCompletionLocHom]
  exact weightedRationalEvalHom_comp_algebraMap P T s S hden hW

-- The algebraic generators of `A⁺[T/s]` lift to the completed source plus ring.
private theorem adjoin_plus_le_comap_map_weightedRationalEvalPairHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (Algebra.adjoin U.plus (Set.range fun y : ↥T ↦ (divBy (y : A) s : S))).toSubring ≤
      (((U.weighted hW).completion.plus.map
        (weightedRationalEvalPairHom P U hP T s S hden hW).toRingHom).comap
          Completion.coeRingHom) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  rw [Algebra.adjoin_eq_ring_closure, Subring.closure_le]
  rintro a (⟨b, rfl⟩ | ⟨y, rfl⟩)
  · rw [SetLike.mem_coe, Subring.mem_comap, toRingHom_weightedRationalEvalPairHom,
      IsScalarTower.algebraMap_apply U.plus A S, Algebra.algebraMap_ofSubsemiring_apply]
    refine Subring.mem_map.mpr ⟨((weightedC (rationalWeight T s) hW b :
      weightedRestrictedSubring _ _) : Completion (weightedRestrictedSubring _ hW)), ?_, ?_⟩
    · rw [Pair.completion_plus]
      exact map_mem_completionPlus (U.weightedC_mem_weighted_plus hW b.2)
    · simp [toCompletionLoc_apply, Completion.coeRingHom]
  · rw [SetLike.mem_coe, Subring.mem_comap, toRingHom_weightedRationalEvalPairHom]
    refine Subring.mem_map.mpr ⟨((weightedC (rationalWeight T s) hW y * weightedX _ hW 0 :
      weightedRestrictedSubring _ _) : Completion (weightedRestrictedSubring _ hW)), ?_, ?_⟩
    · rw [Pair.completion_plus]
      exact map_mem_completionPlus
        (U.weightedC_mul_weightedX_mem_weighted_plus hW
          (rationalWeight_apply T s 0 ▸ Set.mem_insert_of_mem s y.2))
    · rw [Completion.coe_mul, map_mul, weightedRationalEvalHom_coe_weightedC,
        weightedRationalEvalHom_coe_weightedX, toCompletionLoc_apply, ← Completion.coe_mul,
        mul_comm, invSelf_mul_algebraMap]
      rfl

/-- **Over a Huber ring, the evaluation `X ↦ 1/s` is a quotient mapping of Huber pairs**: its
target plus ring is exactly the integral closure of the image of the completed source plus
ring. -/
theorem isQuotientMapping_weightedRationalEvalPairHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (weightedRationalEvalPairHom P U hP T s S hden hW).IsQuotientMapping := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  refine isQuotientMapping_of_adjoin_le P U hP T s S hden _ ?_
    (adjoin_plus_le_comap_map_weightedRationalEvalPairHom P U hP T s S hden hW)
  rw [toRingHom_weightedRationalEvalPairHom]
  exact isOpenQuotientMap_weightedRationalEvalHom P T s S hden hW

/-- **Rational localisation of a Huber pair is topologically of finite type** (Wedhorn,
Definition 8.42, at Example 6.38): if `T ∪ {s}` generates an open ideal, the structure morphism
`(A, A⁺) → (A⟨T/s⟩, A_U⁺)` is presented by the weighted pair `(A⟨X⟩_{T ∪ {s}}, A⟨X⟩_{T ∪ {s}}⁺)`,
`X ↦ 1/s`. No Tate hypothesis is needed. -/
theorem isTopologicallyFiniteType_toCompletionLocHom
    (hT : IsOpen (Ideal.span (insert s (T : Set A)) : Set A)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (toCompletionLocHom P U hP T s S hden).IsTopologicallyFiniteType :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_completion_locTopology P T s S hden
  Pair.Hom.isTopologicallyFiniteType_iff.mpr
    ⟨1, rationalWeight T s, finite_rationalWeight T s, isWeightFamily_rationalWeight hT,
      weightedRationalEvalPairHom P U hP T s S hden _,
      isQuotientMapping_weightedRationalEvalPairHom P U hP T s S hden _,
      weightedRationalEvalPairHom_comp_weightedCompletionHom P U hP T s S hden _⟩

end TauCeti.Huber.PairOfDefinition

/-! ### Base change along a rational localisation -/

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)
  (P' : PairOfDefinition B) (U' : Pair B) (hP' : P'.ringOfDefinition ≤ U'.plus)
  (f : Pair.Hom U U') (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
  [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P' T' s' S')
  (hs : f.toRingHom s = s') (hT : ∀ t ∈ T, f.toRingHom t ∈ T')

/-- **Base change along a rational localisation preserves topological finite type**, over a Tate
base: if `f : (A, A⁺) → (B, B⁺)` is topologically of finite type and `A` is Tate, then so is the
base change `(A⟨T/s⟩, A_U⁺) → (B⟨T'/f(s)⟩, B_V⁺)`.

The hypothesis `hspan`, that `T'` and `f(s)` generate the unit ideal of `B`, holds as soon as `T`
and `s` generate the unit ideal of `A`, which for a rational subset of a Tate spectrum follows from
openness of the numerator ideal. -/
theorem isTopologicallyFiniteType_completionLocPairMap (hf : f.IsTopologicallyFiniteType)
    (hspan : Ideal.span (insert s' (T' : Set B)) = ⊤) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    (completionLocPairMap P U hP T s S hden P' U' hP' f T' s' S' hden'
      hs hT).IsTopologicallyFiniteType := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  have : IsTateRing B := IsTateRing.of_continuous f.continuous_toRingHom
  have h := (isTopologicallyFiniteType_toCompletionLocHom P' U' hP' T' s' S' hden'
    (by rw [hspan]; exact isOpen_univ)).comp hf
  rw [← completionLocPairMap_comp_toCompletionLocHom P U hP T s S hden P' U' hP' f T' s' S' hden'
    hs hT] at h
  exact h.of_comp

end TauCeti.Huber.PairOfDefinition
