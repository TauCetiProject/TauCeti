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
import TauCeti.RingTheory.Huber.WeightedEval.Finite
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate.Pair
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.OpenQuotient

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

Composing a finite-type morphism with rational localisation preserves topological finite type
(`isTopologicallyFiniteType_toCompletionLocHom_comp`), without a Tate hypothesis. A weighted
presentation retains the original coefficient plus ring up to integrality and lifts every rational
fraction. This makes its final evaluation a quotient mapping of pairs.

Base change along a rational localisation also preserves topological finite type: if
`f : (A, A⁺) → (B, B⁺)` is topologically of finite type, then so is the base change
`(A⟨T/s⟩, A_U⁺) → (B⟨T'/f(s)⟩, B_V⁺)` of
`TauCeti.Huber.PairOfDefinition.completionLocPairMap`
(`isTopologicallyFiniteType_completionLocPairMap`). For `T'` with underlying set `f(T)` this is
the map of coordinate rings over a rational open `R(T/s)` of `Spa(A, A⁺)` and its preimage in
`Spa(B, B⁺)`, which is what restricting a chart of a morphism locally of finite type
(Wedhorn, Definition 8.48) to a rational open of its target needs. Both the composition and the
base-change statements apply to general Huber pairs, including non-Tate rings.

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
quotient mapping as soon as the generators `A⁺` and `T/s` of `A⁺[T/s]` are integral over
the image of `B⁺`. -/
theorem isQuotientMapping_of_adjoin_le_integralClosure {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsHuberRing B] {W : Pair B} :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    ∀ π : Pair.Hom W (rationalLocalizationPair P U hP T s S hden),
      IsOpenQuotientMap π.toRingHom →
      (Algebra.adjoin U.plus (Set.range fun y : ↥T ↦ (divBy (y : A) s : S))).toSubring ≤
        (integralClosure (W.plus.map π.toRingHom) (Completion S)).toSubring.comap
          Completion.coeRingHom →
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
      hadj
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
  refine isQuotientMapping_of_adjoin_le_integralClosure P U hP T s S hden _ ?_
    ((adjoin_plus_le_comap_map_rationalEvalPairHom P U hP T s S hden t ht hTt).trans
      (fun x hx ↦ by
        rw [Subring.mem_comap, Subalgebra.mem_toSubring, mem_integralClosure_iff]
        exact isIntegral_algebraMap
          (R := (U.weighted (isWeightFamily_one_weight (k := k))).completion.plus.map
            (rationalEvalPairHom P U hP T s S hden t ht).toRingHom)
          (x := ⟨_, hx⟩)))
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
  refine isQuotientMapping_of_adjoin_le_integralClosure P U hP T s S hden _ ?_
    ((adjoin_plus_le_comap_map_weightedRationalEvalPairHom P U hP T s S hden hW).trans
      (fun x hx ↦ by
        rw [Subring.mem_comap, Subalgebra.mem_toSubring, mem_integralClosure_iff]
        exact isIntegral_algebraMap
          (R := (U.weighted hW).completion.plus.map
            (weightedRationalEvalPairHom P U hP T s S hden hW).toRingHom)
          (x := ⟨_, hx⟩)))
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

/-! ### Composing a finite-type chart with rational localisation -/

namespace TauCeti.Huber.PairOfDefinition

open Filter

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  (P : PairOfDefinition B) {U : Pair A} (V : Pair B) (hP : P.ringOfDefinition ≤ V.plus)
  (T : Finset B) (s : B) (S : Type*) [CommRing S] [Algebra B S]
  [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)

-- A rational presentation is a quotient mapping when it retains a quotient presentation of the
-- coefficient plus ring and lifts the rational fractions. This criterion is specific to refining
-- a finite-type presentation; intermediate coefficient maps need not be quotient mappings.
private theorem isQuotientMapping_of_presentation {C : Type*} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsHuberRing C] {W : Pair A} {Z : Pair C}
    (π : Pair.Hom W V) (hπ : π.IsQuotientMapping) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    ∀ (σ : Pair.Hom Z (rationalLocalizationPair P V hP T s S hden))
      (_ : IsOpenQuotientMap σ.toRingHom) (ι : Pair.Hom W Z)
      (_ : ∀ a, σ.toRingHom (ι.toRingHom a) =
        toCompletionLoc P T s S hden (π.toRingHom a))
      (_ : ∀ a : ↥T, ((divBy (a : B) s : S) : Completion S) ∈ Z.plus.map σ.toRingHom),
      σ.IsQuotientMapping := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  intro σ hσ ι hσι hfrac
  apply isQuotientMapping_of_adjoin_le_integralClosure P V hP T s S hden σ hσ
  rw [Algebra.adjoin_eq_ring_closure, Subring.closure_le]
  rintro a (⟨a, rfl⟩ | ⟨a, rfl⟩)
  · let κ : W.plus.map π.toRingHom →+* Z.plus.map σ.toRingHom :=
      (toCompletionLoc P T s S hden).restrict _ _ fun a ha ↦ by
        obtain ⟨a, ha, rfl⟩ := ha
        exact Subring.mem_map.mpr ⟨_, ι.map_mem_plus a ha, hσι a⟩
    rw [SetLike.mem_coe, Subring.mem_comap, Subalgebra.mem_toSubring, mem_integralClosure_iff,
      IsScalarTower.algebraMap_apply V.plus B S, Algebra.algebraMap_ofSubsemiring_apply]
    simpa only [toCompletionLoc_apply, Completion.coe_coeRingHom] using
      (hπ.mem_plus_iff.mp a.2).map_of_comp_eq κ
        (toCompletionLoc P T s S hden) (by ext; rfl)
  · exact isIntegral_algebraMap (R := Z.plus.map σ.toRingHom) (x := ⟨_, hfrac a⟩)

/-- Composing a morphism of Huber pairs topologically of finite type with rational localisation
is topologically of finite type, without a Tate hypothesis. This is the source-refinement input
in Wedhorn's Proposition 8.50. -/
theorem isTopologicallyFiniteType_toCompletionLocHom_comp (f : Pair.Hom U V)
    (hf : f.IsTopologicallyFiniteType) (hT : IsOpen (Ideal.span (insert s (T : Set B)) : Set B)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    ((toCompletionLocHom P V hP T s S hden).comp f).IsTopologicallyFiniteType := by
  classical
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  obtain ⟨k, R, hRfin, hR, π, hπ, hπf⟩ := Pair.Hom.isTopologicallyFiniteType_iff.mp hf
  let D := Completion (weightedRestrictedSubring R hR)
  let Q := rationalWeight T s
  have hQ : IsWeightFamily Q := isWeightFamily_rationalWeight hT
  let E := Completion (weightedRestrictedSubring Q hQ)
  let EV := (V.weighted hQ).completion
  let ρ := weightedRationalEvalPairHom P V hP T s S hden hQ
  let b : Fin 1 → E := fun i ↦ (weightedX Q hQ i : weightedRestrictedSubring Q hQ)
  have hρC (a : B) : ρ.toRingHom (algebraMap B E a) = toCompletionLoc P T s S hden a := by
    exact RingHom.congr_fun
      (weightedRationalEvalHom_comp_algebraMap P T s S hden hQ) a
  have hρX (i : Fin 1) :
      ρ.toRingHom (b i) = ((IsLocalization.Away.invSelf s : S) : Completion S) := by
    exact weightedRationalEvalHom_coe_weightedX P T s S hden hQ i
  -- Adapt the presentation of `Huber.IsTopologicallyFiniteType.comp`: move the second weights
  -- to the original base and add
  -- unweighted variables for their generators. Choose the new weights using the plus ring.
  have hsmall (i : Fin 1) :
      {a : A | algebraMap B E (f.toRingHom a) * b i ∈ EV.plus} ∈ 𝓝 0 := by
    exact ((EV.isRingOfIntegralElements.isOpen.preimage
      (((continuous_algebraMap_completion_weightedRestrictedSubring 1 B hQ).comp
        f.continuous_toRingHom).mul_const (b i))).mem_nhds (by simp))
  choose G hG hGopen using fun i ↦ exists_finset_subset_isOpen_span (hsmall i)
  let W : Fin 1 → Set A := fun i ↦ (G i : Set A)
  have hW : IsWeightFamily W := isWeightFamily_iff_isOpen_span.mpr hGopen
  have hW' : IsWeightFamily fun i ↦ f.toRingHom '' W i :=
    isWeightFamily_iff_isOpen_span.mpr fun i ↦ by
      rw [← Ideal.map_span]
      exact hf.isTopologicallyFiniteType_toRingHom.isOpen_map (hGopen i)
  have hb : IsWeightedVarPowerBounded (algebraMap B E) (fun i ↦ f.toRingHom '' W i) b :=
    (isWeightedVarPowerBounded_iff_of_finite fun i ↦ (G i).finite_toSet.image _).mpr
      fun i a ha ↦ by
        obtain ⟨a, ha, rfl⟩ := ha
        exact EV.isRingOfIntegralElements.isPowerBounded_of_mem (hG i ha)
  obtain ⟨m, idx, t, ht, hcover, θ, hθ, hθB, hθX, hθY⟩ :=
    exists_isOpenQuotientMap_completion_weightedRestrictedSubring_append hQ
      (finite_rationalWeight T s) hW' hb
  let WD : Fin (1 + m) → Set D := Fin.append
    (fun i ↦ algebraMap A D '' W i) (fun _ ↦ ({1} : Set D))
  let WB : Fin (1 + m) → Set B := Fin.append
    (fun i ↦ f.toRingHom '' W i) (fun _ ↦ ({1} : Set B))
  have hWD : IsWeightFamily WD :=
    (hR.image_algebraMap_completion hW).append isWeightFamily_one_weight
  have hWB : IsWeightFamily WB := hW'.append isWeightFamily_one_weight
  have hπA : π.toRingHom.comp (algebraMap A D) = f.toRingHom := by
    rw [← Pair.Hom.toRingHom_weightedCompletionHom, ← Pair.Hom.toRingHom_comp, hπf]
  have hmap : ∀ i, π.toRingHom '' WD i = WB i := fun i ↦ Fin.addCases
    (fun j ↦ by
      simp only [WD, WB, Fin.append_left, Set.image_image]
      exact Set.image_congr fun a _ ↦ RingHom.congr_fun hπA a)
    (fun j ↦ by simp [WD, WB]) i
  let β := weightedMapCompletion π.continuous_toRingHom hWD hWB fun i ↦ (hmap i).subset
  have hβ : IsOpenQuotientMap β := hπ.isOpenQuotientMap.weightedMapCompletion hWD hWB hmap
  let Z : Fin (k + (1 + m)) → Set A := Fin.append R (Fin.append W fun _ ↦ ({1} : Set A))
  have hZ : IsWeightFamily Z := hR.append (hW.append isWeightFamily_one_weight)
  have hRZ : ∀ i, Z (Fin.castAdd (1 + m) i) = R i := fun i ↦ by simp [Z]
  have hZW : ∀ j, algebraMap A D '' Z (Fin.natAdd k j) = WD j := fun j ↦
    Fin.addCases (fun i ↦ by simp [Z, WD]) (fun i ↦ by simp [Z, WD]) j
  let e := U.iterateSplitHom hR hWD hZ hRZ hZW
  have heX (j : Fin (1 + m)) :
      e.toRingHom (weightedX Z hZ (Fin.natAdd k j) : weightedRestrictedSubring Z hZ) =
        (weightedX WD hWD j : weightedRestrictedSubring WD hWD) := by
    dsimp only [e]
    rw [Pair.Hom.toRingHom_iterateSplitHom, iterateSplitHom_coe_weightedX,
      iterateVar_natAdd]
  -- Only plus-ring preservation is needed for the two middle maps. Their composite will be
  -- a quotient mapping by the rational generator criterion, avoiding intermediate integrality.
  have hθC (a : B) : θ (algebraMap B _ a) = algebraMap B E a :=
    RingHom.congr_fun hθB a
  let θ' : Pair.Hom (V.weighted hWB).completion EV :=
    { toRingHom := θ
      continuous_toRingHom := hθ.continuous
      map_mem_plus := V.weighted_completion_plus_le_comap hWB EV hθ.continuous
        (fun a ha ↦ by
          rw [← algebraMap_completion_weightedRestrictedSubring_apply, hθC,
            algebraMap_completion_weightedRestrictedSubring_apply]
          exact V.weightedC_mem_weighted_completion_plus hQ ha)
        (fun j a ha ↦ by
          rw [Completion.coe_mul, map_mul,
            ← algebraMap_completion_weightedRestrictedSubring_apply, hθC]
          revert a ha
          refine Fin.addCases (fun i a ha ↦ ?_) (fun l a ha ↦ ?_) j
          · simp only [WB, Fin.append_left] at ha
            obtain ⟨a, ha, rfl⟩ := ha
            rw [hθX]
            exact hG i ha
          · simp only [WB, Fin.append_right, Set.mem_singleton_iff] at ha
            obtain rfl : a = 1 := ha
            rw [hθY, map_one, one_mul]
            exact V.weightedC_mul_weightedX_mem_weighted_completion_plus hQ (ht l)) }
  have hθ'Y (j : Fin m) :
      θ'.toRingHom (weightedX WB hWB (Fin.natAdd 1 j) : weightedRestrictedSubring WB hWB) =
        algebraMap B E (t j) * b (idx j) := by
    simpa only [θ', Completion.coe_mul,
      ← algebraMap_completion_weightedRestrictedSubring_apply] using hθY j
  let β' : Pair.Hom (((U.weighted hR).completion).weighted hWD).completion
      (V.weighted hWB).completion :=
    { toRingHom := β
      continuous_toRingHom := continuous_weightedMapCompletion ..
      map_mem_plus := Pair.weighted_completion_plus_le_comap_weightedMapCompletion _ π hWB
        fun i ↦ (hmap i).subset }
  have hβX (j : Fin (1 + m)) :
      β'.toRingHom (weightedX WD hWD j : weightedRestrictedSubring WD hWD) =
        (weightedX WB hWB j : weightedRestrictedSubring WB hWB) := by
    dsimp only [β', β]
    rw [weightedMapCompletion_coe, weightedMap_weightedX]
  let σ := ρ.comp (θ'.comp (β'.comp e))
  have hσ : IsOpenQuotientMap σ.toRingHom := by
    simpa only [σ, Pair.Hom.toRingHom_comp, RingHom.coe_comp, Function.comp_assoc]
      using (isQuotientMapping_weightedRationalEvalPairHom
        P V hP T s S hden hQ).isOpenQuotientMap.comp (hθ.comp (hβ.comp
          (U.isQuotientMapping_iterateSplitHom hR hWD hZ hRZ hZW).isOpenQuotientMap))
  -- The first-block inclusion retains the original plus-ring presentation of B.
  let ι := (U.iterateJoinHom hR hWD hZ hRZ hZW).comp
    ((U.weighted hR).completion.weightedCompletionHom hWD)
  have hσι (a : D) : σ.toRingHom (ι.toRingHom a) =
      toCompletionLoc P T s S hden (π.toRingHom a) := by
    have heι : e.comp ι = (U.weighted hR).completion.weightedCompletionHom hWD := by
      simp [e, ι, ← Pair.Hom.comp_assoc]
    have hβC (a : D) : β (algebraMap D _ a) = algebraMap B _ (π.toRingHom a) := by
      dsimp only [β, D]
      rw [algebraMap_completion_weightedRestrictedSubring_apply, weightedMapCompletion_coe,
        weightedMap_weightedC, algebraMap_completion_weightedRestrictedSubring_apply]
    have heι' := RingHom.congr_fun (congrArg Pair.Hom.toRingHom heι) a
    simp only [Pair.Hom.toRingHom_comp, RingHom.comp_apply,
      Pair.Hom.toRingHom_weightedCompletionHom] at heι'
    simp only [σ, Pair.Hom.toRingHom_comp, RingHom.comp_apply]
    rw [heι', hβC, hθC, hρC]
  have hσX (j : Fin m) :
      σ.toRingHom (weightedX Z hZ (Fin.natAdd k (Fin.natAdd 1 j)) :
        weightedRestrictedSubring Z hZ) = (divBy (t j) s : S) := by
    simp only [σ, Pair.Hom.toRingHom_comp, RingHom.comp_apply]
    rw [heX, hβX, hθ'Y, map_mul, hρC, hρX, toCompletionLoc_apply, ← Completion.coe_mul]
    exact congrArg (fun x : S ↦ (x : Completion S)) (algebraMap_mul_invSelf (t j) s)
  have hσquot : σ.IsQuotientMapping := by
    apply isQuotientMapping_of_presentation P V hP T s S hden π hπ σ hσ ι hσι
    intro a
    -- Every rational fraction is the image of an extra unweighted variable.
    obtain ⟨j, _, htj⟩ := hcover 0 a (by
      dsimp only [Q]
      rw [rationalWeight_apply]
      exact Set.mem_insert_of_mem s a.2)
    let l := Fin.natAdd k (Fin.natAdd 1 j)
    have hl : (1 : A) ∈ Z l := by simp [l, Z]
    have hmem := U.weightedC_mul_weightedX_mem_weighted_completion_plus hZ hl
    simp only [map_one, one_mul] at hmem
    have hval : σ.toRingHom (weightedX Z hZ l : weightedRestrictedSubring Z hZ) =
        (divBy (a : B) s : S) := by
      simpa only [l, htj] using hσX j
    exact Subring.mem_map.mpr ⟨_, hmem, hval⟩
  refine Pair.Hom.isTopologicallyFiniteType_iff.mpr
    ⟨k + (1 + m), Z, fun i ↦ Fin.addCases (fun j ↦ by simpa [Z] using hRfin j)
      (fun j ↦ Fin.addCases (fun l ↦ by simpa only [Z, Fin.append_right, Fin.append_left]
        using (G l).finite_toSet)
        (fun _ ↦ by simp [Z]) j) i, hZ, σ, hσquot, ?_⟩
  apply Pair.Hom.ext
  ext a
  have hιA : ι.toRingHom (algebraMap A D a) = algebraMap A _ a := by
    dsimp only [ι, D]
    simp [algebraMap_completion_weightedRestrictedSubring_apply]
  simpa only [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_weightedCompletionHom,
    RingHom.comp_apply, ← hιA, hσι, toRingHom_toCompletionLocHom] using
    congrArg (toCompletionLoc P T s S hden) (RingHom.congr_fun hπA a)

end TauCeti.Huber.PairOfDefinition

/-! ### Base change along a rational localisation -/

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)
  (P' : PairOfDefinition B) (U' : Pair B) (hP' : P'.ringOfDefinition ≤ U'.plus)
  (f : Pair.Hom U U') (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
  [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P' T' s' S')
  (hs : f.toRingHom s = s') (hT : ∀ t ∈ T, f.toRingHom t ∈ T')

/-- **Base change along a rational localisation preserves topological finite type** for Huber
pairs. The target numerators and denominator must generate an open ideal; this holds for the
preimage of a rational subset under a morphism topologically of finite type. -/
theorem isTopologicallyFiniteType_completionLocPairMap (hf : f.IsTopologicallyFiniteType)
    (hspan : IsOpen (Ideal.span (insert s' (T' : Set B)) : Set B)) :
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
  have h := isTopologicallyFiniteType_toCompletionLocHom_comp P' U' hP' T' s' S' hden'
    f hf hspan
  rw [← completionLocPairMap_comp_toCompletionLocHom P U hP T s S hden P' U' hP' f T' s' S' hden'
    hs hT] at h
  exact h.of_comp

end TauCeti.Huber.PairOfDefinition
