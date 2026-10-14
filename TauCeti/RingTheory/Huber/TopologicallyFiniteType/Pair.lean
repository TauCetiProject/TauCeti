/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Completion.Basic
public import TauCeti.RingTheory.Huber.QuotientMapping
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair

/-!
# Morphisms of Huber pairs topologically of finite type

A morphism `f : (A, A⁺) → (B, B⁺)` of Huber pairs is *topologically of finite type* (Wedhorn,
Definition 8.42) when it factors as the structure map into the completion of a weighted
restricted power-series pair `(A⟨X₁, …, Xₖ⟩_T, A⟨X⟩_T⁺)` (Remark and Definition 8.41), each weight
`Tᵢ` finite, followed by a quotient mapping onto `(B, B⁺)`. A quotient mapping is an open
surjection whose target plus ring is the integral closure of the image of the source plus ring, so
the definition controls `B⁺` as well as `B`. This is the affinoid notion from which morphisms of
adic spaces locally of finite type are built.

Forgetting the plus rings recovers the ring-level notion
`TauCeti.Huber.IsTopologicallyFiniteType` of Wedhorn's Proposition and Definition 6.29(i), and
`TauCeti.Huber.Pair.Hom.isTopologicallyFiniteType_iff_exists_isOpenQuotientMap` says exactly what
the plus rings add: the target plus ring is the integral closure of the image of the completed
weighted plus ring.

As for the ring-level notion, completeness of `A` and `B` is not imposed by the definition; Wedhorn
states it for complete affinoid rings, and a consumer that needs completeness assumes it alongside.
Over a complete Hausdorff pair the identity is topologically of finite type, presented with no
variables, and hence so is every quotient mapping out of such a pair.

## Main definitions

* `TauCeti.Huber.Pair.weightedCompletionHom`: the structure map `(A, A⁺) → (A⟨X⟩_T, A⟨X⟩_T⁺)^`
  into the completed weighted pair.
* `TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType`: Wedhorn Definition 8.42.

## Main results

* `TauCeti.Huber.Pair.Hom.isTopologicallyFiniteType_iff_exists_isOpenQuotientMap`: the definition
  in terms of a ring-level presentation together with the integral-closure condition on `B⁺`.
* `TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.isTopologicallyFiniteType_toRingHom`: the
  underlying ring homomorphism is topologically of finite type.
* `TauCeti.Huber.Pair.isTopologicallyFiniteType_weightedCompletionHom`: the structure map into a
  completed weighted pair with finite weights is topologically of finite type.
* `TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.comp_isQuotientMapping` and
  `TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.quotientHom`: the notion is stable under
  composing with a quotient mapping, in particular under passing to a quotient pair.
* `TauCeti.Huber.Pair.weighted_completion_plus_le` and
  `TauCeti.Huber.Pair.weighted_completion_plus_le_comap`: the plus ring of the completed weighted
  pair is the smallest closed, integrally closed subring containing the constants from `A⁺` and
  the weighted variables, so morphisms out of it are checked on those generators.
* `TauCeti.Huber.Pair.Hom.isQuotientMapping_of_isIntegral_weighted`: an open quotient map onto a
  completed weighted pair is a quotient mapping once those generators are integral over the image
  of the source plus ring.
* `TauCeti.Huber.Pair.exists_isQuotientMapping_weightedCompletionHom` and
  `TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.exists_isQuotientMapping_one_weight`: over a
  Tate ring the weights can be removed, so a morphism topologically of finite type is presented
  by an unweighted completed pair `(A⟨Y₁, …, Yₘ⟩, A⟨Y⟩⁺)`.
* `TauCeti.Huber.Pair.Hom.isTopologicallyFiniteType_id` and
  `TauCeti.Huber.Pair.Hom.IsQuotientMapping.isTopologicallyFiniteType`: over a complete Hausdorff
  Huber pair, the identity and every quotient mapping are topologically of finite type.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 6.34, Lemma 7.47,
  Remark and Definition 8.41, and Definition 8.42.
-/

public section

open UniformSpace

namespace TauCeti.Huber.Pair

section Presentation

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  {S : Pair A} {U : Pair B} {V : Pair C} {k : ℕ} {T : Fin k → Set A}

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

namespace Hom

/-- **Wedhorn Definition 8.42**: a morphism `f : (A, A⁺) → (B, B⁺)` of Huber pairs is
*topologically of finite type* when it factors as the structure map into a completed weighted pair
`(A⟨X₁, …, Xₖ⟩_T, A⟨X⟩_T⁺)^`, each weight `Tᵢ` finite, followed by a quotient mapping onto
`(B, B⁺)`. -/
def IsTopologicallyFiniteType (f : Hom S U) : Prop :=
  ∃ (k : ℕ) (T : Fin k → Set A) (_ : ∀ i, (T i).Finite) (hT : IsWeightFamily T)
    (π : Hom (S.weighted hT).completion U),
    π.IsQuotientMapping ∧ π.comp (S.weightedCompletionHom hT) = f

/-- Unfolding lemma for the sealed definition `TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType`.
-/
theorem isTopologicallyFiniteType_iff {f : Hom S U} :
    f.IsTopologicallyFiniteType ↔
      ∃ (k : ℕ) (T : Fin k → Set A) (_ : ∀ i, (T i).Finite) (hT : IsWeightFamily T)
        (π : Hom (S.weighted hT).completion U),
        π.IsQuotientMapping ∧ π.comp (S.weightedCompletionHom hT) = f :=
  (Iff.rfl)

/-- **A morphism of Huber pairs is topologically of finite type exactly when its underlying ring
homomorphism has a presentation `π : Â⟨X⟩_T ↠ B` whose image of the plus ring of `Â⟨X⟩_T` has
integral closure `B⁺`.** The plus rings add nothing beyond this integral-closure condition. -/
theorem isTopologicallyFiniteType_iff_exists_isOpenQuotientMap {f : Hom S U} :
    f.IsTopologicallyFiniteType ↔
      ∃ (k : ℕ) (T : Fin k → Set A) (_ : ∀ i, (T i).Finite) (hT : IsWeightFamily T)
        (π : Completion (weightedRestrictedSubring T hT) →+* B),
        IsOpenQuotientMap π ∧
          π.comp (algebraMap A (Completion (weightedRestrictedSubring T hT))) = f.toRingHom ∧
          U.plus = (integralClosure ((S.weighted hT).completion.plus.map π) B).toSubring := by
  refine ⟨fun ⟨k, T, hTfin, hT, π, hπ, hcomm⟩ ↦ ⟨k, T, hTfin, hT, π.toRingHom,
    hπ.isOpenQuotientMap, ?_, hπ.plus_eq⟩, fun ⟨k, T, hTfin, hT, π, hπ, hcomm, hplus⟩ ↦ ?_⟩
  · rw [← hcomm, toRingHom_comp, toRingHom_weightedCompletionHom]
  · -- every element of the image of the plus ring is integral over it, so lies in `B⁺`
    let π' : Hom (S.weighted hT).completion U :=
      { toRingHom := π
        continuous_toRingHom := hπ.continuous
        map_mem_plus a ha := hplus ▸ Subalgebra.algebraMap_mem _
          (⟨π a, Subring.mem_map.mpr ⟨a, ha, rfl⟩⟩ : (S.weighted hT).completion.plus.map π) }
    exact ⟨k, T, hTfin, hT, π', ⟨hπ, hplus⟩, Hom.ext <| by
      rw [toRingHom_comp, toRingHom_weightedCompletionHom, ← hcomm]⟩

/-- **The underlying ring homomorphism of a morphism of Huber pairs topologically of finite type is
topologically of finite type**, in the sense of Wedhorn's Proposition and Definition 6.29(i). -/
theorem IsTopologicallyFiniteType.isTopologicallyFiniteType_toRingHom {f : Hom S U}
    (h : f.IsTopologicallyFiniteType) :
    _root_.TauCeti.Huber.IsTopologicallyFiniteType f.toRingHom := by
  obtain ⟨k, T, hTfin, hT, π, hπ, hcomm, -⟩ :=
    isTopologicallyFiniteType_iff_exists_isOpenQuotientMap.mp h
  exact _root_.TauCeti.Huber.isTopologicallyFiniteType_iff.mpr ⟨k, T, hTfin, hT, π, hπ, hcomm⟩

/-- **A presentation composes with a quotient mapping**: if `f` is topologically of finite type
and `g` is a quotient mapping, then `g ∘ f` is topologically of finite type. -/
theorem IsTopologicallyFiniteType.comp_isQuotientMapping {f : Hom S U} {g : Hom U V}
    (hf : f.IsTopologicallyFiniteType) (hg : g.IsQuotientMapping) :
    (g.comp f).IsTopologicallyFiniteType := by
  obtain ⟨k, T, hTfin, hT, π, hπ, rfl⟩ := isTopologicallyFiniteType_iff.mp hf
  exact ⟨k, T, hTfin, hT, g.comp π, hg.comp hπ, comp_assoc ..⟩

/-- **Topological finite type passes to a quotient pair**: if `f : (A, A⁺) → (B, B⁺)` is
topologically of finite type, then so is its composite with `(B, B⁺) → (B ⧸ J, (B ⧸ J)⁺)`. -/
theorem IsTopologicallyFiniteType.quotientHom {f : Hom S U} (hf : f.IsTopologicallyFiniteType)
    (J : Ideal B) : ((U.quotientHom J).comp f).IsTopologicallyFiniteType :=
  hf.comp_isQuotientMapping (isQuotientMapping_quotientHom U J)

end Hom

/-- **The structure map into a completed weighted pair is topologically of finite type** when every
weight is finite: it is presented by the identity. -/
theorem isTopologicallyFiniteType_weightedCompletionHom (hTfin : ∀ i, (T i).Finite)
    (hT : IsWeightFamily T) : (S.weightedCompletionHom hT).IsTopologicallyFiniteType :=
  ⟨k, T, hTfin, hT, Hom.id _, Hom.isQuotientMapping_id _, Hom.id_comp _⟩

end Presentation

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

variable {S hT} in
/-- **A morphism onto a completed weighted pair is a quotient mapping** as soon as it is an open
quotient map and the constants from `A⁺` and the weighted variables `t Xᵢ` (`t ∈ Tᵢ`) are
integral over the image of the source plus ring. -/
theorem Hom.isQuotientMapping_of_isIntegral_weighted {W : Pair B}
    (θ : Hom W (S.weighted hT).completion) (hθ : IsOpenQuotientMap θ.toRingHom)
    (hC : ∀ a ∈ S.plus, IsIntegral (W.plus.map θ.toRingHom)
      ((weightedC T hT a : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)))
    (hX : ∀ i, ∀ t ∈ T i, IsIntegral (W.plus.map θ.toRingHom)
      ((weightedC T hT t * weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT))) :
    θ.IsQuotientMapping := by
  let R := (integralClosure (W.plus.map θ.toRingHom)
    (Completion (weightedRestrictedSubring T hT))).toSubring
  -- `R` contains the open image of `W⁺`, so it is open, hence closed
  have hopen :
      IsOpen (W.plus.map θ.toRingHom : Set (Completion (weightedRestrictedSubring T hT))) := by
    rw [Subring.coe_map]
    exact hθ.isOpenMap _ W.isRingOfIntegralElements.isOpen
  have hR : IsClosed (R : Set (Completion (weightedRestrictedSubring T hT))) :=
    R.toAddSubgroup.isClosed_of_isOpen <| AddSubgroup.isOpen_mono
      (H₁ := (W.plus.map θ.toRingHom).toAddSubgroup)
      (fun x hx ↦ isIntegral_algebraMap (R := W.plus.map θ.toRingHom) (x := ⟨x, hx⟩)) hopen
  exact (isQuotientMapping_iff_isOpenQuotientMap_and_isIntegral θ).mpr
    ⟨hθ, fun b hb ↦ S.weighted_completion_plus_le hT hR hC hX hb⟩

end CompletedPlus

/-! ### Unweighted presentations over a Tate ring -/

section Tate

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {S : Pair A} {U : Pair B}

variable (S) in
/-- **Over a Tate ring a completed weighted pair is a quotient of an unweighted one**: for a
finite weight family `T`, there is a quotient mapping
`(A⟨Y₁, …, Yₘ⟩, A⟨Y⟩⁺) → (A⟨X⟩_T, A⟨X⟩_T⁺)^` under `(A, A⁺)`, sending each `Yⱼ` to a weighted
variable `t Xᵢ`. Pair form of
`TauCeti.Huber.isStrictlyTopologicallyFiniteType_algebraMap_completion_weightedRestrictedSubring`.
-/
theorem exists_isQuotientMapping_weightedCompletionHom {k : ℕ} {T : Fin k → Set A}
    (hT : IsWeightFamily T) (hTfin : ∀ i, (T i).Finite) :
    ∃ (m : ℕ) (θ : Hom (S.weighted (isWeightFamily_one_weight (k := m))).completion
      (S.weighted hT).completion), θ.IsQuotientMapping ∧
        θ.comp (S.weightedCompletionHom isWeightFamily_one_weight) =
          S.weightedCompletionHom hT := by
  obtain ⟨m, idx, t, htT, ht, θ, hθ, hθA, hθX⟩ :=
    exists_isOpenQuotientMap_restrictedMvPowerSeriesCompletion hT hTfin
  have hθC (a : A) : θ ((weightedC (fun _ : Fin m ↦ ({1} : Set A)) isWeightFamily_one_weight a :
      weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion m A) =
        (weightedC T hT a : weightedRestrictedSubring T hT) := by
    simpa [algebraMap_completion_weightedRestrictedSubring_apply] using
      congrArg (fun φ : A →+* _ ↦ φ a) hθA
  -- the generators of the unweighted plus ring: the constants from `A⁺` and the variables
  have hY : ∀ a ∈ ({1} : Set A), ∀ j,
      (weightedC (fun _ : Fin m ↦ ({1} : Set A)) isWeightFamily_one_weight a *
        weightedX _ isWeightFamily_one_weight j : weightedRestrictedSubring _ _) =
        weightedX _ isWeightFamily_one_weight j := by
    rintro a rfl j
    rw [map_one, one_mul]
  let θ' : Hom (S.weighted (isWeightFamily_one_weight (k := m))).completion
      (S.weighted hT).completion :=
    { toRingHom := θ
      continuous_toRingHom := hθ.continuous
      map_mem_plus := S.weighted_completion_plus_le_comap _ _ hθ.continuous
        (fun a ha ↦ by
          rw [hθC]
          exact S.weightedC_mem_weighted_completion_plus hT ha)
        (fun j a ha ↦ by
          rw [hY a ha j, hθX]
          exact S.weightedC_mul_weightedX_mem_weighted_completion_plus hT (htT j)) }
  -- an element of the image of the source plus ring is integral over it
  have hint : ∀ x ∈ (S.weighted (isWeightFamily_one_weight (k := m))).completion.plus,
      IsIntegral ((S.weighted (isWeightFamily_one_weight (k := m))).completion.plus.map θ)
        (θ x) := fun x hx ↦
    isIntegral_algebraMap (R := (S.weighted _).completion.plus.map θ)
      (x := ⟨θ x, Subring.mem_map.mpr ⟨x, hx, rfl⟩⟩)
  refine ⟨m, θ', Hom.isQuotientMapping_of_isIntegral_weighted θ' hθ (fun a ha ↦ ?_)
    (fun i a ha ↦ ?_), Hom.ext ?_⟩
  · rw [← hθC]
    exact hint _ (S.weightedC_mem_weighted_completion_plus _ ha)
  · obtain ⟨j, rfl, rfl⟩ := ht i a ha
    rw [← hθX, ← hY 1 rfl j]
    exact hint _ (S.weightedC_mul_weightedX_mem_weighted_completion_plus _ (Set.mem_singleton 1))
  · rw [Hom.toRingHom_comp, Hom.toRingHom_weightedCompletionHom,
      Hom.toRingHom_weightedCompletionHom]
    exact hθA

/-- **Over a Tate ring a morphism of Huber pairs topologically of finite type has an unweighted
presentation**: it factors as the structure map into some `(A⟨Y₁, …, Yₘ⟩, A⟨Y⟩⁺)` followed by a
quotient mapping. Pair form of
`TauCeti.Huber.IsTopologicallyFiniteType.isStrictlyTopologicallyFiniteType`. -/
theorem Hom.IsTopologicallyFiniteType.exists_isQuotientMapping_one_weight {f : Hom S U}
    (hf : f.IsTopologicallyFiniteType) :
    ∃ (m : ℕ) (π : Hom (S.weighted (isWeightFamily_one_weight (k := m))).completion U),
      π.IsQuotientMapping ∧ π.comp (S.weightedCompletionHom isWeightFamily_one_weight) = f := by
  obtain ⟨k, T, hTfin, hT, π, hπ, rfl⟩ := isTopologicallyFiniteType_iff.mp hf
  obtain ⟨m, θ, hθ, hθc⟩ := S.exists_isQuotientMapping_weightedCompletionHom hT hTfin
  exact ⟨m, π.comp θ, hπ.comp hθ, by rw [comp_assoc, hθc]⟩

end Tate

/-! ### Complete Hausdorff pairs -/

section Complete

variable {A B : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]

/-- **The identity of a complete Hausdorff Huber pair is topologically of finite type**, presented
with no variables: `Â⟨⟩` is `Â = A`, and the extension of `A⟨⟩ ≃ A` to the completion is a
quotient mapping with section the structure map. -/
theorem Hom.isTopologicallyFiniteType_id (S : Pair A) :
    (Hom.id S).IsTopologicallyFiniteType := by
  let T : Fin 0 → Set A := finZeroElim
  have hT := isWeightFamily_fin_zero T
  -- the comparison `A⟨⟩ ≃ A` is a morphism of pairs `(A⟨⟩, A⟨⟩⁺) → (A, A⁺)`
  let ev : Hom (S.weighted hT) S :=
    { toRingHom := weightedRestrictedSubringFinZeroEquiv T
      continuous_toRingHom := continuous_weightedRestrictedSubringFinZeroEquiv T
      map_mem_plus := S.weighted_plus_le_comap hT S
        (continuous_weightedRestrictedSubringFinZeroEquiv T) (fun a ha ↦ by simpa using ha)
        finZeroElim }
  -- its extension to the completion has the structure map as a section
  have hsec : ev.extension.comp (S.weightedCompletionHom hT) = Hom.id S := by
    rw [weightedCompletionHom, ← comp_assoc, Hom.extension_comp_completionHom]
    ext a
    simp [ev]
  have hinv : Function.LeftInverse ev.extension.toRingHom (S.weightedCompletionHom hT).toRingHom :=
    fun a ↦ by simp [weightedCompletionHom, ev]
  refine ⟨0, T, finZeroElim, hT, ev.extension,
    (Hom.isQuotientMapping_iff_isOpenQuotientMap_and_isIntegral _).mpr ⟨?_, fun a ha ↦ ?_⟩, hsec⟩
  · -- a continuous map with a continuous section is a quotient map, hence open for groups
    exact AddMonoidHom.isOpenQuotientMap_of_isQuotientMap <| .of_inverse
      (S.weightedCompletionHom hT).continuous_toRingHom ev.extension.continuous_toRingHom hinv
  · -- `a` is the image of `a ∈ Â⟨⟩⁺`, so integral over the image
    have hmem : a ∈ (S.weighted hT).completion.plus.map ev.extension.toRingHom :=
      hinv a ▸ Subring.mem_map.mpr ⟨_, (S.weightedCompletionHom hT).map_mem_plus a ha, rfl⟩
    exact isIntegral_algebraMap (R := (S.weighted hT).completion.plus.map _) (x := ⟨a, hmem⟩)

/-- **Every quotient mapping out of a complete Hausdorff Huber pair is topologically of finite
type**, presented with no variables. -/
theorem Hom.IsQuotientMapping.isTopologicallyFiniteType {S : Pair A} {U : Pair B} {f : Hom S U}
    (hf : f.IsQuotientMapping) : f.IsTopologicallyFiniteType := by
  simpa using (Hom.isTopologicallyFiniteType_id S).comp_isQuotientMapping hf

end Complete

end TauCeti.Huber.Pair
