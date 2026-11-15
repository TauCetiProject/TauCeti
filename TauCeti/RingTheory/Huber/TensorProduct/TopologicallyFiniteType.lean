/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Presentation
public import TauCeti.RingTheory.Huber.TensorProduct.Symmetry
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.PlusWeak
public import TauCeti.Topology.Maps.OpenQuotient

import TauCeti.RingTheory.Huber.TensorProduct.Quotient.Pair
import TauCeti.RingTheory.Huber.TensorProduct.Restricted.Pair

/-!
# Completed base change of homomorphisms and pair morphisms of finite type

Let `A → B` be an adic homomorphism of Huber rings and `A → C` a homomorphism topologically of
finite type (`TauCeti.Huber.IsTopologicallyFiniteType`), presented by an open quotient map
`π : A⟨X⟩_T → C` out of the completed weighted restricted power series with finite weights `T`.
Then the coprojection `B → C ⊗̂_A B` is again topologically of finite type: base change of `π`
is an open quotient map `B⟨X⟩_{λ(T)} → C ⊗̂_A B` out of the completed weighted restricted power
series over `B` with the image weights
(`TauCeti.Huber.CompletedTensor.isOpenQuotientMap_baseChangePresentation`), and these weights are
again finite.

When `A → B` and `A → C` underlie morphisms of Huber pairs `(A, A⁺) → (B, B⁺)` and
`(A, A⁺) → (C, C⁺)`, the same base-change presentation controls the completed tensor plus rings:

1. **Topological finite type of Huber pairs** (Wedhorn, Definition 8.42; Huber 1994,
   Proposition 3.7): if `(A, A⁺) → (C, C⁺)` is topologically of finite type, presented by a
   quotient mapping `(A⟨X⟩_T, A⟨X⟩_T⁺)^ → (C, C⁺)`, then `(B, B⁺) → (C, C⁺) ⊗̂_A (B, B⁺)` is
   topologically of finite type, presented by composing the inverse restricted-series comparison
   `(B⟨X⟩_{λ(T)}, B⟨X⟩_{λ(T)}⁺)^ → (A⟨X⟩_T, A⟨X⟩_T⁺)^ ⊗̂_A (B, B⁺)` with the base change of the
   quotient mapping (`TauCeti.Huber.Pair.completedTensor.isQuotientMapping_map`).
2. **+Weakly finite type of Huber pairs** (Huber 1996, Definition 1.2.1(ii) and Corollary 1.2.3):
   if `(A, A⁺) → (C, C⁺)` is of +weakly finite type, with `C⁺ = plusClosure (f(A⁺) ∪ E)`, then
   `(B, B⁺) → (C, C⁺) ⊗̂_A (B, B⁺)` is of +weakly finite type with finite generating set the left
   image of `E`.

## Main results

* `TauCeti.Huber.CompletedTensor.isTopologicallyFiniteType_inr`,
  `TauCeti.Huber.CompletedTensor.isTopologicallyFiniteType_inl`: completed base change of
  ring homomorphisms topologically of finite type.
* `TauCeti.Huber.Pair.completedTensor.isTopologicallyFiniteType_inr`,
  `TauCeti.Huber.Pair.completedTensor.isTopologicallyFiniteType_inl`: completed base change of
  morphisms of Huber pairs topologically of finite type.
* `TauCeti.Huber.Pair.completedTensor.isPlusWeaklyFiniteType_inr`,
  `TauCeti.Huber.Pair.completedTensor.isPlusWeaklyFiniteType_inl`: completed base change of
  morphisms of Huber pairs of +weakly finite type.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Lemma 3.5 and Proposition 3.7.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, Definition 1.2.1, Proposition 1.2.2, and Corollary 1.2.3.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], §8.6, Theorem 8.56.
-/

public section

namespace TauCeti.Huber.CompletedTensor

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [Algebra A B] [Algebra A C] [hAB : IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- **Completed base change preserves topological finite type.** If `A → C` is topologically of
finite type and `A → B` is adic, then the right coprojection `B → C ⊗̂_A B` is topologically of
finite type. A presentation `A⟨X⟩_T → C` with finite weights `T` base changes to a presentation
`B⟨X⟩_{λ(T)} → C ⊗̂_A B` with the image weights.

The adicness of `A → C` is part of the data needed to form `C ⊗̂_A B`; it follows from the
finite type hypothesis by `TauCeti.Huber.IsTopologicallyFiniteType.isAdicHom`. -/
theorem isTopologicallyFiniteType_inr (h : IsTopologicallyFiniteType (algebraMap A C)) :
    IsTopologicallyFiniteType (inr A C B) := by
  obtain ⟨k, T, hTfin, hT, π, hπ, hcomm⟩ := isTopologicallyFiniteType_iff.mp h
  refine isTopologicallyFiniteType_iff.mpr ⟨k, fun i ↦ algebraMap A B '' T i,
    fun i ↦ (hTfin i).image _, hAB.isWeightFamily_image hT, _,
    isOpenQuotientMap_baseChangePresentation B hcomm hπ, ?_⟩
  ext b
  simp [algebraMap_completion_weightedRestrictedSubring_apply]

/-- If `A → C` is topologically of finite type and `A → B` is adic, then the left coprojection
`B → B ⊗̂_A C` is topologically of finite type. This is
`TauCeti.Huber.CompletedTensor.isTopologicallyFiniteType_inr` transported along the exchange of
the two factors. -/
theorem isTopologicallyFiniteType_inl (h : IsTopologicallyFiniteType (algebraMap A C)) :
    IsTopologicallyFiniteType (inl A B C) := by
  have hq : IsOpenQuotientMap (comm A C B).toRingHom := by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact (isHomeomorph_comm A C B).isOpenQuotientMap
  have h' := (isTopologicallyFiniteType_inr h).comp_isOpenQuotientMap hq
  convert h' using 1
  ext b
  simp

end TauCeti.Huber.CompletedTensor

namespace TauCeti.Huber.Pair.completedTensor

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  [Algebra A B] [Algebra A C] [hAB : IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

-- Any pair morphism whose underlying ring map is an open quotient map and that admits a section as
-- a morphism of Huber pairs is a quotient mapping of Huber pairs.
private theorem isQuotientMapping_of_comp_eq_id {D E : Type*} [CommRing D] [TopologicalSpace D]
    [IsTopologicalRing D] [IsHuberRing D] [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsHuberRing E] {V : Pair D} {W : Pair E} {f : Hom V W} {g : Hom W V}
    (hopen : IsOpenQuotientMap f.toRingHom) (hfg : f.comp g = Hom.id W) :
    f.IsQuotientMapping := by
  refine (Hom.isQuotientMapping_iff_isOpenQuotientMap_and_isIntegral f).mpr ⟨hopen, fun e he ↦ ?_⟩
  have hmem : e ∈ V.plus.map f.toRingHom := ⟨g.toRingHom e, g.map_mem_plus e he, by
    simpa only [Hom.toRingHom_comp, RingHom.comp_apply, Hom.toRingHom_id, RingHom.id_apply] using
      congrArg (fun k : Hom W W ↦ k.toRingHom e) hfg⟩
  exact isIntegral_algebraMap (R := V.plus.map f.toRingHom) (x := ⟨e, hmem⟩)

-- Exchanging the two factors of `(B, B⁺) ⊗̂_A (C, C⁺)` as a morphism of Huber pairs.
private noncomputable def commHom (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Algebra A B] [Algebra A C] [IsAdicHom (algebraMap A B)]
    [IsAdicHom (algebraMap A C)] (U : Pair B) (T : Pair C) :
    Hom (U.completedTensor A T) (T.completedTensor A U) where
  toRingHom := (CompletedTensor.comm A B C).toRingHom
  continuous_toRingHom := CompletedTensor.continuous_comm A B C
  map_mem_plus _ hx := (comm_mem_plus A U T _).mpr hx

omit [IsHuberRing A] in
@[simp]
private theorem toRingHom_commHom (U : Pair B) (T : Pair C) :
    (commHom A U T).toRingHom = (CompletedTensor.comm A B C).toRingHom :=
  (rfl)

omit [IsHuberRing A] in
private theorem isQuotientMapping_commHom (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Algebra A B] [Algebra A C] [IsAdicHom (algebraMap A B)]
    [IsAdicHom (algebraMap A C)] (U : Pair B) (T : Pair C) :
    (commHom A U T).IsQuotientMapping := by
  refine isQuotientMapping_of_comp_eq_id (g := commHom A T U) ?_ ?_
  · rw [toRingHom_commHom, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact (CompletedTensor.isHomeomorph_comm A B C).isOpenQuotientMap
  · apply Hom.ext
    ext x
    simp only [Hom.toRingHom_comp, toRingHom_commHom, RingHom.comp_apply, Hom.toRingHom_id,
      RingHom.id_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← CompletedTensor.comm_symm]
    exact (CompletedTensor.comm A C B).symm_apply_apply x

/-- **Completed base change preserves topological finite type of Huber pairs** (Huber 1994,
Proposition 3.7; Wedhorn, Definition 8.42 and Theorem 8.56). If `f : (A, A⁺) → (C, C⁺)` is
topologically of finite type over `A` and `A → B` preserves the chosen rings of integral elements,
then the right coprojection `(B, B⁺) → (C, C⁺) ⊗̂_A (B, B⁺)` is topologically of finite type. -/
theorem isTopologicallyFiniteType_inr {S : Pair A} {T : Pair C} (U : Pair B)
    (hplus : S.plus ≤ U.plus.comap (algebraMap A B)) {f : Hom S T}
    (hf : f.IsTopologicallyFiniteType) (hfA : f.toRingHom = algebraMap A C) :
    (inr A T U).IsTopologicallyFiniteType := by
  obtain ⟨k, W, hWfin, hW, π, hπ, hcomm⟩ := Hom.isTopologicallyFiniteType_iff.mp hf
  have hπA : π.toRingHom.comp
      (algebraMap A (UniformSpace.Completion (weightedRestrictedSubring W hW))) =
      algebraMap A C := by
    rw [← hfA, ← hcomm, Hom.toRingHom_comp, Hom.toRingHom_weightedCompletionHom]
  have hidA : (Hom.id U).toRingHom.comp (algebraMap A B) = algebraMap A B := by simp
  have hofW : (ofWeighted S U hW).IsQuotientMapping := by
    refine isQuotientMapping_of_comp_eq_id (g := toWeighted S U hW hplus) ?_
      (ofWeighted_comp_toWeighted S U hW hplus)
    rw [toRingHom_ofWeighted, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact (CompletedTensor.isHomeomorph_weightedRestrictedEquiv_symm B hW).isOpenQuotientMap
  have hmap : (map (RingHom.id A) π (Hom.id U) hπA hidA).IsQuotientMapping :=
    isQuotientMapping_map π (Hom.id U) hπA hidA hπ (Hom.isQuotientMapping_id U)
  refine Hom.isTopologicallyFiniteType_iff.mpr ⟨k, fun i ↦ algebraMap A B '' W i,
    fun i ↦ (hWfin i).image _, hAB.isWeightFamily_image hW,
    (map (RingHom.id A) π (Hom.id U) hπA hidA).comp (ofWeighted S U hW),
    hmap.comp hofW, ?_⟩
  apply Hom.ext
  ext b
  simp [algebraMap_completion_weightedRestrictedSubring_apply]

/-- **Symmetric form of `isTopologicallyFiniteType_inr`**: if `f : (A, A⁺) → (C, C⁺)` is
topologically of finite type over `A` and `A → B` preserves the chosen rings of integral elements,
then the left coprojection `(B, B⁺) → (B, B⁺) ⊗̂_A (C, C⁺)` is topologically of finite type. -/
theorem isTopologicallyFiniteType_inl {S : Pair A} {T : Pair C} (U : Pair B)
    (hplus : S.plus ≤ U.plus.comap (algebraMap A B)) {f : Hom S T}
    (hf : f.IsTopologicallyFiniteType) (hfA : f.toRingHom = algebraMap A C) :
    (inl A U T).IsTopologicallyFiniteType := by
  have heq : (commHom A T U).comp (inr A T U) = inl A U T := by
    apply Hom.ext
    ext b
    simp
  rw [← heq]
  exact (isTopologicallyFiniteType_inr U hplus hf hfA).comp_isQuotientMapping
    (isQuotientMapping_commHom A T U)

/-- **Completed base change preserves +weakly finite type of Huber pairs** (Huber 1996,
Definition 1.2.1(ii) and Corollary 1.2.3(ii)): if `f : (A, A⁺) → (C, C⁺)` is of +weakly finite
type over `A` and `A → B` preserves the chosen rings of integral elements, then the right
coprojection `(B, B⁺) → (C, C⁺) ⊗̂_A (B, B⁺)` is of +weakly finite type. -/
theorem isPlusWeaklyFiniteType_inr {S : Pair A} {T : Pair C} (U : Pair B)
    (hplus : S.plus ≤ U.plus.comap (algebraMap A B)) {f : Hom S T}
    (hf : f.IsPlusWeaklyFiniteType) (hfA : f.toRingHom = algebraMap A C) :
    (inr A T U).IsPlusWeaklyFiniteType := by
  classical
  obtain ⟨hftft, E, hE⟩ := Hom.isPlusWeaklyFiniteType_iff.mp hf
  have hET : (E : Set C) ⊆ T.plus := hE ▸ fun _ hc ↦ subset_plusClosure _ (Or.inr hc)
  let E' : Finset (CompletedTensor A C B) := E.image (CompletedTensor.inl A C B)
  have hE' : (E' : Set (CompletedTensor A C B)) ⊆ (T.completedTensor A U).plus := by
    rw [Finset.coe_image]
    exact Set.image_subset_iff.mpr fun _ hc ↦ T.inl_mem_completedTensor_plus U (hET hc)
  refine Hom.isPlusWeaklyFiniteType_of_plus_le
    (by rw [toRingHom_inr]; exact CompletedTensor.isTopologicallyFiniteType_inr (hfA ▸ hftft))
    E' hE' ?_
  set X := (inr A T U).toRingHom '' (U.plus : Set B) ∪ (E' : Set (CompletedTensor A C B))
  have hQ := isRingOfIntegralElements_plusClosure fun _ hx ↦
    (T.completedTensor A U).isRingOfIntegralElements.le_powerBoundedSubring
      ((inr A T U).plusClosure_image_union_le hE' (subset_plusClosure X hx))
  have := hQ.isIntegrallyClosedIn
  refine T.completedTensor_plus_le_comap U
    ((plusClosure X).toAddSubgroup.isClosed_of_isOpen hQ.isOpen) (f := RingHom.id _) continuous_id
    (fun c hc ↦ ?_) (fun b hb ↦ subset_plusClosure X (Or.inl ⟨b, hb, by simp⟩))
  -- Since `C⁺ = plusClosure (f(A⁺) ∪ E)`, `inl` carries `C⁺` into `plusClosure X`.
  rw [hE] at hc
  refine plusClosure_le hQ.isOpen ?_
    (map_plusClosure_le (CompletedTensor.continuous_inl A C B) _ ⟨c, hc, rfl⟩)
  rintro _ ⟨c₀, hc₀ | hc₀, rfl⟩
  · obtain ⟨a, ha, rfl⟩ := hc₀
    rw [hfA, CompletedTensor.inl_algebraMap, ← CompletedTensor.inr_algebraMap]
    exact subset_plusClosure X (Or.inl ⟨algebraMap A B a, hplus ha, by simp⟩)
  · exact subset_plusClosure X (Or.inr (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hc₀)))

/-- **Symmetric form of `isPlusWeaklyFiniteType_inr`**: if `f : (A, A⁺) → (C, C⁺)` is of +weakly
finite type over `A` and `A → B` preserves the chosen rings of integral elements, then the left
coprojection `(B, B⁺) → (B, B⁺) ⊗̂_A (C, C⁺)` is of +weakly finite type. -/
theorem isPlusWeaklyFiniteType_inl {S : Pair A} {T : Pair C} (U : Pair B)
    (hplus : S.plus ≤ U.plus.comap (algebraMap A B)) {f : Hom S T}
    (hf : f.IsPlusWeaklyFiniteType) (hfA : f.toRingHom = algebraMap A C) :
    (inl A U T).IsPlusWeaklyFiniteType := by
  have heq : (commHom A T U).comp (inr A T U) = inl A U T := by
    apply Hom.ext
    ext b
    simp
  rw [← heq]
  have hcomm : (commHom A T U).IsPlusWeaklyFiniteType :=
    (isQuotientMapping_commHom A T U).isTopologicallyFiniteType.isPlusWeaklyFiniteType
  exact hcomm.comp (isPlusWeaklyFiniteType_inr U hplus hf hfA)

end TauCeti.Huber.Pair.completedTensor
