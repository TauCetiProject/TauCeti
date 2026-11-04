/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Affinoid
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Sheafy
public import TauCeti.RingTheory.Huber.TensorProduct.Pushout

import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.GlueMorphisms
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Points
import TauCeti.RingTheory.Huber.TensorProduct.TopologicallyFiniteType

/-!
# Fibre products of affinoid adic spaces

Let `(A, A⁺)`, `(B, B⁺)` and `(C, C⁺)` be complete Hausdorff Huber pairs whose adic spectra are
sheafy, and let `(E, E⁺)` be a sheafy complete Hausdorff Huber pair fitting into a completed pushout
square `TauCeti.Huber.IsCompletedPushout f g i j` (in particular, Huber's completed tensor product
`(B, B⁺) ⊗̂_A (C, C⁺)` along adic structure maps). This file proves that `Spa(E, E⁺)` is a
pullback of `Spa(B, B⁺) ⟶ Spa(A, A⁺)` and `Spa(C, C⁺) ⟶ Spa(A, A⁺)` in Wedhorn's category
`TauCeti.AdicSpace` of adic spaces (`TauCeti.AdicSpace.isPullback_ofPair_of_isCompletedPushout`,
`TauCeti.AdicSpace.affinoid_isPullback`).

The universal property is tested against arbitrary adic spaces `X`, not only affinoid ones:

1. **Affinoid test objects**: when `X = Spa(D, D⁺)` with `D` complete and Hausdorff (`T0Space D`)
   and sheafy structure presheaf, Huber's global-sections bijection
   (`TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceHomEquiv`) translates compatible cones
   into compatible morphisms of Huber pairs into `(D, D⁺)`, where `IsCompletedPushout` supplies a
   unique common extension.
2. **Joint monomorphicity**: for an arbitrary adic space `X`, two morphisms `X ⟶ Spa(E, E⁺)` with
   equal compositions to `Spa(B, B⁺)` and `Spa(C, C⁺)` agree on every open affinoid subspace
   `U ⊆ X` by choosing a complete Hausdorff sheafy model of `X|_U`
   (`TauCeti.PreAdicSpace.isSheafy.exists_complete_isSheaf_of_mem_affinoidOpens`), hence agree
   globally because `X` is sheafy (`TauCeti.PreAdicSpace.hom_ext_of_ofRestrict`).
3. **Gluing local lifts**: local lifts over the open affinoid cover of `X` agree on overlaps
   `X|_{U₁} ×_X X|_{U₂}`, because the overlap maps to `X` by an open immersion and is therefore
   again an adic space (`TauCeti.PreAdicSpace.isAdic_of_isOpenImmersion`), so joint monomorphicity
   applies on the overlap and `TauCeti.PreAdicSpace.glueMorphisms` produces the global lift.

When one of `B` or `C` is stably sheafy (`TauCeti.Huber.IsStablySheafyRing`) and the other structure
map is topologically of finite type (`TauCeti.Huber.IsTopologicallyFiniteType`), the completed
tensor product is automatically sheafy
(`TauCeti.Huber.isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_left`), giving an
unconditional affinoid fibre product
(`TauCeti.AdicSpace.affinoid_isPullback_of_isStablySheafyRing_left`, the local step of Wedhorn's
Theorem 8.56). Over a Tate base (`TauCeti.Huber.IsTateRing A`), compatible points of the two factors
lift to a point of the fibre product (`TauCeti.AdicSpace.exists_ofPair_completedTensor_point`).

## Main results

* `TauCeti.ValuationSpectrum.existsUnique_presentationLimitPreAdicSpace_lift_of_isCompletedPushout`:
  the pre-adic universal property of a completed pushout against any adic test space `X`.
* `TauCeti.AdicSpace.isPullback_ofPresentation_of_isCompletedPushout`,
  `TauCeti.AdicSpace.isPullback_ofPair_of_isCompletedPushout`: any sheafy complete Hausdorff
  completed pushout gives a pullback square in `AdicSpace`.
* `TauCeti.AdicSpace.affinoid_isPullback`: `Spa((B, B⁺) ⊗̂_A (C, C⁺))` is the pullback of
  `Spa(B, B⁺)` and `Spa(C, C⁺)` over `Spa(A, A⁺)` in `AdicSpace` whenever it is sheafy.
* `TauCeti.AdicSpace.affinoid_isPullback_of_isStablySheafyRing_left`,
  `TauCeti.AdicSpace.affinoid_isPullback_of_isStablySheafyRing_right`: unconditional pullback in
  `AdicSpace` when one factor is stably sheafy and the opposite structure map is topologically of
  finite type.
* `TauCeti.AdicSpace.isAdic_comapOfPair_completedTensor_inl`,
  `TauCeti.AdicSpace.locallyOfWeaklyFiniteType_comapOfPair_completedTensor_inl` (and `_inr`):
  preservation of adicness and local weak finite type on projections.
* `TauCeti.AdicSpace.exists_ofPair_completedTensor_point`: lifting compatible points over a Tate
  base to the affinoid fibre product.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Proposition 3.7 and Lemma 3.9(i).
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, Proposition 1.2.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.6, Theorem 8.56.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.PreAdicSpace

universe u

section Condition

variable {A B C E : Type u}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  [CommRing E] [TopologicalSpace E] [IsTopologicalRing E] [IsHuberRing E]
  {S : Pair A} {T : Pair B} {U : Pair C} {W : Pair E}
  (PA : PairOfDefinition A) (PB : PairOfDefinition B)
  (PC : PairOfDefinition C) (PE : PairOfDefinition E)
  (hA : PA.ringOfDefinition ≤ S.plus) (hB : PB.ringOfDefinition ≤ T.plus)
  (hC : PC.ringOfDefinition ≤ U.plus) (hE : PE.ringOfDefinition ≤ W.plus)
  (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
    (presentationLimitPresheaf PB T.plus))
  (hsheafC : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U.plus))
    (presentationLimitPresheaf PC U.plus))
  (hsheafE : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa W.plus))
    (presentationLimitPresheaf PE W.plus))

/-- A completed pushout square of Huber pairs induces a commuting square of presentation-limit
pre-adic spaces. -/
@[reassoc]
theorem presentationLimitPreAdicSpacePairComap_condition_of_isCompletedPushout
    {f : Pair.Hom S T} {g : Pair.Hom S U} {i : Pair.Hom T W} {j : Pair.Hom U W}
    (hpush : IsCompletedPushout f g i j) :
    presentationLimitPreAdicSpacePairComap PB PE hB hE hsheafE i ≫
        presentationLimitPreAdicSpacePairComap PA PB hA hB hsheafB f =
      presentationLimitPreAdicSpacePairComap PC PE hC hE hsheafE j ≫
        presentationLimitPreAdicSpacePairComap PA PC hA hC hsheafC g := by
  rw [← presentationLimitPreAdicSpacePairComap_comp PA PB PE hA hB hE hsheafB hsheafE,
    ← presentationLimitPreAdicSpacePairComap_comp PA PC PE hA hC hE hsheafC hsheafE,
    hpush.condition]

end Condition

section UniversalProperty

variable {A B C E : Type u}
  [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsHuberRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T0Space B] [IsHuberRing B]
  [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [CompleteSpace C] [T0Space C] [IsHuberRing C]
  [CommRing E] [UniformSpace E] [IsUniformAddGroup E] [IsTopologicalRing E]
  [CompleteSpace E] [T0Space E] [IsHuberRing E]
  {S : Pair A} {T : Pair B} {U : Pair C} {W : Pair E}
  (PA : PairOfDefinition A) (PB : PairOfDefinition B)
  (PC : PairOfDefinition C) (PE : PairOfDefinition E)
  (hA : PA.ringOfDefinition ≤ S.plus) (hB : PB.ringOfDefinition ≤ T.plus)
  (hC : PC.ringOfDefinition ≤ U.plus) (hE : PE.ringOfDefinition ≤ W.plus)
  (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
    (presentationLimitPresheaf PB T.plus))
  (hsheafC : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U.plus))
    (presentationLimitPresheaf PC U.plus))
  (hsheafE : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa W.plus))
    (presentationLimitPresheaf PE W.plus))
  {f : Pair.Hom S T} {g : Pair.Hom S U} {i : Pair.Hom T W} {j : Pair.Hom U W}
  (hpush : IsCompletedPushout f g i j)

include hpush in
/-- **Affinoid test case**: compatible morphisms from a sheafy complete Hausdorff affinoid spectrum
`Spa(D, D⁺)` into `Spa(B, B⁺)` and `Spa(C, C⁺)` factor uniquely through `Spa(E, E⁺)`. -/
theorem existsUnique_presentationLimitPreAdicSpacePairComap_of_isCompletedPushout
    {D : Type u} [CommRing D] [UniformSpace D] [IsUniformAddGroup D] [IsTopologicalRing D]
    [CompleteSpace D] [T0Space D] [IsHuberRing D]
    (PD : PairOfDefinition D) (V : Pair D) (hD : PD.ringOfDefinition ≤ V.plus)
    (hsheafD : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa V.plus))
      (presentationLimitPresheaf PD V.plus))
    (u : presentationLimitPreAdicSpace PD V.plus
      V.isRingOfIntegralElements.isPowerBounded_of_mem hD ⟶
      presentationLimitPreAdicSpace PB T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hB)
    (v : presentationLimitPreAdicSpace PD V.plus
      V.isRingOfIntegralElements.isPowerBounded_of_mem hD ⟶
      presentationLimitPreAdicSpace PC U.plus
        U.isRingOfIntegralElements.isPowerBounded_of_mem hC)
    (huv : u ≫ presentationLimitPreAdicSpacePairComap PA PB hA hB hsheafB f =
      v ≫ presentationLimitPreAdicSpacePairComap PA PC hA hC hsheafC g) :
    ∃! l : presentationLimitPreAdicSpace PD V.plus
        V.isRingOfIntegralElements.isPowerBounded_of_mem hD ⟶
        presentationLimitPreAdicSpace PE W.plus
          W.isRingOfIntegralElements.isPowerBounded_of_mem hE,
      l ≫ presentationLimitPreAdicSpacePairComap PB PE hB hE hsheafE i = u ∧
        l ≫ presentationLimitPreAdicSpacePairComap PC PE hC hE hsheafE j = v := by
  let a := presentationLimitHomPairHom PB PD T V hB hD u
  let b := presentationLimitHomPairHom PC PD U V hC hD v
  have hab : a.comp f = b.comp g := by
    have h := congrArg (presentationLimitHomPairHom PA PD S V hA hD) huv
    rw [presentationLimitHomPairHom_comp PA PB PD S T V hA hB hD,
      presentationLimitHomPairHom_comp PA PC PD S U V hA hC hD,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap PA PB S T hA hB hsheafB,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap PA PC S U hA hC hsheafC]
      at h
    exact h
  refine ⟨presentationLimitPreAdicSpacePairComap PE PD hE hD hsheafD (hpush.desc a b hab),
    ⟨?_, ?_⟩, ?_⟩
  · rw [← presentationLimitPreAdicSpacePairComap_comp PB PE PD hB hE hD hsheafE hsheafD,
      hpush.desc_comp_left,
      presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom PB PD T V hB hD hsheafD]
  · rw [← presentationLimitPreAdicSpacePairComap_comp PC PE PD hC hE hD hsheafE hsheafD,
      hpush.desc_comp_right,
      presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom PC PD U V hC hD hsheafD]
  · rintro l ⟨hli, hlj⟩
    refine presentationLimitPreAdicSpace_hom_ext_pairHom PE PD W V hE hD hsheafD ?_
    rw [presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap PE PD W V hE hD hsheafD]
    refine hpush.hom_ext ?_ ?_
    · have hi := congrArg (presentationLimitHomPairHom PB PD T V hB hD) hli
      rw [presentationLimitHomPairHom_comp PB PE PD T W V hB hE hD,
        presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap PB PE T W hB hE hsheafE]
        at hi
      exact hi.trans (hpush.desc_comp_left a b hab).symm
    · have hj := congrArg (presentationLimitHomPairHom PC PD U V hC hD) hlj
      rw [presentationLimitHomPairHom_comp PC PE PD U W V hC hE hD,
        presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap PC PE U W hC hE hsheafE]
        at hj
      exact hj.trans (hpush.desc_comp_right a b hab).symm

include hA hsheafB hsheafC hpush in
/-- **Joint monomorphicity out of any adic space**: two morphisms `X ⟶ Spa(E, E⁺)` out of an adic
space `X` whose compositions to `Spa(B, B⁺)` and `Spa(C, C⁺)` agree are equal. -/
theorem presentationLimitPreAdicSpace_hom_ext_of_isCompletedPushout
    {X : PreAdicSpace.{u}} (hX : isAdic X)
    {l₁ l₂ : X ⟶ presentationLimitPreAdicSpace PE W.plus
      W.isRingOfIntegralElements.isPowerBounded_of_mem hE}
    (hi : l₁ ≫ presentationLimitPreAdicSpacePairComap PB PE hB hE hsheafE i =
      l₂ ≫ presentationLimitPreAdicSpacePairComap PB PE hB hE hsheafE i)
    (hj : l₁ ≫ presentationLimitPreAdicSpacePairComap PC PE hC hE hsheafE j =
      l₂ ≫ presentationLimitPreAdicSpacePairComap PC PE hC hE hsheafE j) :
    l₁ = l₂ := by
  refine hom_ext_of_ofRestrict hX.isSheafy (fun O : X.affinoidOpens ↦ O.1)
    hX.isLocallyAffinoid.iSup_affinoidOpens_eq_top fun O ↦ ?_
  obtain ⟨D, _, _, _, _, _, _, _, V, PD, hD, hsheafD, ⟨e⟩⟩ :=
    hX.isSheafy.exists_complete_isSheaf_of_mem_affinoidOpens O.2
  rw [← cancel_epi e.inv]
  have hcond : ((e.inv ≫ X.ofRestrict O.1.isOpenEmbedding ≫ l₂) ≫
        presentationLimitPreAdicSpacePairComap PB PE hB hE hsheafE i) ≫
          presentationLimitPreAdicSpacePairComap PA PB hA hB hsheafB f =
      ((e.inv ≫ X.ofRestrict O.1.isOpenEmbedding ≫ l₂) ≫
        presentationLimitPreAdicSpacePairComap PC PE hC hE hsheafE j) ≫
          presentationLimitPreAdicSpacePairComap PA PC hA hC hsheafC g := by
    simp only [Category.assoc,
      presentationLimitPreAdicSpacePairComap_condition_of_isCompletedPushout
        PA PB PC PE hA hB hC hE hsheafB hsheafC hsheafE hpush]
  exact (existsUnique_presentationLimitPreAdicSpacePairComap_of_isCompletedPushout
    PA PB PC PE hA hB hC hE hsheafB hsheafC hsheafE hpush PD V hD hsheafD
    ((e.inv ≫ X.ofRestrict O.1.isOpenEmbedding ≫ l₂) ≫
      presentationLimitPreAdicSpacePairComap PB PE hB hE hsheafE i)
    ((e.inv ≫ X.ofRestrict O.1.isOpenEmbedding ≫ l₂) ≫
      presentationLimitPreAdicSpacePairComap PC PE hC hE hsheafE j)
    hcond).unique
    ⟨by simp only [Category.assoc, hi], by simp only [Category.assoc, hj]⟩ ⟨rfl, rfl⟩

include hpush in
/-- **Universal property of a completed pushout against any adic space**: compatible morphisms from
an adic space `X` into `Spa(B, B⁺)` and `Spa(C, C⁺)` over `Spa(A, A⁺)` lift uniquely to a morphism
`X ⟶ Spa(E, E⁺)`. -/
theorem existsUnique_presentationLimitPreAdicSpace_lift_of_isCompletedPushout
    {X : PreAdicSpace.{u}} (hX : isAdic X)
    (u : X ⟶ presentationLimitPreAdicSpace PB T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hB)
    (v : X ⟶ presentationLimitPreAdicSpace PC U.plus
      U.isRingOfIntegralElements.isPowerBounded_of_mem hC)
    (huv : u ≫ presentationLimitPreAdicSpacePairComap PA PB hA hB hsheafB f =
      v ≫ presentationLimitPreAdicSpacePairComap PA PC hA hC hsheafC g) :
    ∃! l : X ⟶ presentationLimitPreAdicSpace PE W.plus
        W.isRingOfIntegralElements.isPowerBounded_of_mem hE,
      l ≫ presentationLimitPreAdicSpacePairComap PB PE hB hE hsheafE i = u ∧
        l ≫ presentationLimitPreAdicSpacePairComap PC PE hC hE hsheafE j = v := by
  let hcov := hX.isLocallyAffinoid.iSup_affinoidOpens_eq_top
  -- Construct local lifts on each open affinoid subspace via complete Hausdorff models.
  have hloc (O : X.affinoidOpens) :
      ∃ l : X.restrict O.1.isOpenEmbedding ⟶
          presentationLimitPreAdicSpace PE W.plus
            W.isRingOfIntegralElements.isPowerBounded_of_mem hE,
        l ≫ presentationLimitPreAdicSpacePairComap PB PE hB hE hsheafE i =
          X.ofRestrict O.1.isOpenEmbedding ≫ u ∧
        l ≫ presentationLimitPreAdicSpacePairComap PC PE hC hE hsheafE j =
          X.ofRestrict O.1.isOpenEmbedding ≫ v := by
    obtain ⟨D, _, _, _, _, _, _, _, V, PD, hD, hsheafD, ⟨e⟩⟩ :=
      hX.isSheafy.exists_complete_isSheaf_of_mem_affinoidOpens O.2
    obtain ⟨l₀, ⟨hl₀i, hl₀j⟩, -⟩ :=
      existsUnique_presentationLimitPreAdicSpacePairComap_of_isCompletedPushout
        PA PB PC PE hA hB hC hE hsheafB hsheafC hsheafE hpush PD V hD hsheafD
        (e.inv ≫ X.ofRestrict O.1.isOpenEmbedding ≫ u)
        (e.inv ≫ X.ofRestrict O.1.isOpenEmbedding ≫ v)
        (by simp only [Category.assoc, huv])
    exact ⟨e.hom ≫ l₀,
      by rw [Category.assoc, hl₀i, e.hom_inv_id_assoc],
      by rw [Category.assoc, hl₀j, e.hom_inv_id_assoc]⟩
  choose loc hloci hlocj using hloc
  -- Overlaps of open affinoid subspaces are open subspaces of `X`, hence adic spaces, so local
  -- lifts agree on overlaps by joint monomorphicity.
  have hcompat : ∀ O₁ O₂ : X.affinoidOpens,
      pullback.fst (X.ofRestrict O₁.1.isOpenEmbedding) (X.ofRestrict O₂.1.isOpenEmbedding) ≫
        loc O₁ = pullback.snd _ _ ≫ loc O₂ := by
    intro O₁ O₂
    have hP : isAdic
        (pullback (X.ofRestrict O₁.1.isOpenEmbedding) (X.ofRestrict O₂.1.isOpenEmbedding)) :=
      isAdic_of_isOpenImmersion hX
        (pullback.fst (X.ofRestrict O₁.1.isOpenEmbedding) (X.ofRestrict O₂.1.isOpenEmbedding) ≫
          X.ofRestrict O₁.1.isOpenEmbedding)
    refine presentationLimitPreAdicSpace_hom_ext_of_isCompletedPushout
      PA PB PC PE hA hB hC hE hsheafB hsheafC hsheafE hpush hP ?_ ?_
    · rw [Category.assoc, hloci, Category.assoc, hloci, pullback.condition_assoc]
    · rw [Category.assoc, hlocj, Category.assoc, hlocj, pullback.condition_assoc]
  refine ⟨glueMorphisms hX.isSheafy (fun O : X.affinoidOpens ↦ O.1) hcov loc hcompat,
    ⟨?_, ?_⟩, fun l ⟨hli, hlj⟩ ↦ ?_⟩
  · refine hom_ext_of_ofRestrict hX.isSheafy (fun O : X.affinoidOpens ↦ O.1) hcov fun O ↦ ?_
    rw [ofRestrict_glueMorphisms_assoc, hloci]
  · refine hom_ext_of_ofRestrict hX.isSheafy (fun O : X.affinoidOpens ↦ O.1) hcov fun O ↦ ?_
    rw [ofRestrict_glueMorphisms_assoc, hlocj]
  · refine hom_ext_of_ofRestrict hX.isSheafy (fun O : X.affinoidOpens ↦ O.1) hcov fun O ↦ ?_
    refine presentationLimitPreAdicSpace_hom_ext_of_isCompletedPushout
      PA PB PC PE hA hB hC hE hsheafB hsheafC hsheafE hpush (isAdic_restrict _ hX) ?_ ?_
    · rw [Category.assoc, hli, ofRestrict_glueMorphisms, hloci]
    · rw [Category.assoc, hlj, ofRestrict_glueMorphisms, hlocj]

end UniversalProperty

end TauCeti.ValuationSpectrum

namespace TauCeti.AdicSpace

open Huber PreAdicSpace ValuationSpectrum

universe u

section CompletedPushout

variable {A B C E : Type u}
  [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsHuberRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T0Space B] [IsHuberRing B]
  [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [CompleteSpace C] [T0Space C] [IsHuberRing C]
  [CommRing E] [UniformSpace E] [IsUniformAddGroup E] [IsTopologicalRing E]
  [CompleteSpace E] [T0Space E] [IsHuberRing E]

/-- **Pullback square in `AdicSpace` for explicit presentations**: any completed pushout square of
complete Hausdorff sheafy Huber pairs induces a pullback square of their presentation-limit adic
spaces. -/
theorem isPullback_ofPresentation_of_isCompletedPushout
    {S : Pair A} {T : Pair B} {U : Pair C} {W : Pair E}
    (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (PC : PairOfDefinition C) (PE : PairOfDefinition E)
    (hA : PA.ringOfDefinition ≤ S.plus) (hB : PB.ringOfDefinition ≤ T.plus)
    (hC : PC.ringOfDefinition ≤ U.plus) (hE : PE.ringOfDefinition ≤ W.plus)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf PA S.plus))
    (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf PB T.plus))
    (hsheafC : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U.plus))
      (presentationLimitPresheaf PC U.plus))
    (hsheafE : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa W.plus))
      (presentationLimitPresheaf PE W.plus))
    {f : Pair.Hom S T} {g : Pair.Hom S U} {i : Pair.Hom T W} {j : Pair.Hom U W}
    (hpush : IsCompletedPushout f g i j) :
    IsPullback
      (comapOfPresentation T PB hB hsheafB W PE hE hsheafE i)
      (comapOfPresentation U PC hC hsheafC W PE hE hsheafE j)
      (comapOfPresentation S PA hA hsheafA T PB hB hsheafB f)
      (comapOfPresentation S PA hA hsheafA U PC hC hsheafC g) := by
  have hw : comapOfPresentation T PB hB hsheafB W PE hE hsheafE i ≫
        comapOfPresentation S PA hA hsheafA T PB hB hsheafB f =
      comapOfPresentation U PC hC hsheafC W PE hE hsheafE j ≫
        comapOfPresentation S PA hA hsheafA U PC hC hsheafC g := by
    ext1
    simp only [ObjectProperty.FullSubcategory.comp_hom, comapOfPresentation_hom]
    exact presentationLimitPreAdicSpacePairComap_condition_of_isCompletedPushout
      PA PB PC PE hA hB hC hE hsheafB hsheafC hsheafE hpush
  refine { w := hw, isLimit' := ⟨PullbackCone.isLimitAux' _ fun s ↦ ?_⟩ }
  have hcond : s.fst.hom ≫ presentationLimitPreAdicSpacePairComap PA PB hA hB hsheafB f =
      s.snd.hom ≫ presentationLimitPreAdicSpacePairComap PA PC hA hC hsheafC g := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom, comapOfPresentation_hom] using
      congrArg InducedCategory.Hom.hom s.condition
  have hs := existsUnique_presentationLimitPreAdicSpace_lift_of_isCompletedPushout
    PA PB PC PE hA hB hC hE hsheafB hsheafC hsheafE hpush s.pt.property s.fst.hom s.snd.hom hcond
  refine ⟨ObjectProperty.homMk hs.choose, ?_, ?_, fun {m} hm₁ hm₂ ↦ ?_⟩
  · ext1
    simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      PullbackCone.mk_fst, comapOfPresentation_hom] using hs.choose_spec.1.1
  · ext1
    simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      PullbackCone.mk_snd, comapOfPresentation_hom] using hs.choose_spec.1.2
  · ext1
    refine hs.choose_spec.2 m.hom ⟨?_, ?_⟩
    · simpa only [ObjectProperty.FullSubcategory.comp_hom, PullbackCone.mk_fst,
        comapOfPresentation_hom] using congrArg InducedCategory.Hom.hom hm₁
    · simpa only [ObjectProperty.FullSubcategory.comp_hom, PullbackCone.mk_snd,
        comapOfPresentation_hom] using congrArg InducedCategory.Hom.hom hm₂

/-- **Pullback square in `AdicSpace` for a completed pushout of Huber pairs**: any completed pushout
square `IsCompletedPushout f g i j` between complete Hausdorff sheafy Huber pairs induces a
pullback square in `AdicSpace`. -/
theorem isPullback_ofPair_of_isCompletedPushout
    {S : Pair A} {T : Pair B} {U : Pair C} {W : Pair E}
    (hS : IsSheafyForEveryPresentation S.plus)
    (hT : IsSheafyForEveryPresentation T.plus)
    (hU : IsSheafyForEveryPresentation U.plus)
    (hW : IsSheafyForEveryPresentation W.plus)
    {f : Pair.Hom S T} {g : Pair.Hom S U} {i : Pair.Hom T W} {j : Pair.Hom U W}
    (hpush : IsCompletedPushout f g i j) :
    IsPullback
      (comapOfPair hT hW i) (comapOfPair hU hW j)
      (comapOfPair hS hT f) (comapOfPair hS hU g) := by
  obtain ⟨PA, hPA, -⟩ := hS.exists_compatible_isSheaf
  obtain ⟨PB, hPB, -⟩ := hT.exists_compatible_isSheaf
  obtain ⟨PC, hPC, -⟩ := hU.exists_compatible_isSheaf
  obtain ⟨PE, hPE, -⟩ := hW.exists_compatible_isSheaf
  exact (isPullback_ofPresentation_of_isCompletedPushout PA PB PC PE hPA hPB hPC hPE
    (hS.isSheaf PA hPA) (hT.isSheaf PB hPB) (hU.isSheaf PC hPC) (hW.isSheaf PE hPE) hpush).of_iso'
    (ofPairIsoOfPresentation W hW PE hPE)
    (ofPairIsoOfPresentation T hT PB hPB)
    (ofPairIsoOfPresentation U hU PC hPC)
    (ofPairIsoOfPresentation S hS PA hPA)
    (ofPairIsoOfPresentation_hom_comapOfPresentation hT hW PB hPB PE hPE i)
    (ofPairIsoOfPresentation_hom_comapOfPresentation hU hW PC hPC PE hPE j)
    (ofPairIsoOfPresentation_hom_comapOfPresentation hS hT PA hPA PB hPB f)
    (ofPairIsoOfPresentation_hom_comapOfPresentation hS hU PA hPA PC hPC g)

end CompletedPushout

section CompletedTensor

variable {A B C : Type u}
  [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsHuberRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T0Space B] [IsHuberRing B]
  [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [CompleteSpace C] [T0Space C] [IsHuberRing C]
  [Algebra A B] [Algebra A C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- **Affinoid fibre products in `AdicSpace` for explicit presentations**: when the completed tensor
product `(B, B⁺) ⊗̂_A (C, C⁺)` along adic structure maps is sheafy, its presentation-limit adic
space is a pullback of `Spa(B, B⁺)` and `Spa(C, C⁺)` over `Spa(A, A⁺)`. -/
theorem isPullback_ofPresentation_completedTensor
    {S : Pair A} {T : Pair B} {U : Pair C}
    (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (PC : PairOfDefinition C) (PE : PairOfDefinition (CompletedTensor A B C))
    (hA : PA.ringOfDefinition ≤ S.plus) (hB : PB.ringOfDefinition ≤ T.plus)
    (hC : PC.ringOfDefinition ≤ U.plus) (hE : PE.ringOfDefinition ≤ (T.completedTensor A U).plus)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf PA S.plus))
    (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf PB T.plus))
    (hsheafC : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U.plus))
      (presentationLimitPresheaf PC U.plus))
    (hsheafE : Presheaf.IsSheaf
      (Opens.grothendieckTopology ↥(spa (T.completedTensor A U).plus))
      (presentationLimitPresheaf PE (T.completedTensor A U).plus))
    (f : Pair.Hom S T) (g : Pair.Hom S U)
    (hf : f.toRingHom = algebraMap A B) (hg : g.toRingHom = algebraMap A C) :
    IsPullback
      (comapOfPresentation T PB hB hsheafB (T.completedTensor A U) PE hE hsheafE
        (Pair.completedTensor.inl A T U))
      (comapOfPresentation U PC hC hsheafC (T.completedTensor A U) PE hE hsheafE
        (Pair.completedTensor.inr A T U))
      (comapOfPresentation S PA hA hsheafA T PB hB hsheafB f)
      (comapOfPresentation S PA hA hsheafA U PC hC hsheafC g) :=
  isPullback_ofPresentation_of_isCompletedPushout PA PB PC PE hA hB hC hE
    hsheafA hsheafB hsheafC hsheafE (Pair.completedTensor.isCompletedPushout f g hf hg)

/-- **Fibre product of affinoid adic spaces** (Huber 1994, Proposition 3.7; Huber 1996,
Proposition 1.2.2; Wedhorn, Theorem 8.56): let `(A, A⁺)`, `(B, B⁺)` and `(C, C⁺)` be sheafy
complete Hausdorff Huber pairs and `f : (A, A⁺) → (B, B⁺)`, `g : (A, A⁺) → (C, C⁺)` adic morphisms
of Huber pairs. Whenever the completed tensor product `(B, B⁺) ⊗̂_A (C, C⁺)` is sheafy, its adic
spectrum is the pullback of `Spa(B, B⁺) ⟶ Spa(A, A⁺)` and `Spa(C, C⁺) ⟶ Spa(A, A⁺)` in
`AdicSpace`. -/
theorem affinoid_isPullback
    {S : Pair A} {T : Pair B} {U : Pair C}
    (hS : IsSheafyForEveryPresentation S.plus)
    (hT : IsSheafyForEveryPresentation T.plus)
    (hU : IsSheafyForEveryPresentation U.plus)
    (hTU : IsSheafyForEveryPresentation (T.completedTensor A U).plus)
    (f : Pair.Hom S T) (g : Pair.Hom S U)
    (hf : f.toRingHom = algebraMap A B) (hg : g.toRingHom = algebraMap A C) :
    IsPullback
      (comapOfPair hT hTU (Pair.completedTensor.inl A T U))
      (comapOfPair hU hTU (Pair.completedTensor.inr A T U))
      (comapOfPair hS hT f)
      (comapOfPair hS hU g) :=
  isPullback_ofPair_of_isCompletedPushout hS hT hU hTU
    (Pair.completedTensor.isCompletedPushout f g hf hg)

/-- **Unconditional affinoid fibre product over a stably sheafy left factor** (Wedhorn,
Theorem 8.56): when `B` is stably sheafy and `A → C` is topologically of finite type, the completed
tensor product `(B, B⁺) ⊗̂_A (C, C⁺)` is automatically sheafy and gives a pullback square in
`AdicSpace`. -/
theorem affinoid_isPullback_of_isStablySheafyRing_left
    {S : Pair A} {T : Pair B} {U : Pair C}
    (hS : IsSheafyForEveryPresentation S.plus)
    (hU : IsSheafyForEveryPresentation U.plus)
    (hB : IsStablySheafyRing.{u, u} B)
    (hC : IsTopologicallyFiniteType (algebraMap A C))
    (f : Pair.Hom S T) (g : Pair.Hom S U)
    (hf : f.toRingHom = algebraMap A B) (hg : g.toRingHom = algebraMap A C) :
    IsPullback
      (comapOfPair
        (hB.isSheafyRing.isSheafyForEveryPresentation T.isRingOfIntegralElements)
        (isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_left T U hB hC)
        (Pair.completedTensor.inl A T U))
      (comapOfPair hU
        (isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_left T U hB hC)
        (Pair.completedTensor.inr A T U))
      (comapOfPair hS
        (hB.isSheafyRing.isSheafyForEveryPresentation T.isRingOfIntegralElements) f)
      (comapOfPair hS hU g) :=
  affinoid_isPullback hS _ hU _ f g hf hg

/-- **Unconditional affinoid fibre product over a stably sheafy right factor**: symmetric form of
`affinoid_isPullback_of_isStablySheafyRing_left` when `C` is stably sheafy and `A → B` is
topologically of finite type. -/
theorem affinoid_isPullback_of_isStablySheafyRing_right
    {S : Pair A} {T : Pair B} {U : Pair C}
    (hS : IsSheafyForEveryPresentation S.plus)
    (hT : IsSheafyForEveryPresentation T.plus)
    (hC : IsStablySheafyRing.{u, u} C)
    (hB : IsTopologicallyFiniteType (algebraMap A B))
    (f : Pair.Hom S T) (g : Pair.Hom S U)
    (hf : f.toRingHom = algebraMap A B) (hg : g.toRingHom = algebraMap A C) :
    IsPullback
      (comapOfPair hT
        (isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_right T U hC hB)
        (Pair.completedTensor.inl A T U))
      (comapOfPair
        (hC.isSheafyRing.isSheafyForEveryPresentation U.isRingOfIntegralElements)
        (isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_right T U hC hB)
        (Pair.completedTensor.inr A T U))
      (comapOfPair hS hT f)
      (comapOfPair hS
        (hC.isSheafyRing.isSheafyForEveryPresentation U.isRingOfIntegralElements) g) :=
  affinoid_isPullback hS hT _ _ f g hf hg

end CompletedTensor

section ProjectionsAndPoints

variable {A B C : Type u}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  [Algebra A B] [Algebra A C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- The first projection `Spa((B, B⁺) ⊗̂_A (C, C⁺)) ⟶ Spa(B, B⁺)` is an adic morphism. -/
theorem isAdic_comapOfPair_completedTensor_inl {T : Pair B} {U : Pair C}
    (hT : IsSheafyForEveryPresentation T.plus)
    (hTU : IsSheafyForEveryPresentation (T.completedTensor A U).plus) :
    IsAdic (comapOfPair hT hTU (Pair.completedTensor.inl A T U)) := by
  rw [isAdic_comapOfPair_iff, Pair.completedTensor.toRingHom_inl]
  exact CompletedTensor.isAdicHom_inl A B C

/-- The second projection `Spa((B, B⁺) ⊗̂_A (C, C⁺)) ⟶ Spa(C, C⁺)` is an adic morphism. -/
theorem isAdic_comapOfPair_completedTensor_inr {T : Pair B} {U : Pair C}
    (hU : IsSheafyForEveryPresentation U.plus)
    (hTU : IsSheafyForEveryPresentation (T.completedTensor A U).plus) :
    IsAdic (comapOfPair hU hTU (Pair.completedTensor.inr A T U)) := by
  rw [isAdic_comapOfPair_iff, Pair.completedTensor.toRingHom_inr]
  exact CompletedTensor.isAdicHom_inr A B C

/-- If `A → C` is topologically of finite type, the first projection
`Spa((B, B⁺) ⊗̂_A (C, C⁺)) ⟶ Spa(B, B⁺)` is locally of weakly finite type. -/
theorem locallyOfWeaklyFiniteType_comapOfPair_completedTensor_inl [IsHuberRing A]
    {T : Pair B} {U : Pair C}
    (hT : IsSheafyForEveryPresentation T.plus)
    (hTU : IsSheafyForEveryPresentation (T.completedTensor A U).plus)
    (hC : IsTopologicallyFiniteType (algebraMap A C)) :
    LocallyOfWeaklyFiniteType (comapOfPair hT hTU (Pair.completedTensor.inl A T U)) :=
  locallyOfWeaklyFiniteType_comapOfPair hT hTU _ <| by
    rw [Pair.completedTensor.toRingHom_inl]
    exact CompletedTensor.isTopologicallyFiniteType_inl hC

/-- If `A → B` is topologically of finite type, the second projection
`Spa((B, B⁺) ⊗̂_A (C, C⁺)) ⟶ Spa(C, C⁺)` is locally of weakly finite type. -/
theorem locallyOfWeaklyFiniteType_comapOfPair_completedTensor_inr [IsHuberRing A]
    {T : Pair B} {U : Pair C}
    (hU : IsSheafyForEveryPresentation U.plus)
    (hTU : IsSheafyForEveryPresentation (T.completedTensor A U).plus)
    (hB : IsTopologicallyFiniteType (algebraMap A B)) :
    LocallyOfWeaklyFiniteType (comapOfPair hU hTU (Pair.completedTensor.inr A T U)) :=
  locallyOfWeaklyFiniteType_comapOfPair hU hTU _ <| by
    rw [Pair.completedTensor.toRingHom_inr]
    exact CompletedTensor.isTopologicallyFiniteType_inr hB

/-- **Surjectivity onto compatible points over a Tate base**: when `A` is a Tate ring, any two
points of `Spa(B, B⁺)` and `Spa(C, C⁺)` with the same image in `Spa(A, A⁺)` lift to a point of
`Spa((B, B⁺) ⊗̂_A (C, C⁺))` under the two projections. -/
theorem exists_ofPair_completedTensor_point [IsTateRing A]
    {S : Pair A} {T : Pair B} {U : Pair C}
    (hS : IsSheafyForEveryPresentation S.plus)
    (hT : IsSheafyForEveryPresentation T.plus)
    (hU : IsSheafyForEveryPresentation U.plus)
    (hTU : IsSheafyForEveryPresentation (T.completedTensor A U).plus)
    (f : Pair.Hom S T) (g : Pair.Hom S U)
    (hf : f.toRingHom = algebraMap A B) (hg : g.toRingHom = algebraMap A C)
    (x : (ofPair T hT).obj) (y : (ofPair U hU).obj)
    (hxy : (comapOfPair hS hT f).hom.base x = (comapOfPair hS hU g).hom.base y) :
    ∃ z : (ofPair (T.completedTensor A U) hTU).obj,
      (comapOfPair hT hTU (Pair.completedTensor.inl A T U)).hom.base z = x ∧
        (comapOfPair hU hTU (Pair.completedTensor.inr A T U)).hom.base z = y := by
  have hxy' : f.spaComap (ofPairHomeomorph T hT x) = g.spaComap (ofPairHomeomorph U hU y) := by
    have h := congrArg (ofPairHomeomorph S hS) hxy
    simpa only [ofPairHomeomorph_comapOfPair_apply] using h
  obtain ⟨z₀, hz₁, hz₂⟩ := exists_spaPoint_of_isCompletedPushout
    (Pair.completedTensor.isCompletedPushout f g hf hg)
    (ofPairHomeomorph T hT x) (ofPairHomeomorph U hU y) hxy'
  exact ⟨(ofPairHomeomorph (T.completedTensor A U) hTU).symm z₀, by simp [hz₁], by simp [hz₂]⟩

end ProjectionsAndPoints

end TauCeti.AdicSpace
