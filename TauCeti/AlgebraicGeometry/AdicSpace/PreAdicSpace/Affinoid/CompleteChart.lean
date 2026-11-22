/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Open
public import TauCeti.RingTheory.Huber.LocalizationTopology.BaseChange

import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Completed presentations via `{1} / 1`

This module packages the trivial `{1} / 1` rational-localisation completion of a sheafy
presentation `(P, S)` into a `CompleteAffinoidOpen` interface built on
`TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Open`:

* **Completed presentations**: `CompleteAffinoidOpen.ofCompletion` produces a complete Hausdorff
  sheafy `CompleteAffinoidOpen` over `Spa(A, A⁺)`, with canonical pair morphism
  `CompleteAffinoidOpen.toCompletionHom`, surjectivity on underlying points
  (`range_ofCompletion_hom_base`), and finite-type / discrete finite-presentation lemmas
  (`isTopologicallyFiniteType_toCompletionHom`, `finitePresentation_toCompletionHom`).
* **Functoriality and commuting completion square**: `CompleteAffinoidOpen.ofCompletionMap` lifts
  any Huber-pair morphism `φ : S → T` between sheafy presentations to a morphism between their
  `{1} / 1` completions, obeying naturality (`ofCompletionMap_comp_toCompletionHom`), the
  commuting-square law (`pairComap_ofCompletionMap_comp_hom`), and preservation of topological
  finite type (`isTopologicallyFiniteType_ofCompletionMap`).

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2–§3.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remarks 8.4 and 8.8, and
  Definition 8.48.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti.PreAdicSpace.CompleteAffinoidOpen

open Huber Huber.PairOfDefinition ValuationSpectrum

universe u

section Single

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {S : Pair A} (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
    (presentationLimitPresheaf P S.plus))

/-- Complete Hausdorff affinoid open `Spa(A⟨{1}/1⟩, A⟨{1}/1⟩⁺) ⟶ Spa(A, A⁺)` obtained by completing
a sheafy presentation `(P, S)` via the trivial rational localisation `R({1} / 1)`. -/
@[expose]
noncomputable def ofCompletion :
    CompleteAffinoidOpen (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  ofRationalLocalization P hP hsheaf (𝟙 _) ({1} : Finset A) 1 (by simp)

/-- Canonical Huber-pair morphism `S → (ofCompletion P hP hsheaf).pair` from a sheafy
presentation into its `{1} / 1` completion. -/
@[expose]
noncomputable def toCompletionHom : Pair.Hom S (ofCompletion P hP hsheaf).pair :=
  toRationalLocalizationHom P hP hsheaf (𝟙 _) ({1} : Finset A) 1 (by simp)

/-- The structure morphism of `ofCompletion` is the morphism induced by `toCompletionHom`. -/
@[reassoc]
theorem ofCompletion_hom :
    (ofCompletion P hP hsheaf).hom =
      presentationLimitPreAdicSpacePairComap P (ofCompletion P hP hsheaf).pairOfDefinition hP
        (ofCompletion P hP hsheaf).le_plus (ofCompletion P hP hsheaf).isSheaf
        (toCompletionHom P hP hsheaf) :=
  Category.comp_id _

/-- The structure morphism of `ofCompletion` is surjective on underlying points. -/
@[simp]
theorem range_ofCompletion_hom_base :
    Set.range (ofCompletion P hP hsheaf).hom.base = Set.univ := by
  rw [ofCompletion_hom]
  exact (range_toRationalLocalizationComap_base P hP hsheaf (𝟙 _) ({1} : Finset A) 1
    (by simp)).trans (by rw [spaBasicOpen_singleton_one, Opens.coe_top]; rfl)

/-- The canonical completion morphism `toCompletionHom` is topologically of finite type. -/
theorem isTopologicallyFiniteType_toCompletionHom :
    (toCompletionHom P hP hsheaf).IsTopologicallyFiniteType :=
  isTopologicallyFiniteType_toRationalLocalizationHom P hP hsheaf (𝟙 _) ({1} : Finset A) 1 (by simp)

/-- When `A` is discrete, the underlying ring homomorphism of `toCompletionHom` is algebraically of
finite presentation (`RingHom.FinitePresentation`). -/
theorem finitePresentation_toCompletionHom [DiscreteTopology A] :
    (toCompletionHom P hP hsheaf).toRingHom.FinitePresentation :=
  finitePresentation_toRationalLocalizationHom P hP hsheaf (𝟙 _) ({1} : Finset A) 1 (by simp)

end Single

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {S : Pair A} (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
  (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
    (presentationLimitPresheaf P S.plus))
  {T : Pair B} (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
  (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
    (presentationLimitPresheaf P' T.plus))

/-- Canonical morphism of completed Huber pairs
`(ofCompletion P hP hsheafA).pair → (ofCompletion P' hP' hsheafB).pair` induced by a Huber-pair
morphism `φ : S → T` via `{1} / 1` rational base change. -/
@[expose]
noncomputable def ofCompletionMap (φ : Pair.Hom S T) :
    Pair.Hom (ofCompletion P hP hsheafA).pair (ofCompletion P' hP' hsheafB).pair :=
  P.completionLocPairMap S hP ({1} : Finset A) 1 (Localization.Away (1 : A))
    (P.hasDenominatorPower_of_isOpen_span ({1} : Finset A) 1 _ (by simp))
    P' T hP' φ ({1} : Finset B) 1 (Localization.Away (1 : B))
    (P'.hasDenominatorPower_of_isOpen_span ({1} : Finset B) 1 _ (by simp))
    (map_one φ.toRingHom) (by simp)

/-- Naturality of `toCompletionHom` with respect to `ofCompletionMap` at the level of Huber
pairs. -/
theorem ofCompletionMap_comp_toCompletionHom (φ : Pair.Hom S T) :
    (ofCompletionMap P hP hsheafA P' hP' hsheafB φ).comp (toCompletionHom P hP hsheafA) =
      (toCompletionHom P' hP' hsheafB).comp φ :=
  P.completionLocPairMap_comp_toCompletionLocHom S hP ({1} : Finset A) 1 (Localization.Away (1 : A))
    (P.hasDenominatorPower_of_isOpen_span ({1} : Finset A) 1 _ (by simp))
    P' T hP' φ ({1} : Finset B) 1 (Localization.Away (1 : B))
    (P'.hasDenominatorPower_of_isOpen_span ({1} : Finset B) 1 _ (by simp))
    (map_one φ.toRingHom) (by simp)

/-- **Commuting completion square**: `pairComap` of `ofCompletionMap` intertwines the completion
isomorphisms `(ofCompletion ...).hom` with `presentationLimitPreAdicSpacePairComap`. -/
@[reassoc]
theorem pairComap_ofCompletionMap_comp_hom (φ : Pair.Hom S T) :
    (ofCompletion P hP hsheafA).pairComap (ofCompletion P' hP' hsheafB)
        (ofCompletionMap P hP hsheafA P' hP' hsheafB φ) ≫
      (ofCompletion P hP hsheafA).hom =
      (ofCompletion P' hP' hsheafB).hom ≫
        presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ := by
  rw [ofCompletion_hom, ofCompletion_hom, pairComap,
    ← presentationLimitPreAdicSpacePairComap_comp, ← presentationLimitPreAdicSpacePairComap_comp,
    ofCompletionMap_comp_toCompletionHom]

/-- `ofCompletionMap` preserves `Pair.Hom.IsTopologicallyFiniteType`. -/
theorem isTopologicallyFiniteType_ofCompletionMap (φ : Pair.Hom S T)
    (hφ : φ.IsTopologicallyFiniteType) :
    (ofCompletionMap P hP hsheafA P' hP' hsheafB φ).IsTopologicallyFiniteType :=
  .of_comp ((ofCompletionMap_comp_toCompletionHom P hP hsheafA P' hP' hsheafB φ).symm ▸
    (isTopologicallyFiniteType_toCompletionHom P' hP' hsheafB).comp hφ)

end TauCeti.PreAdicSpace.CompleteAffinoidOpen
