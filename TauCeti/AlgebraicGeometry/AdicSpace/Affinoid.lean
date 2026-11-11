/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.WeaklyFiniteType
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.PairEquiv
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafForEveryPresentation

/-!
# Affinoid adic spaces and their morphisms

This file packages the adic spectrum of a sheafy Huber pair as an object of Wedhorn's category
`TauCeti.AdicSpace` (`(Adic)`), both for an explicit compatible pair of definition
(`TauCeti.AdicSpace.ofPresentation`, mirroring `TauCeti.AffinoidPreAdicSpace.ofPresentation`) and
canonically from `TauCeti.Huber.IsSheafyForEveryPresentation` without choosing a pair of definition
(`TauCeti.AdicSpace.ofPair`).

Any two compatible pairs of definition give canonically isomorphic objects of `AdicSpace`
(`TauCeti.AdicSpace.ofPresentationPairChangeIso`, `TauCeti.AdicSpace.ofPairIsoOfPresentation`),
naturally in morphisms of Huber pairs. When the coefficient rings are complete and Hausdorff,
Huber's global-sections correspondence identifies morphisms `Spa(B, B⁺) ⟶ Spa(A, A⁺)` in
`AdicSpace` bijectively with morphisms of Huber pairs `(A, A⁺) → (B, B⁺)`
(`TauCeti.AdicSpace.ofPresentationHomEquiv`, `TauCeti.AdicSpace.ofPairHomEquiv`).

## Main definitions

* `TauCeti.AdicSpace.ofPresentation`, `TauCeti.AdicSpace.comapOfPresentation`: the affinoid adic
  space and induced morphism attached to explicit compatible pairs of definition.
* `TauCeti.AdicSpace.ofPair`, `TauCeti.AdicSpace.comapOfPair`: the canonical affinoid adic space
  and induced morphism attached to sheafy Huber pairs (`IsSheafyForEveryPresentation`).
* `TauCeti.AdicSpace.ofPairIsoOfPresentation`: the canonical isomorphism comparing `ofPair` with
  `ofPresentation` for any compatible pair of definition.
* `TauCeti.AdicSpace.ofPairHomeomorph`: the canonical homeomorphism
  `(ofPair S hS).obj ≃ₜ spa S.plus` on underlying topological spaces.
* `TauCeti.AdicSpace.ofPresentationHomEquiv`, `TauCeti.AdicSpace.ofPairHomEquiv`: Huber's
  bijection `(Spa(B, B⁺) ⟶ Spa(A, A⁺)) ≃ Pair.Hom S T` for complete Hausdorff Huber pairs.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, Proposition 2.1(i).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1–§8.2, Theorem 8.12 and
  Definition 8.22.
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti.AdicSpace

open Huber PreAdicSpace ValuationSpectrum

universe u

section OfPresentation

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]

/-- The affinoid adic space `Spa(A, A⁺)` attached to a Huber pair `S`, a compatible pair of
definition `P`, and a proof that its presentation-limit structure presheaf is a sheaf.

This is reducible so that `(ofPresentation S P hP hsheaf).obj` reduces to
`presentationLimitPreAdicSpace` when typing morphisms in the full subcategory `AdicSpace`. -/
noncomputable abbrev ofPresentation (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus)) : AdicSpace.{u} :=
  ⟨presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP,
    isAdic_presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP hsheaf⟩

/-- The underlying pre-adic space of `AdicSpace.ofPresentation` is
`presentationLimitPreAdicSpace`. -/
theorem ofPresentation_obj (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus)) :
    (ofPresentation S P hP hsheaf).obj =
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP :=
  (rfl)

/-- Every `AdicSpace.ofPresentation` is an affinoid pre-adic space. -/
theorem isAffinoid_ofPresentation (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus)) :
    isAffinoid (ofPresentation S P hP hsheaf).obj :=
  isAffinoid_presentationLimitPreAdicSpace S P hP

/-- The morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` in `AdicSpace` induced contravariantly by a morphism of
Huber pairs `φ : (A, A⁺) → (B, B⁺)` for explicit compatible pairs of definition. -/
noncomputable def comapOfPresentation (S : Pair A) (P : PairOfDefinition A)
    (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) :
    ofPresentation T P' hT hsheafT ⟶ ofPresentation S P hS hsheafS :=
  ObjectProperty.homMk (presentationLimitPreAdicSpacePairComap P P' hS hT hsheafT φ)

@[simp]
theorem comapOfPresentation_hom (S : Pair A) (P : PairOfDefinition A)
    (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) :
    (comapOfPresentation S P hS hsheafS T P' hT hsheafT φ).hom =
      presentationLimitPreAdicSpacePairComap P P' hS hT hsheafT φ :=
  (rfl)

/-- On points, `comapOfPresentation` acts by `Pair.Hom.spaComap`. -/
theorem comapOfPresentation_base_apply (S : Pair A) (P : PairOfDefinition A)
    (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) (x : (ofPresentation T P' hT hsheafT).obj) :
    ((comapOfPresentation S P hS hsheafS T P' hT hsheafT φ).hom.base x : spa S.plus) =
      φ.spaComap x :=
  presentationLimitPreAdicSpacePairComap_base_apply P P' hS hT hsheafT φ x

@[simp]
theorem comapOfPresentation_id (S : Pair A) (P : PairOfDefinition A)
    (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus)) :
    comapOfPresentation S P hS hsheafS S P hS hsheafS (Pair.Hom.id S) =
      𝟙 (ofPresentation S P hS hsheafS) := by
  ext1
  exact presentationLimitPreAdicSpacePairComap_id P hS hsheafS

/-- Contravariant functoriality of `comapOfPresentation`. -/
@[reassoc]
theorem comapOfPresentation_comp (S : Pair A) (P : PairOfDefinition A)
    (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (U : Pair C) (P'' : PairOfDefinition C) (hU : P''.ringOfDefinition ≤ U.plus)
    (hsheafU : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U.plus))
      (presentationLimitPresheaf P'' U.plus))
    (φ : Pair.Hom S T) (ψ : Pair.Hom T U) :
    comapOfPresentation S P hS hsheafS U P'' hU hsheafU (ψ.comp φ) =
      comapOfPresentation T P' hT hsheafT U P'' hU hsheafU ψ ≫
        comapOfPresentation S P hS hsheafS T P' hT hsheafT φ := by
  ext1
  exact presentationLimitPreAdicSpacePairComap_comp P P' P'' hS hT hU hsheafT hsheafU φ ψ

/-- Canonical isomorphism in `AdicSpace` between the affinoid objects constructed from any two
compatible pairs of definition of `(A, A⁺)`. -/
noncomputable def ofPresentationPairChangeIso (S : Pair A) (P P' : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (hsheaf' : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P' S.plus)) :
    ofPresentation S P hP hsheaf ≅ ofPresentation S P' hP' hsheaf' :=
  ObjectProperty.isoMk _ (presentationLimitPreAdicSpacePairChangeIso P P' hP hP' hsheaf hsheaf')

@[simp]
theorem ofPresentationPairChangeIso_hom (S : Pair A) (P P' : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (hsheaf' : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P' S.plus)) :
    (ofPresentationPairChangeIso S P P' hP hP' hsheaf hsheaf').hom =
      comapOfPresentation S P' hP' hsheaf' S P hP hsheaf (Pair.Hom.id S) := by
  ext1
  exact presentationLimitPreAdicSpacePairChangeIso_hom P P' hP hP' hsheaf hsheaf'

@[simp]
theorem ofPresentationPairChangeIso_inv (S : Pair A) (P P' : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (hsheaf' : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P' S.plus)) :
    (ofPresentationPairChangeIso S P P' hP hP' hsheaf hsheaf').inv =
      comapOfPresentation S P hP hsheaf S P' hP' hsheaf' (Pair.Hom.id S) := by
  ext1
  exact presentationLimitPreAdicSpacePairChangeIso_inv P P' hP hP' hsheaf hsheaf'

/-- `comapOfPresentation` unfolds to `ObjectProperty.homMk` applied to
`presentationLimitPreAdicSpaceComap`. -/
theorem comapOfPresentation_eq_homMk_presentationLimitPreAdicSpaceComap
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) :
    comapOfPresentation S P hS hsheafS T P' hT hsheafT φ =
      ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hS hT hsheafT) := by
  ext1
  exact presentationLimitPreAdicSpacePairComap_def P P' hS hT hsheafT φ

/-- For complete Hausdorff `B`, `comapOfPresentation` is adic if and only if the underlying ring
homomorphism is adic. -/
theorem isAdic_comapOfPresentation_iff {B : Type u} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T0Space B] [IsHuberRing B]
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) :
    IsAdic (comapOfPresentation S P hS hsheafS T P' hT hsheafT φ) ↔ IsAdicHom φ.toRingHom := by
  rw [comapOfPresentation_eq_homMk_presentationLimitPreAdicSpaceComap]
  exact IsAdic.iff_isAdicHom P P' hS hT hsheafT (ofPresentation S P hS hsheafS).property φ

/-- For complete Hausdorff `B`, `comapOfPresentation` is locally of weakly finite type whenever the
underlying ring homomorphism is topologically of finite type. -/
theorem locallyOfWeaklyFiniteType_comapOfPresentation {B : Type u} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T0Space B] [IsHuberRing B]
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) (hφ : IsTopologicallyFiniteType φ.toRingHom) :
    LocallyOfWeaklyFiniteType (comapOfPresentation S P hS hsheafS T P' hT hsheafT φ) := by
  rw [comapOfPresentation_eq_homMk_presentationLimitPreAdicSpaceComap]
  exact locallyOfWeaklyFiniteType_presentationLimitPreAdicSpaceComap P P' hS hT hsheafT
    (ofPresentation S P hS hsheafS).property φ hφ

end OfPresentation

section OfPresentationComplete

variable {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsHuberRing A]
  {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [CompleteSpace B] [T0Space B] [IsHuberRing B]

/-- **Huber's bijection in `AdicSpace` for explicit presentations**: morphisms
`Spa(B, B⁺) ⟶ Spa(A, A⁺)` in `AdicSpace` between complete Hausdorff affinoid adic spaces correspond
bijectively to morphisms of Huber pairs `(A, A⁺) → (B, B⁺)`. -/
noncomputable def ofPresentationHomEquiv (S : Pair A) (P : PairOfDefinition A)
    (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus)) :
    (ofPresentation T P' hT hsheafT ⟶ ofPresentation S P hS hsheafS) ≃ Pair.Hom S T :=
  (ObjectProperty.fullyFaithfulι isAdic).homEquiv.trans
    (presentationLimitPreAdicSpaceHomEquiv P P' S T hS hT hsheafT)

@[simp]
theorem ofPresentationHomEquiv_apply (S : Pair A) (P : PairOfDefinition A)
    (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (f : ofPresentation T P' hT hsheafT ⟶ ofPresentation S P hS hsheafS) :
    ofPresentationHomEquiv S P hS hsheafS T P' hT hsheafT f =
      presentationLimitHomPairHom P P' S T hS hT f.hom := by
  rw [ofPresentationHomEquiv, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply,
    ObjectProperty.ι_map, presentationLimitPreAdicSpaceHomEquiv_apply]

@[simp]
theorem ofPresentationHomEquiv_symm_apply (S : Pair A) (P : PairOfDefinition A)
    (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) :
    (ofPresentationHomEquiv S P hS hsheafS T P' hT hsheafT).symm φ =
      comapOfPresentation S P hS hsheafS T P' hT hsheafT φ := by
  apply (ofPresentationHomEquiv S P hS hsheafS T P' hT hsheafT).injective
  rw [Equiv.apply_symm_apply, ofPresentationHomEquiv_apply, comapOfPresentation_hom,
    presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P P' S T hS hT hsheafT]

end OfPresentationComplete

section OfPair

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]

/-- The canonical affinoid adic space `Spa(A, A⁺)` attached to a Huber pair `S` whose plus ring
satisfies `IsSheafyForEveryPresentation`. Up to canonical isomorphism
(`ofPairIsoOfPresentation`), it is independent of any choice of compatible pair of definition. -/
noncomputable def ofPair (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus) :
    AdicSpace.{u} :=
  ofPresentation S hS.exists_compatible_isSheaf.choose
    hS.exists_compatible_isSheaf.choose_spec.1 hS.exists_compatible_isSheaf.choose_spec.2

/-- Every `AdicSpace.ofPair` is an affinoid pre-adic space. -/
theorem isAffinoid_ofPair (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus) :
    isAffinoid (ofPair S hS).obj :=
  isAffinoid_presentationLimitPreAdicSpace S _ _

/-- The underlying topological carrier of `ofPair S hS` is `TopCat.of ↥(spa S.plus)`. -/
theorem ofPair_carrier (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus) :
    ((ofPair S hS).obj.toPresheafedSpace : TopCat) = TopCat.of ↥(spa S.plus) :=
  presentationLimitPreAdicSpace_carrier _ _ _ _

/-- Canonical homeomorphism between the underlying space of `AdicSpace.ofPair S hS` and
`ValuationSpectrum.spa S.plus`. -/
noncomputable def ofPairHomeomorph (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus) :
    (ofPair S hS).obj ≃ₜ spa S.plus :=
  TopCat.homeoOfIso (eqToIso (ofPair_carrier S hS))

/-- The morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` in `AdicSpace` induced contravariantly by a morphism of
sheafy Huber pairs `φ : (A, A⁺) → (B, B⁺)`. -/
noncomputable def comapOfPair {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) :
    ofPair T hT ⟶ ofPair S hS :=
  comapOfPresentation S hS.exists_compatible_isSheaf.choose
    hS.exists_compatible_isSheaf.choose_spec.1 hS.exists_compatible_isSheaf.choose_spec.2
    T hT.exists_compatible_isSheaf.choose
    hT.exists_compatible_isSheaf.choose_spec.1 hT.exists_compatible_isSheaf.choose_spec.2 φ

@[simp]
theorem comapOfPair_id (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus) :
    comapOfPair hS hS (Pair.Hom.id S) = 𝟙 (ofPair S hS) :=
  comapOfPresentation_id _ _ _ _

/-- Contravariant functoriality of `comapOfPair` with respect to `Pair.Hom.comp`. -/
@[reassoc]
theorem comapOfPair_comp {S : Pair A} {T : Pair B} {U : Pair C}
    (hS : IsSheafyForEveryPresentation S.plus)
    (hT : IsSheafyForEveryPresentation T.plus)
    (hU : IsSheafyForEveryPresentation U.plus)
    (φ : Pair.Hom S T) (ψ : Pair.Hom T U) :
    comapOfPair hS hU (ψ.comp φ) = comapOfPair hT hU ψ ≫ comapOfPair hS hT φ :=
  comapOfPresentation_comp _ _ _ _ _ _ _ _ _ _ _ _ φ ψ

/-- On points, `comapOfPair` acts as `Pair.Hom.spaComap` under `ofPairHomeomorph`. -/
@[simp]
theorem ofPairHomeomorph_comapOfPair_apply {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (x : (ofPair T hT).obj) :
    ofPairHomeomorph S hS ((comapOfPair hS hT φ).hom.base x) =
      φ.spaComap (ofPairHomeomorph T hT x) := by
  -- `ofPair` is sealed in the public interface because it chooses a pair of definition; once
  -- unfolded, its carrier is definitionally `TopCat.of ↥(spa _.plus)` via the exposed
  -- `presentationLimitPreAdicSpace`, so `eqToIso (ofPair_carrier _ _)` is `eqToIso rfl` and
  -- `TopCat.homeoOfIso` acts as the identity on points.
  dsimp only [ofPair, ofPairHomeomorph, comapOfPair, TopCat.homeoOfIso_apply, eqToIso.hom,
    eqToHom_refl]
  exact comapOfPresentation_base_apply _ _ _ _ _ _ _ _ φ x

/-- Under `ofPairHomeomorph.symm`, the base map of `comapOfPair` transports `Pair.Hom.spaComap`. -/
@[simp]
theorem comapOfPair_base_ofPairHomeomorph_symm {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (x : spa T.plus) :
    (comapOfPair hS hT φ).hom.base ((ofPairHomeomorph T hT).symm x) =
      (ofPairHomeomorph S hS).symm (φ.spaComap x) := by
  apply (ofPairHomeomorph S hS).injective
  simp

/-- Canonical isomorphism comparing `ofPair S hS` with `ofPresentation S P hP (hS.isSheaf P hP)`
for any compatible pair of definition `P`. -/
noncomputable def ofPairIsoOfPresentation (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) :
    ofPair S hS ≅ ofPresentation S P hP (hS.isSheaf P hP) :=
  ofPresentationPairChangeIso S hS.exists_compatible_isSheaf.choose P
    hS.exists_compatible_isSheaf.choose_spec.1 hP
    hS.exists_compatible_isSheaf.choose_spec.2 (hS.isSheaf P hP)

/-- Naturality of `ofPairIsoOfPresentation` relating `comapOfPair` and `comapOfPresentation`. -/
@[reassoc (attr := simp)]
theorem ofPairIsoOfPresentation_hom_comapOfPresentation {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (φ : Pair.Hom S T) :
    (ofPairIsoOfPresentation T hT P' hP').hom ≫
        comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP') φ =
      comapOfPair hS hT φ ≫ (ofPairIsoOfPresentation S hS P hP).hom := by
  unfold ofPair comapOfPair ofPairIsoOfPresentation
  rw [ofPresentationPairChangeIso_hom, ofPresentationPairChangeIso_hom,
    ← comapOfPresentation_comp, ← comapOfPresentation_comp, Pair.Hom.comp_id, Pair.Hom.id_comp]

/-- Naturality of `(ofPairIsoOfPresentation _ _ _ _).inv` relating `comapOfPresentation` and
`comapOfPair`. -/
@[reassoc (attr := simp)]
theorem comapOfPresentation_ofPairIsoOfPresentation_inv {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (φ : Pair.Hom S T) :
    comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP') φ ≫
        (ofPairIsoOfPresentation S hS P hP).inv =
      (ofPairIsoOfPresentation T hT P' hP').inv ≫ comapOfPair hS hT φ := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact ofPairIsoOfPresentation_hom_comapOfPresentation hS hT P hP P' hP' φ

/-- For complete Hausdorff `B`, `comapOfPair` is adic if and only if the underlying ring
homomorphism is adic. -/
theorem isAdic_comapOfPair_iff {B : Type u} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T0Space B] [IsHuberRing B]
    {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) :
    IsAdic (comapOfPair hS hT φ) ↔ IsAdicHom φ.toRingHom :=
  isAdic_comapOfPresentation_iff S _ _ hS.exists_compatible_isSheaf.choose_spec.2
    T _ _ hT.exists_compatible_isSheaf.choose_spec.2 φ

/-- For complete Hausdorff `B`, `comapOfPair` is locally of weakly finite type whenever the
underlying ring homomorphism is topologically of finite type. -/
theorem locallyOfWeaklyFiniteType_comapOfPair {B : Type u} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T0Space B] [IsHuberRing B]
    {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : IsTopologicallyFiniteType φ.toRingHom) :
    LocallyOfWeaklyFiniteType (comapOfPair hS hT φ) :=
  locallyOfWeaklyFiniteType_comapOfPresentation S _ _ hS.exists_compatible_isSheaf.choose_spec.2
    T _ _ hT.exists_compatible_isSheaf.choose_spec.2 φ hφ

end OfPair

section OfPairComplete

variable {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsHuberRing A]
  {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [CompleteSpace B] [T0Space B] [IsHuberRing B]
  {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
  [IsTopologicalRing C] [CompleteSpace C] [T0Space C] [IsHuberRing C]

/-- **Huber's bijection in `AdicSpace`**: morphisms `Spa(B, B⁺) ⟶ Spa(A, A⁺)` in `AdicSpace`
between complete Hausdorff sheafy Huber pairs correspond bijectively to morphisms of Huber pairs
`(A, A⁺) → (B, B⁺)`. -/
noncomputable def ofPairHomEquiv {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus) :
    (ofPair T hT ⟶ ofPair S hS) ≃ Pair.Hom S T :=
  ofPresentationHomEquiv S hS.exists_compatible_isSheaf.choose
    hS.exists_compatible_isSheaf.choose_spec.1 hS.exists_compatible_isSheaf.choose_spec.2
    T hT.exists_compatible_isSheaf.choose
    hT.exists_compatible_isSheaf.choose_spec.1 hT.exists_compatible_isSheaf.choose_spec.2

@[simp]
theorem ofPairHomEquiv_symm_apply {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) :
    (ofPairHomEquiv hS hT).symm φ = comapOfPair hS hT φ :=
  ofPresentationHomEquiv_symm_apply _ _ _ _ _ _ _ _ φ

@[simp]
theorem ofPairHomEquiv_comapOfPair {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) :
    ofPairHomEquiv hS hT (comapOfPair hS hT φ) = φ := by
  rw [← ofPairHomEquiv_symm_apply hS hT φ, Equiv.apply_symm_apply]

@[simp]
theorem comapOfPair_ofPairHomEquiv {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (f : ofPair T hT ⟶ ofPair S hS) :
    comapOfPair hS hT (ofPairHomEquiv hS hT f) = f := by
  rw [← ofPairHomEquiv_symm_apply hS hT, Equiv.symm_apply_apply]

@[simp]
theorem ofPairHomEquiv_id (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus) :
    ofPairHomEquiv hS hS (𝟙 (ofPair S hS)) = Pair.Hom.id S := by
  rw [← comapOfPair_id S hS, ofPairHomEquiv_comapOfPair]

@[simp]
theorem ofPairHomEquiv_comp {S : Pair A} {T : Pair B} {U : Pair C}
    (hS : IsSheafyForEveryPresentation S.plus)
    (hT : IsSheafyForEveryPresentation T.plus)
    (hU : IsSheafyForEveryPresentation U.plus)
    (f : ofPair U hU ⟶ ofPair T hT) (g : ofPair T hT ⟶ ofPair S hS) :
    ofPairHomEquiv hS hU (f ≫ g) =
      (ofPairHomEquiv hT hU f).comp (ofPairHomEquiv hS hT g) := by
  refine (ofPairHomEquiv hS hU).symm.injective ?_
  rw [Equiv.symm_apply_apply, ofPairHomEquiv_symm_apply, comapOfPair_comp hS hT hU,
    comapOfPair_ofPairHomEquiv, comapOfPair_ofPairHomEquiv]

end OfPairComplete

end TauCeti.AdicSpace
