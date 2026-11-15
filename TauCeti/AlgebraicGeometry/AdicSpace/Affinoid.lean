/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.WeaklyFiniteType
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.PairEquiv
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafForEveryPresentation
public import TauCeti.RingTheory.Huber.QuotientMapping
import TauCeti.RingTheory.Huber.LocalizationTopology.IdealQuotient
import TauCeti.Topology.Algebra.Ring.Ideal

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

## Main results

* `TauCeti.AdicSpace.isAnalytic_ofPair_iff` and `TauCeti.AdicSpace.IsAnalytic.ofPair`: analyticity
  criterion for `ofPair` and automatic analyticity over Tate rings.
* `TauCeti.AdicSpace.isHomeomorph_comapOfPair_quotientHom_base` and
  `TauCeti.AdicSpace.isHomeomorph_comapOfPair_base_of_isQuotientMapping`: quotient morphisms with
  nilpotent kernel induce homeomorphisms on underlying adic spectra.
* `TauCeti.AdicSpace.exists_ofPair_quotient_rational_square`: refines any neighbourhood on
  `ofPair S hS` to a rational open over which an ideal quotient pulls back to a quotient mapping
  between complete Hausdorff sheafy Huber pairs.

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

/-- **`AdicSpace.ofPair S hS` is analytic if and only if `spaAnalytic S.plus = spa S.plus`.** -/
theorem isAnalytic_ofPair_iff (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus) :
    (ofPair S hS).IsAnalytic ↔ spaAnalytic S.plus = spa S.plus := by
  unfold ofPair ofPresentation
  exact isAnalytic_spa_iff _ S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem _
    hS.exists_compatible_isSheaf.choose_spec.2

/-- **`AdicSpace.ofPair S hS` is analytic whenever `A` is a Tate ring.** -/
theorem IsAnalytic.ofPair {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsTateRing A] (S : Pair A) (hS : IsSheafyForEveryPresentation S.plus) :
    (ofPair S hS).IsAnalytic := by
  unfold AdicSpace.ofPair ofPresentation
  exact IsAnalytic.spa _ S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem _
    hS.exists_compatible_isSheaf.choose_spec.2

/-- **Quotienting a Huber pair by an ideal of nilpotent elements induces a homeomorphism on
underlying adic spectra.** -/
theorem isHomeomorph_comapOfPair_quotientHom_base (S : Pair A)
    (hS : IsSheafyForEveryPresentation S.plus) (J : Ideal A)
    (hSJ : IsSheafyForEveryPresentation (S.quotient J).plus)
    (hJ : ∀ a ∈ J, IsNilpotent a) :
    IsHomeomorph (comapOfPair hS hSJ (Pair.quotientHom S J)).hom.base := by
  have hsurj : Function.Surjective (Pair.quotientHom S J).spaComap := by
    rw [← Set.range_eq_univ, Pair.Hom.range_spaComap_quotientHom, Set.eq_univ_iff_forall]
    intro v
    refine fun a ha ↦ ?_
    obtain ⟨n, hn⟩ := hJ a ha
    exact (inferInstance : v.1.supp.IsPrime).mem_of_pow_mem n (hn ▸ v.1.supp.zero_mem)
  have hspa : IsHomeomorph (Pair.quotientHom S J).spaComap :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨(Pair.Hom.isClosedEmbedding_spaComap_quotientHom S J).isEmbedding, hsurj⟩
  have heq : ⇑(comapOfPair hS hSJ (Pair.quotientHom S J)).hom.base =
      ⇑(ofPairHomeomorph S hS).symm ∘ (Pair.quotientHom S J).spaComap ∘
        ⇑(ofPairHomeomorph (S.quotient J) hSJ) := by
    ext x
    apply (ofPairHomeomorph S hS).injective
    simp
  rw [heq]
  exact (ofPairHomeomorph S hS).symm.isHomeomorph.comp
    (hspa.comp (ofPairHomeomorph (S.quotient J) hSJ).isHomeomorph)

/-- A quotient mapping of sheafy Huber pairs with nilpotent kernel induces a homeomorphism on
underlying adic spectra. -/
theorem isHomeomorph_comapOfPair_base_of_isQuotientMapping {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    {q : Pair.Hom S T} (hq : q.IsQuotientMapping)
    (hker : ∀ a ∈ RingHom.ker q.toRingHom, IsNilpotent a) :
    IsHomeomorph (comapOfPair hS hT q).hom.base := by
  set K := RingHom.ker q.toRingHom
  let φ := Pair.Hom.quotientLift K q le_rfl
  let ψ := hq.quotientKerInverse
  have hψφ : ∀ x, ψ.toRingHom (φ.toRingHom x) = x := fun x ↦ by
    simpa only [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_id, RingHom.comp_apply,
      RingHom.id_apply] using
      RingHom.congr_fun (congrArg Pair.Hom.toRingHom hq.quotientKerInverse_comp_quotientLift) x
  have hφψ : ∀ x, φ.toRingHom (ψ.toRingHom x) = x := fun x ↦ by
    simpa only [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_id, RingHom.comp_apply,
      RingHom.id_apply] using
      RingHom.congr_fun (congrArg Pair.Hom.toRingHom hq.quotientLift_comp_quotientKerInverse) x
  let e : (A ⧸ K) ≃+* B :=
    { φ.toRingHom with
      invFun := ψ.toRingHom
      left_inv := hψφ
      right_inv := hφψ }
  have hplus : (S.quotient K).plus.map (e : A ⧸ K →+* B) = T.plus := by
    ext b
    exact ⟨by rintro ⟨x, hx, rfl⟩; exact φ.map_mem_plus x hx,
      fun hb ↦ ⟨ψ.toRingHom b, ψ.map_mem_plus b hb, hφψ b⟩⟩
  have hSK : IsSheafyForEveryPresentation (S.quotient K).plus :=
    (isSheafyForEveryPresentation_iff_of_ringEquiv e φ.continuous_toRingHom
      ψ.continuous_toRingHom hplus).mpr hT
  have hiso : IsIso (comapOfPair hSK hT φ) :=
    ⟨comapOfPair hT hSK ψ,
      by rw [← comapOfPair_comp, hq.quotientLift_comp_quotientKerInverse, comapOfPair_id],
      by rw [← comapOfPair_comp, hq.quotientKerInverse_comp_quotientLift, comapOfPair_id]⟩
  have hfac : comapOfPair hS hT q =
      comapOfPair hSK hT φ ≫ comapOfPair hS hSK (Pair.quotientHom S K) := by
    rw [← comapOfPair_comp, Pair.Hom.quotientLift_comp_quotientHom]
  have hφ_homeo : IsHomeomorph (comapOfPair hSK hT φ).hom.base :=
    (TopCat.homeoOfIso (forgetToTop.mapIso
      ((ObjectProperty.ι isAdic).mapIso (asIso (comapOfPair hSK hT φ))))).isHomeomorph
  have hbase : ⇑(comapOfPair hS hT q).hom.base =
      ⇑(comapOfPair hS hSK (Pair.quotientHom S K)).hom.base ∘ ⇑(comapOfPair hSK hT φ).hom.base := by
    rw [hfac]
    rfl
  rw [hbase]
  exact (isHomeomorph_comapOfPair_quotientHom_base S hS K hSK hker).comp hφ_homeo

/-- Rational localization preserves `IsSheafyForEveryPresentation`. -/
theorem isSheafyForEveryPresentation_rationalLocalizationPair (P : PairOfDefinition A)
    (S : Pair A) (hP : P.ringOfDefinition ≤ S.plus)
    (F : Finset A) (s : A) (L : Type u) [CommRing L] [Algebra A L] [IsLocalization.Away s L]
    (hden : P.HasDenominatorPower F s L) (hF : IsOpen (Ideal.span (F : Set A) : Set A))
    (hS : IsSheafyForEveryPresentation S.plus) :
    letI := P.locUniformSpace F s L hden
    haveI := P.isUniformAddGroup_locUniformSpace F s L hden
    haveI := P.isTopologicalRing_locUniformSpace F s L hden
    haveI := P.isHuberRing_completion_locTopology F s L hden
    IsSheafyForEveryPresentation (P.rationalLocalizationPair S hP F s L hden).plus := by
  let _ := P.locUniformSpace F s L hden
  have _ := P.isUniformAddGroup_locUniformSpace F s L hden
  have _ := P.isTopologicalRing_locUniformSpace F s L hden
  have _ := P.isHuberRing_completion_locTopology F s L hden
  let Sloc := P.rationalLocalizationPair S hP F s L hden
  let Ploc := P.completionLocalization F s L hden
  exact (isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf Ploc).mpr
    ⟨Sloc.isRingOfIntegralElements,
      isSheaf_presentationLimitPresheaf_rationalLocalizationPair P S hP F s L hden hF
        (hS.isSheaf P hP)⟩

/-- The rational-localization morphism `comapOfPair` attached to `P.toCompletionLocHom` is an open
immersion. -/
theorem isOpenImmersion_comapOfPair_toCompletionLocHom (P : PairOfDefinition A)
    (S : Pair A) (hP : P.ringOfDefinition ≤ S.plus)
    (F : Finset A) (s : A) (L : Type u) [CommRing L] [Algebra A L] [IsLocalization.Away s L]
    (hden : P.HasDenominatorPower F s L) (hF : IsOpen (Ideal.span (F : Set A) : Set A))
    (hS : IsSheafyForEveryPresentation S.plus) :
    letI := P.locUniformSpace F s L hden
    haveI := P.isUniformAddGroup_locUniformSpace F s L hden
    haveI := P.isTopologicalRing_locUniformSpace F s L hden
    haveI := P.isHuberRing_completion_locTopology F s L hden
    ∀ (hSloc : IsSheafyForEveryPresentation (P.rationalLocalizationPair S hP F s L hden).plus),
      PreAdicSpace.IsOpenImmersion
        (comapOfPair hS hSloc (P.toCompletionLocHom S hP F s L hden)).hom := by
  let _ := P.locUniformSpace F s L hden
  have _ := P.isUniformAddGroup_locUniformSpace F s L hden
  have _ := P.isTopologicalRing_locUniformSpace F s L hden
  have _ := P.isHuberRing_completion_locTopology F s L hden
  intro hSloc
  let Sloc := P.rationalLocalizationPair S hP F s L hden
  let Ploc := P.completionLocalization F s L hden
  have hPloc := P.completionLocalization_ringOfDefinition_le_rationalLocalizationPair S hP F s L
    hden
  have hpres : PreAdicSpace.IsOpenImmersion
      (comapOfPresentation S P hP (hS.isSheaf P hP) Sloc Ploc hPloc (hSloc.isSheaf Ploc hPloc)
        (P.toCompletionLocHom S hP F s L hden)).hom := by
    rw [comapOfPresentation_eq_homMk_presentationLimitPreAdicSpaceComap]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P hP F s L hden
      hF (hSloc.isSheaf Ploc hPloc)
  have hfac : comapOfPair hS hSloc (P.toCompletionLocHom S hP F s L hden) =
      (ofPairIsoOfPresentation Sloc hSloc Ploc hPloc).hom ≫
        comapOfPresentation S P hP (hS.isSheaf P hP) Sloc Ploc hPloc (hSloc.isSheaf Ploc hPloc)
          (P.toCompletionLocHom S hP F s L hden) ≫
        (ofPairIsoOfPresentation S hS P hP).inv := by
    rw [comapOfPresentation_ofPairIsoOfPresentation_inv, Iso.hom_inv_id_assoc]
  rw [hfac, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
  have : IsIso (ofPairIsoOfPresentation Sloc hSloc Ploc hPloc).hom.hom :=
    ((ObjectProperty.ι isAdic).mapIso (ofPairIsoOfPresentation Sloc hSloc Ploc hPloc)).isIso_hom
  have : IsIso (ofPairIsoOfPresentation S hS P hP).inv.hom :=
    ((ObjectProperty.ι isAdic).mapIso (ofPairIsoOfPresentation S hS P hP)).isIso_inv
  infer_instance

/-- The underlying image of `comapOfPair` along `P.toCompletionLocHom` is the preimage of the
rational subset `R(F/s)` under `ofPairHomeomorph`. -/
theorem range_comapOfPair_toCompletionLocHom_base (P : PairOfDefinition A)
    (S : Pair A) (hP : P.ringOfDefinition ≤ S.plus)
    (F : Finset A) (s : A) (L : Type u) [CommRing L] [Algebra A L] [IsLocalization.Away s L]
    (hden : P.HasDenominatorPower F s L)
    (hS : IsSheafyForEveryPresentation S.plus) :
    letI := P.locUniformSpace F s L hden
    haveI := P.isUniformAddGroup_locUniformSpace F s L hden
    haveI := P.isTopologicalRing_locUniformSpace F s L hden
    haveI := P.isHuberRing_completion_locTopology F s L hden
    ∀ (hSloc : IsSheafyForEveryPresentation (P.rationalLocalizationPair S hP F s L hden).plus),
      Set.range (comapOfPair hS hSloc (P.toCompletionLocHom S hP F s L hden)).hom.base =
        ofPairHomeomorph S hS ⁻¹' (spaBasicOpen S.plus F s : Set (spa S.plus)) := by
  let _ := P.locUniformSpace F s L hden
  have _ := P.isUniformAddGroup_locUniformSpace F s L hden
  have _ := P.isTopologicalRing_locUniformSpace F s L hden
  have _ := P.isHuberRing_completion_locTopology F s L hden
  intro hSloc
  let Ploc := P.completionLocalization F s L hden
  have hPloc := P.completionLocalization_ringOfDefinition_le_rationalLocalizationPair S hP F s L
    hden
  have hspa_range : Set.range (P.toCompletionLocHom S hP F s L hden).spaComap =
      (spaBasicOpen S.plus F s : Set (spa S.plus)) := by
    let φ := P.toCompletionLocHom S hP F s L hden
    rw [← range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base P hP F s L hden
      (hSloc.isSheaf Ploc hPloc), ← presentationLimitPreAdicSpacePairComap_def P Ploc hP hPloc
      (hSloc.isSheaf Ploc hPloc) φ]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, presentationLimitPreAdicSpacePairComap_base_apply P Ploc hP hPloc
        (hSloc.isSheaf Ploc hPloc) φ y ▸ rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, (presentationLimitPreAdicSpacePairComap_base_apply P Ploc hP hPloc
        (hSloc.isSheaf Ploc hPloc) φ y).symm⟩
  ext x
  rw [Set.mem_preimage, ← hspa_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨ofPairHomeomorph _ hSloc y, (ofPairHomeomorph_comapOfPair_apply ..).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨(ofPairHomeomorph _ hSloc).symm y, (ofPairHomeomorph S hS).injective ?_⟩
    simp [hy]

omit [IsHuberRing A] in
open scoped Classical in
private theorem isOpen_span_image_quotient_mk (J : Ideal A) (F : Finset A)
    (hF : IsOpen (Ideal.span (F : Set A) : Set A)) :
    IsOpen (Ideal.span ((F.image (Ideal.Quotient.mk J) : Finset (A ⧸ J)) : Set (A ⧸ J)) :
      Set (A ⧸ J)) := by
  rw [Finset.coe_image, ← Ideal.map_span,
    Ideal.map_eq_image_of_surjective _ Ideal.Quotient.mk_surjective]
  exact (QuotientRing.isOpenQuotientMap_mk J).isOpenMap _ hF

open scoped Classical in
private theorem preimage_comapOfPair_quotientHom_spaBasicOpen (S : Pair A)
    (hS : IsSheafyForEveryPresentation S.plus) (J : Ideal A)
    (hSJ : IsSheafyForEveryPresentation (S.quotient J).plus) (F : Finset A) (s : A) :
    (comapOfPair hS hSJ (Pair.quotientHom S J)).hom.base ⁻¹'
      (ofPairHomeomorph S hS ⁻¹' (spaBasicOpen S.plus F s : Set (spa S.plus))) =
      ofPairHomeomorph (S.quotient J) hSJ ⁻¹'
        (spaBasicOpen (S.quotient J).plus (F.image (Ideal.Quotient.mk J))
          (Ideal.Quotient.mk J s) : Set (spa (S.quotient J).plus)) := by
  ext x
  have hpre := Set.ext_iff.mp ((S.quotientHom J).spaComap_preimage_rationalSubset F s)
    (ofPairHomeomorph (S.quotient J) hSJ x)
  simp only [Pair.Hom.toRingHom_quotientHom] at hpre
  have hmem : x ∈ (comapOfPair hS hSJ (Pair.quotientHom S J)).hom.base ⁻¹'
      (ofPairHomeomorph S hS ⁻¹' (spaBasicOpen S.plus F s : Set (spa S.plus))) ↔
      (S.quotientHom J).spaComap (ofPairHomeomorph (S.quotient J) hSJ x) ∈
        (spaBasicOpen S.plus F s : Set (spa S.plus)) := by
    simp
  exact (Set.mem_preimage.trans
    (mem_spaBasicOpen.trans (hpre.symm.trans (mem_spaBasicOpen.symm.trans hmem.symm)))).symm

/-- Rational-localization pullback square for `Pair.quotientHom S J` over a given rational open
`spaBasicOpen S.plus F s`. -/
private theorem ofPair_quotient_rational_square_of_spaBasicOpen (P : PairOfDefinition A)
    (S : Pair A) (hP : P.ringOfDefinition ≤ S.plus) (hS : IsSheafyForEveryPresentation S.plus)
    (J : Ideal A) (hSJ : IsSheafyForEveryPresentation (S.quotient J).plus)
    (F : Finset A) (s : A) (hF : IsOpen (Ideal.span (F : Set A) : Set A)) :
    let O : Opens (ofPair S hS).obj :=
      ⟨ofPairHomeomorph S hS ⁻¹' (spaBasicOpen S.plus F s : Set (spa S.plus)),
        (spaBasicOpen S.plus F s).isOpen.preimage (ofPairHomeomorph S hS).continuous⟩
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : UniformSpace A₁) (_ : IsUniformAddGroup A₁)
      (_ : IsTopologicalRing A₁) (_ : CompleteSpace A₁) (_ : T2Space A₁) (_ : IsHuberRing A₁)
      (S₁ : Pair A₁) (hS₁ : IsSheafyForEveryPresentation S₁.plus)
      (A₂ : Type u) (_ : CommRing A₂) (_ : UniformSpace A₂) (_ : IsUniformAddGroup A₂)
      (_ : IsTopologicalRing A₂) (_ : CompleteSpace A₂) (_ : T2Space A₂) (_ : IsHuberRing A₂)
      (S₂ : Pair A₂) (hS₂ : IsSheafyForEveryPresentation S₂.plus)
      (π : Pair.Hom S₁ S₂) (_ : π.IsQuotientMapping)
      (_ : ∀ {n : ℕ}, J ^ n = ⊥ → RingHom.ker π.toRingHom ^ n = ⊥)
      (v : ofPair S₁ hS₁ ⟶ ofPair S hS)
      (u : ofPair S₂ hS₂ ⟶ ofPair (S.quotient J) hSJ),
      PreAdicSpace.IsOpenImmersion v.hom ∧
        Set.range v.hom.base = (O : Set (ofPair S hS).obj) ∧
        PreAdicSpace.IsOpenImmersion u.hom ∧
        Set.range u.hom.base =
          (comapOfPair hS hSJ (Pair.quotientHom S J)).hom.base ⁻¹' (O : Set (ofPair S hS).obj) ∧
        comapOfPair hS₁ hS₂ π ≫ v = u ≫ comapOfPair hS hSJ (Pair.quotientHom S J) := by
  classical
  intro O
  have hPq := P.quotient_ringOfDefinition_le_quotient_plus hP J
  let L := Localization.Away s
  let L' := Localization.Away (Ideal.Quotient.mk J s)
  let F' : Finset (A ⧸ J) := F.image (Ideal.Quotient.mk J)
  have hF' : (F' : Set (A ⧸ J)) = Ideal.Quotient.mk J '' F := Finset.coe_image
  have hden := P.hasDenominatorPower_of_isOpen_span F s L hF
  have hden' := P.hasDenominatorPower_quotient J F s L hF' L' hden
  let _ := P.locUniformSpace F s L hden
  have _ := P.isUniformAddGroup_locUniformSpace F s L hden
  have _ := P.isTopologicalRing_locUniformSpace F s L hden
  have _ := P.isHuberRing_completion_locTopology F s L hden
  let _ := (P.quotient J).locUniformSpace F' (Ideal.Quotient.mk J s) L' hden'
  have _ := (P.quotient J).isUniformAddGroup_locUniformSpace F' (Ideal.Quotient.mk J s) L' hden'
  have _ := (P.quotient J).isTopologicalRing_locUniformSpace F' (Ideal.Quotient.mk J s) L' hden'
  have _ := (P.quotient J).isHuberRing_completion_locTopology F' (Ideal.Quotient.mk J s) L' hden'
  have hFq := isOpen_span_image_quotient_mk J F hF
  have hS₁ := isSheafyForEveryPresentation_rationalLocalizationPair P S hP F s L hden hF hS
  have hS₂ := isSheafyForEveryPresentation_rationalLocalizationPair (P.quotient J) (S.quotient J)
    hPq F' (Ideal.Quotient.mk J s) L' hden' hFq hSJ
  let π := P.completionLocQuotientPairHom J F s L hF' L' S hP hden
  have hker_pow : ∀ {n : ℕ}, J ^ n = ⊥ → RingHom.ker π.toRingHom ^ n = ⊥ := fun {n} hJn ↦ by
    rw [PairOfDefinition.toRingHom_completionLocQuotientPairHom,
      P.ker_completionLocQuotientHom J F s L hF' L' hden]
    exact Ideal.closure_pow_eq_bot (by rw [← Ideal.map_pow, hJn, Ideal.map_bot])
  have hsq : comapOfPair hS₁ hS₂ π ≫ comapOfPair hS hS₁ (P.toCompletionLocHom S hP F s L hden) =
      comapOfPair hSJ hS₂ ((P.quotient J).toCompletionLocHom (S.quotient J) hPq F' _ L' hden') ≫
        comapOfPair hS hSJ (Pair.quotientHom S J) := by
    rw [← comapOfPair_comp, ← comapOfPair_comp]
    refine congrArg (comapOfPair hS hS₂) (Pair.Hom.ext ?_)
    rw [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_comp,
      PairOfDefinition.toRingHom_completionLocQuotientPairHom,
      PairOfDefinition.toRingHom_toCompletionLocHom,
      PairOfDefinition.toRingHom_toCompletionLocHom, Pair.Hom.toRingHom_quotientHom]
    exact P.completionLocQuotientHom_comp_toCompletionLoc J F s L hF' L' hden
  exact ⟨UniformSpace.Completion L, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, _, hS₁,
    UniformSpace.Completion L', inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, _, hS₂, π,
    P.isQuotientMapping_completionLocQuotientPairHom J F s L hF' L' S hP hden, hker_pow, _, _,
    isOpenImmersion_comapOfPair_toCompletionLocHom P S hP F s L hden hF hS hS₁,
    range_comapOfPair_toCompletionLocHom_base P S hP F s L hden hS hS₁,
    isOpenImmersion_comapOfPair_toCompletionLocHom (P.quotient J) (S.quotient J) hPq F' _ L'
      hden' hFq hSJ hS₂,
    (range_comapOfPair_toCompletionLocHom_base (P.quotient J) (S.quotient J) hPq F' _ L'
      hden' hSJ hS₂).trans (preimage_comapOfPair_quotientHom_spaBasicOpen S hS J hSJ F s).symm,
    hsq⟩

/-- **Rational-localization square for an ideal quotient of a sheafy Huber pair.** Around any point
`z` in an open `W` of `ofPair S hS`, there is a rational open `O ≤ W` containing `z` over which the
quotient morphism `ofPair (S.quotient J) hSJ ⟶ ofPair S hS` pulls back to a quotient mapping
`π : S₁ → S₂` between complete Hausdorff sheafy Huber pairs, with open immersions `v` and `u` onto
`O` and its preimage, preserving any nilpotency exponent of `J` on `ker π`. -/
theorem exists_ofPair_quotient_rational_square (S : Pair A)
    (hS : IsSheafyForEveryPresentation S.plus) (J : Ideal A)
    (hSJ : IsSheafyForEveryPresentation (S.quotient J).plus)
    (W : Opens (ofPair S hS).obj) {z : (ofPair S hS).obj} (hz : z ∈ W) :
    ∃ (O : Opens (ofPair S hS).obj) (_ : z ∈ O) (_ : O ≤ W)
      (A₁ : Type u) (_ : CommRing A₁) (_ : UniformSpace A₁) (_ : IsUniformAddGroup A₁)
      (_ : IsTopologicalRing A₁) (_ : CompleteSpace A₁) (_ : T2Space A₁) (_ : IsHuberRing A₁)
      (S₁ : Pair A₁) (hS₁ : IsSheafyForEveryPresentation S₁.plus)
      (A₂ : Type u) (_ : CommRing A₂) (_ : UniformSpace A₂) (_ : IsUniformAddGroup A₂)
      (_ : IsTopologicalRing A₂) (_ : CompleteSpace A₂) (_ : T2Space A₂) (_ : IsHuberRing A₂)
      (S₂ : Pair A₂) (hS₂ : IsSheafyForEveryPresentation S₂.plus)
      (π : Pair.Hom S₁ S₂) (_ : π.IsQuotientMapping)
      (_ : ∀ {n : ℕ}, J ^ n = ⊥ → RingHom.ker π.toRingHom ^ n = ⊥)
      (v : ofPair S₁ hS₁ ⟶ ofPair S hS)
      (u : ofPair S₂ hS₂ ⟶ ofPair (S.quotient J) hSJ),
      PreAdicSpace.IsOpenImmersion v.hom ∧
        Set.range v.hom.base = (O : Set (ofPair S hS).obj) ∧
        PreAdicSpace.IsOpenImmersion u.hom ∧
        Set.range u.hom.base =
          (comapOfPair hS hSJ (Pair.quotientHom S J)).hom.base ⁻¹' (O : Set (ofPair S hS).obj) ∧
        comapOfPair hS₁ hS₂ π ≫ v = u ≫ comapOfPair hS hSJ (Pair.quotientHom S J) := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  let W_spa : Opens (spa S.plus) :=
    ⟨(ofPairHomeomorph S hS).symm ⁻¹' (W : Set (ofPair S hS).obj),
      W.isOpen.preimage (ofPairHomeomorph S hS).symm.continuous⟩
  have hz_spa : ofPairHomeomorph S hS z ∈ W_spa := Set.mem_preimage.mpr (by simpa using hz)
  obtain ⟨R₀, hR₀, hzR₀, hR₀W⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens S.plus) hz_spa
  obtain ⟨F, s, hF, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hR₀
  have hOW : (⟨ofPairHomeomorph S hS ⁻¹' (spaBasicOpen S.plus F s : Set (spa S.plus)),
      (spaBasicOpen S.plus F s).isOpen.preimage (ofPairHomeomorph S hS).continuous⟩ :
      Opens (ofPair S hS).obj) ≤ W := fun y hy ↦ by
    have hy' : (ofPairHomeomorph S hS).symm (ofPairHomeomorph S hS y) ∈ (W : Set _) := hR₀W hy
    rwa [(ofPairHomeomorph S hS).symm_apply_apply] at hy'
  exact ⟨_, hzR₀, hOW, ofPair_quotient_rational_square_of_spaBasicOpen P S hP hS J hSJ F s hF⟩

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
