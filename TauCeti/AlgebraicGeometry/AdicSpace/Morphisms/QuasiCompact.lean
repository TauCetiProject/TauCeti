/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.OpenImmersion
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.MorphismSpectral

/-!
# Quasi-compact morphisms of adic spaces

A morphism `f : X ⟶ Y` of adic spaces is *quasi-compact* if the preimage of every quasi-compact
open subset of `Y` is quasi-compact (Huber 1996, Definition 1.2.1(iv)). Quasi-compact morphisms
are the morphisms whose underlying continuous map is spectral in Mathlib's sense
(`IsSpectralMap`), as for morphisms of schemes (`AlgebraicGeometry.quasiCompact_iff_isSpectralMap`).

Since the open affinoid subspaces of an adic space are quasi-compact and form a basis of its
topology, quasi-compactness may be tested on them: `f` is quasi-compact exactly when the preimage
of every open affinoid subspace of `Y` is quasi-compact. In particular, the morphism
`Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a morphism of Huber pairs is quasi-compact as soon as the
image of every open ideal of `A` generates an open ideal of `B`, for instance when `A → B` is adic,
since rational subsets then pull back to rational subsets.

Quasi-compactness is a property of the map and not of the spaces: the identity of every adic
space, quasi-compact or not, is quasi-compact, and so is every morphism out of the empty adic
space, whereas no morphism from an adic space that is not quasi-compact to a
quasi-compact one is quasi-compact. Quasi-compactness is one of the conditions defining proper
morphisms of adic spaces (Huber 1996, Definition 1.3.2), and together with being locally of weakly
finite type it defines morphisms of weakly finite type
(`TauCeti.AdicSpace.IsWeaklyFiniteType`).

## Main definitions

* `TauCeti.AdicSpace.QuasiCompact`: quasi-compact morphisms of adic spaces.

## Main results

* `TauCeti.AdicSpace.quasiCompact_iff_isSpectralMap`: a morphism of adic spaces is quasi-compact
  exactly when its underlying continuous map is spectral.
* `TauCeti.AdicSpace.quasiCompact_iff_forall_mem_affinoidOpens`: quasi-compactness may be tested
  on the open affinoid subspaces of the target.
* `TauCeti.AdicSpace.QuasiCompact.isMultiplicative`, `TauCeti.AdicSpace.QuasiCompact.respectsIso`:
  identities and isomorphisms are quasi-compact, and composites of quasi-compact morphisms are
  quasi-compact.
* `TauCeti.AdicSpace.QuasiCompact.compactSpace`: the source of a quasi-compact morphism into a
  quasi-compact adic space is quasi-compact.
* `TauCeti.AdicSpace.QuasiCompact.of_isOpenImmersion`: an open immersion with quasi-compact
  source into a quasi-separated adic space is quasi-compact.
* `TauCeti.AdicSpace.quasiCompact_presentationLimitPreAdicSpaceComap`: the morphism of affinoid
  adic spaces induced by a morphism of Huber pairs carrying open ideals to ideals generating open
  ideals is quasi-compact.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, Definition 1.2.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Theorem 7.35.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber

universe u

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

/-! ### Quasi-compact morphisms -/

/-- **Quasi-compact morphisms** (Huber 1996, Definition 1.2.1(iv)): a morphism `f : X ⟶ Y` of
adic spaces is *quasi-compact* when the preimage under `f` of every quasi-compact open subset of
`Y` is quasi-compact. By `quasiCompact_iff_isSpectralMap` these are the morphisms whose underlying
continuous map is spectral. -/
def QuasiCompact : MorphismProperty AdicSpace.{u} := fun _ Y f ↦
  ∀ U : Opens Y.obj, IsCompact (U : Set Y.obj) → IsCompact (f.hom.base ⁻¹' U)

variable {X Y Z : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.QuasiCompact`. -/
theorem quasiCompact_iff (f : X ⟶ Y) :
    QuasiCompact f ↔ ∀ U : Opens Y.obj, IsCompact (U : Set Y.obj) →
      IsCompact (f.hom.base ⁻¹' U) :=
  Iff.rfl

/-- The preimage of a quasi-compact open subset under a quasi-compact morphism is
quasi-compact. -/
theorem QuasiCompact.isCompact_preimage {f : X ⟶ Y} (hf : QuasiCompact f) {U : Opens Y.obj}
    (hU : IsCompact (U : Set Y.obj)) : IsCompact (f.hom.base ⁻¹' U) :=
  hf U hU

/-- **A morphism of adic spaces is quasi-compact exactly when its underlying continuous map is
spectral.** -/
theorem quasiCompact_iff_isSpectralMap (f : X ⟶ Y) :
    QuasiCompact f ↔ IsSpectralMap f.hom.base :=
  ⟨fun hf ↦ ⟨f.hom.base.hom.continuous, fun U hUo hUc ↦ hf ⟨U, hUo⟩ hUc⟩,
    fun hf U hU ↦ hf.isCompact_preimage_of_isOpen U.isOpen hU⟩

/-- **Quasi-compactness may be tested on open affinoid subspaces**: a morphism of adic spaces is
quasi-compact exactly when the preimage of every open affinoid subspace of the target is
quasi-compact. The open affinoid subspaces are quasi-compact and form a basis of the topology, so
every quasi-compact open subset is a finite union of them. -/
theorem quasiCompact_iff_forall_mem_affinoidOpens (f : X ⟶ Y) :
    QuasiCompact f ↔ ∀ V ∈ Y.obj.affinoidOpens, IsCompact (f.hom.base ⁻¹' V) :=
  ⟨fun hf _ hV ↦ hf.isCompact_preimage (isCompact_of_mem_affinoidOpens hV),
    fun h ↦ (quasiCompact_iff_isSpectralMap f).mpr <| isSpectralMap_of_isTopologicalBasis
      (isBasis_affinoidOpens Y.property.isLocallyAffinoid) f.hom.base.hom.continuous <| by
        rintro _ ⟨V, hV, rfl⟩
        exact h V hV⟩

/-- **Identities are quasi-compact and composites of quasi-compact morphisms are
quasi-compact.** -/
instance QuasiCompact.isMultiplicative : QuasiCompact.{u}.IsMultiplicative where
  id_mem X := (quasiCompact_iff_isSpectralMap (𝟙 X)).mpr isSpectralMap_id
  comp_mem f g hf hg := (quasiCompact_iff_isSpectralMap (f ≫ g)).mpr <|
    ((quasiCompact_iff_isSpectralMap g).mp hg).comp ((quasiCompact_iff_isSpectralMap f).mp hf)

/-- **Isomorphisms are quasi-compact**: the underlying continuous map of an isomorphism is a
homeomorphism. -/
theorem QuasiCompact.of_isIso (f : X ⟶ Y) [IsIso f] : QuasiCompact f := by
  have : IsIso f.hom := (ObjectProperty.ι _).map_isIso f
  exact (quasiCompact_iff_isSpectralMap f).mpr
    (TopCat.homeoOfIso (forgetToTop.mapIso (asIso f.hom))).isProperMap.isSpectralMap

/-- **Being quasi-compact is invariant under isomorphisms** of the source and of the target. -/
instance QuasiCompact.respectsIso : QuasiCompact.{u}.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦
    QuasiCompact.of_isIso f

/-- Every morphism out of an empty adic space is quasi-compact. -/
theorem QuasiCompact.of_isEmpty (f : X ⟶ Y) [IsEmpty X.obj] : QuasiCompact f := fun U _ ↦ by
  rw [Set.eq_empty_of_isEmpty (f.hom.base ⁻¹' U)]
  exact isCompact_empty

/-- **The source of a quasi-compact morphism into a quasi-compact adic space is quasi-compact.**
So no morphism from an adic space that is not quasi-compact, such as the open unit disc, to a
quasi-compact one, such as an affinoid adic space, is quasi-compact. -/
theorem QuasiCompact.compactSpace {f : X ⟶ Y} (hf : QuasiCompact f) [CompactSpace Y.obj] :
    CompactSpace X.obj :=
  isCompact_univ_iff.mp (hf.isCompact_preimage (U := ⊤) isCompact_univ)

/-- **An open immersion with quasi-compact source into a quasi-separated adic space is
quasi-compact**, for instance the inclusion of a quasi-compact open subspace of an affinoid adic
space. -/
theorem QuasiCompact.of_isOpenImmersion (f : X ⟶ Y) [PreAdicSpace.IsOpenImmersion f.hom]
    [CompactSpace X.obj] [QuasiSeparatedSpace Y.obj] : QuasiCompact f :=
  (quasiCompact_iff_isSpectralMap f).mpr f.hom.isOpenEmbedding.isSpectralMap

/-- **Affinoid morphisms**: for a morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)` between pairs
whose adic spectra are adic spaces, the morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by `φ` is
quasi-compact as soon as the image of every open ideal of `A` generates an open ideal of `B`, for
instance when `φ` is adic (`Huber.IsAdicHom.isOpen_map`) or `A` is a Tate ring. Rational subsets
then pull back to rational subsets, which are quasi-compact. -/
theorem quasiCompact_presentationLimitPreAdicSpaceComap {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (P : PairOfDefinition A) (P' : PairOfDefinition B)
    (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)) (φ : Pair.Hom S T)
    (hopen : ∀ J : Ideal A, IsOpen (J : Set A) → IsOpen (Ideal.map φ.toRingHom J : Set B)) :
    QuasiCompact (X := ⟨_, isAdic_presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hsheaf⟩) (Y := ⟨_, hA⟩)
      (ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom
        φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf)) := by
  have h := φ.isSpectralMap_spaComap hopen
  rw [Pair.Hom.spaComap_def] at h
  rw [quasiCompact_iff_isSpectralMap, ObjectProperty.homMk_hom,
    presentationLimitPreAdicSpaceComap_toHom, presentationLimitPresheafedSpaceComap_base]
  exact h

end AdicSpace

end TauCeti
