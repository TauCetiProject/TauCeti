/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocalAtTarget
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Restrict
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair

import TauCeti.Topology.Category.TopCat.Opens

/-!
# Closed immersions of pre-adic spaces

Let `(A, A⁺)` be a Huber pair and `J ⊆ A` an ideal. The quotient Huber pair `(A ⧸ J, (A ⧸ J)⁺)`
has as plus ring the integral closure of the image of `A⁺`, and the quotient map induces a closed
embedding `Spa(A ⧸ J, (A ⧸ J)⁺) → Spa(A, A⁺)` onto the points whose support contains `J` (Wedhorn,
Proposition 7.38). When the structure presheaf of the quotient pair is a sheaf, this map underlies
a morphism of pre-adic spaces, the *quotient morphism*.

Closed immersions are defined affinoid-locally from these models: a morphism `f : X ⟶ Y` of
pre-adic spaces is a closed immersion when every point of `Y` has an open neighbourhood `V` over
which `f` is isomorphic to the quotient morphism of a Huber pair by a closed ideal with sheafy
quotient. The ideal is required to be closed; for a complete Hausdorff Huber ring `A` this makes
`A ⧸ J` complete and Hausdorff again.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceQuotientComap`: the quotient morphism
  `Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)` of pre-adic spaces, for a sheafy quotient pair.
* `TauCeti.PreAdicSpace.IsClosedImmersion`: a morphism of pre-adic spaces that is, locally on the
  target, isomorphic to a quotient morphism by a closed ideal.

## Main results

* `TauCeti.ValuationSpectrum.isClosedEmbedding_presentationLimitPreAdicSpaceQuotientComap_base`
  and `TauCeti.ValuationSpectrum.range_presentationLimitPreAdicSpaceQuotientComap_base`: the
  quotient morphism is a closed embedding of the underlying spaces, onto the points whose support
  contains `J`.
* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComap_quotientLift_comp_quotientComap`:
  the morphism induced by a morphism of Huber pairs annihilating `J` factors through the quotient
  morphism.
* `TauCeti.ValuationSpectrum.isClosedImmersion_presentationLimitPreAdicSpaceQuotientComap`: the
  quotient morphism by a closed ideal is a closed immersion.
* `TauCeti.PreAdicSpace.IsClosedImmersion.isClosedEmbedding`: a closed immersion is a closed
  embedding of the underlying topological spaces.
* `TauCeti.PreAdicSpace.IsClosedImmersion.respectsIso`: being a closed immersion is invariant
  under isomorphisms of the source and of the target.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.22, Proposition 7.38, and §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber

universe u

namespace ValuationSpectrum

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (S : Pair A) (P : PairOfDefinition A)

variable (hP : P.ringOfDefinition ≤ S.plus) (J : Ideal A)

/-- **The quotient morphism** `Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)` of pre-adic spaces, for a Huber
pair `(A, A⁺)` and an ideal `J` whose quotient pair has a sheaf as structure presheaf. It is the
morphism induced by the quotient map `A → A ⧸ J`, which is open, so carries open ideals to open
ideals. -/
noncomputable def presentationLimitPreAdicSpaceQuotientComap
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa (S.quotient J).plus))
      (presentationLimitPresheaf (P.quotient J) (S.quotient J).plus)) :
    presentationLimitPreAdicSpace (P.quotient J) (S.quotient J).plus
        (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem
        (P.quotient_ringOfDefinition_le_quotient_plus hP J) ⟶
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP :=
  presentationLimitPreAdicSpaceComap (Ideal.Quotient.mk J)
    (QuotientRing.isOpenQuotientMap_mk J).continuous
    (fun I hI ↦ by
      rw [Ideal.map_eq_image_of_surjective _ Ideal.Quotient.mk_surjective]
      exact (QuotientRing.isOpenQuotientMap_mk J).isOpenMap _ hI)
    (Pair.Hom.toRingHom_quotientHom S J ▸ (Pair.quotientHom S J).map_mem_plus)
    S.isRingOfIntegralElements.isPowerBounded_of_mem
    (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem hP
    (P.quotient_ringOfDefinition_le_quotient_plus hP J) hsheaf

variable (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa (S.quotient J).plus))
  (presentationLimitPresheaf (P.quotient J) (S.quotient J).plus))

/-- The map of underlying spaces of the quotient morphism pulls valuations back along the
quotient map `A → A ⧸ J`. -/
@[simp]
theorem presentationLimitPreAdicSpaceQuotientComap_base_apply_val
    (x : presentationLimitPreAdicSpace (P.quotient J) (S.quotient J).plus
      (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem
      (P.quotient_ringOfDefinition_le_quotient_plus hP J)) :
    ((presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf).base x).1 =
      comap (Ideal.Quotient.mk J) x.1 := by
  rw [presentationLimitPreAdicSpaceQuotientComap, presentationLimitPreAdicSpaceComap_toHom,
    presentationLimitPresheafedSpaceComap_base]
  exact spaComap_val _ _ _ _ _ x

/-- The map of underlying spaces of the quotient morphism is the map of adic spectra induced by
the quotient morphism of Huber pairs. -/
theorem coe_presentationLimitPreAdicSpaceQuotientComap_base :
    ⇑(presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf).base =
      (Pair.quotientHom S J).spaComap :=
  funext fun x ↦ Subtype.ext <|
    calc ((presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf).base x).1
        _ = comap (Ideal.Quotient.mk J) x.1 :=
          presentationLimitPreAdicSpaceQuotientComap_base_apply_val S P hP J hsheaf x
        _ = comap (Pair.quotientHom S J).toRingHom x.1 := by
          rw [Pair.Hom.toRingHom_quotientHom]
        _ = ((Pair.quotientHom S J).spaComap x).1 := (Pair.Hom.spaComap_val _ x).symm

/-- **Wedhorn Proposition 7.38 for pre-adic spaces:** the quotient morphism is a closed embedding
of the underlying topological spaces. -/
theorem isClosedEmbedding_presentationLimitPreAdicSpaceQuotientComap_base :
    IsClosedEmbedding (presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf).base := by
  rw [coe_presentationLimitPreAdicSpaceQuotientComap_base]
  exact Pair.Hom.isClosedEmbedding_spaComap_quotientHom S J

/-- The image of the quotient morphism consists of the points of `Spa(A, A⁺)` whose support
contains `J`. -/
theorem range_presentationLimitPreAdicSpaceQuotientComap_base :
    Set.range (presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf).base =
      Subtype.val ⁻¹' {v : Spv A | J ≤ v.supp} := by
  rw [coe_presentationLimitPreAdicSpaceQuotientComap_base]
  exact Pair.Hom.range_spaComap_quotientHom S J

/-- **The factorisation property of the quotient morphism** (Wedhorn, Proposition 7.38): if a
morphism `f : (A, A⁺) → (B, B⁺)` of Huber pairs annihilates `J`, the morphism
`Spa(B, B⁺) ⟶ Spa(A, A⁺)` of pre-adic spaces induced by `f` factors through the quotient
morphism, as the morphism induced by the factorisation `(A ⧸ J, (A ⧸ J)⁺) → (B, B⁺)` of `f`
(`TauCeti.Huber.Pair.Hom.quotientLift`) followed by the quotient morphism. -/
theorem presentationLimitPreAdicSpaceComap_quotientLift_comp_quotientComap {B : Type u}
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B] {T : Pair B}
    (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus) (f : Pair.Hom S T)
    (hf : J ≤ RingHom.ker f.toRingHom)
    (hopen : ∀ ⦃I : Ideal A⦄, IsOpen (I : Set A) → IsOpen (I.map f.toRingHom : Set B))
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus)) :
    presentationLimitPreAdicSpaceComap (f.quotientLift J hf).toRingHom
        (f.quotientLift J hf).continuous_toRingHom
        (fun _ hI ↦ f.isOpen_map_quotientLift J hf hopen hI) (f.quotientLift J hf).map_mem_plus
        (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem
        (P.quotient_ringOfDefinition_le_quotient_plus hP J) hP' hsheafT ≫
      presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf =
    presentationLimitPreAdicSpaceComap f.toRingHom f.continuous_toRingHom hopen f.map_mem_plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheafT := by
  rw [presentationLimitPreAdicSpaceQuotientComap, ← presentationLimitPreAdicSpaceComap_comp]
  congr 1
  rw [← Pair.Hom.toRingHom_quotientHom, ← Pair.Hom.toRingHom_comp,
    Pair.Hom.quotientLift_comp_quotientHom]

end ValuationSpectrum

namespace PreAdicSpace

open ValuationSpectrum

variable {X Y : PreAdicSpace.{u}}

/-- A morphism `f : X ⟶ Y` of pre-adic spaces is a **closed immersion** when it is, locally on
`Y`, the quotient morphism of a Huber pair by a closed ideal with sheafy quotient: every point of
`Y` has an open neighbourhood `V` together with a Huber pair `(A, A⁺)`, a closed ideal `J ⊆ A` for
which `Spa(A ⧸ J, (A ⧸ J)⁺)` has a sheaf as structure presheaf, and isomorphisms identifying `Y`
restricted to `V` with `Spa(A, A⁺)` and `X` restricted to `f⁻¹(V)` with `Spa(A ⧸ J, (A ⧸ J)⁺)`,
under which `f` becomes `presentationLimitPreAdicSpaceQuotientComap`. -/
def IsClosedImmersion (f : X ⟶ Y) : Prop :=
  ∀ y : Y, ∃ (V : Opens Y) (_ : y ∈ V) (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
    (_ : IsTopologicalRing A) (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) (J : Ideal A) (_ : IsClosed (J : Set A))
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa (S.quotient J).plus))
      (presentationLimitPresheaf (P.quotient J) (S.quotient J).plus))
    (eV : Y.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP)
    (eU : X.restrict ((Opens.map f.base).obj V).isOpenEmbedding ≅
      presentationLimitPreAdicSpace (P.quotient J) (S.quotient J).plus
        (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem
        (P.quotient_ringOfDefinition_le_quotient_plus hP J)),
    X.ofRestrict _ ≫ f =
      eU.hom ≫ presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf ≫ eV.inv ≫
        Y.ofRestrict _

/-- Unfolding lemma for `TauCeti.PreAdicSpace.IsClosedImmersion`. -/
theorem isClosedImmersion_iff (f : X ⟶ Y) : IsClosedImmersion f ↔
    ∀ y : Y, ∃ (V : Opens Y) (_ : y ∈ V) (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsTopologicalRing A) (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A)
      (hP : P.ringOfDefinition ≤ S.plus) (J : Ideal A) (_ : IsClosed (J : Set A))
      (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa (S.quotient J).plus))
        (presentationLimitPresheaf (P.quotient J) (S.quotient J).plus))
      (eV : Y.restrict V.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          hP)
      (eU : X.restrict ((Opens.map f.base).obj V).isOpenEmbedding ≅
        presentationLimitPreAdicSpace (P.quotient J) (S.quotient J).plus
          (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem
          (P.quotient_ringOfDefinition_le_quotient_plus hP J)),
      X.ofRestrict _ ≫ f =
        eU.hom ≫ presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf ≫ eV.inv ≫
          Y.ofRestrict _ :=
  Iff.rfl

/-- Over each neighbourhood `V` supplied by the definition, a closed immersion restricts to a
closed embedding `f⁻¹(V) → V`: there it is the quotient morphism, up to homeomorphisms. -/
private theorem IsClosedImmersion.exists_isClosedEmbedding_restrictPreimage {f : X ⟶ Y}
    (hf : IsClosedImmersion f) (y : Y) :
    ∃ V : Opens Y, y ∈ V ∧ IsClosedEmbedding ((V : Set Y).restrictPreimage f.base) := by
  obtain ⟨V, hy, A, _, _, _, _, S, P, hP, J, -, hsheaf, eV, eU, hfac⟩ := hf y
  refine ⟨V, hy, ?_⟩
  -- the defining square, on underlying spaces
  have hfac' := congrArg (fun g ↦ ConcreteCategory.hom (forgetToTop.map g)) hfac
  simp only [Functor.map_comp, TopCat.hom_comp] at hfac'
  have hU := (TopCat.homeoOfIso (forgetToTop.mapIso eU)).isClosedEmbedding
  have hV := (TopCat.homeoOfIso (forgetToTop.mapIso eV.symm)).isClosedEmbedding
  have hq := isClosedEmbedding_presentationLimitPreAdicSpaceQuotientComap_base S P hP J hsheaf
  -- over `V`, `f` is the quotient morphism up to the homeomorphisms `eU` and `eV`
  have heq : (V : Set Y).restrictPreimage f.base =
      TopCat.homeoOfIso (forgetToTop.mapIso eV.symm) ∘
        (presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf).base ∘
          TopCat.homeoOfIso (forgetToTop.mapIso eU) :=
    funext fun x ↦ Subtype.ext (congrArg (fun g ↦ g x) hfac')
  rw [heq]
  exact hV.comp (hq.comp hU)

/-- **A closed immersion is a closed embedding** of the underlying topological spaces. Being a
closed embedding is local on the target, and over each neighbourhood supplied by the definition
the morphism is the quotient morphism, which is a closed embedding by Wedhorn's Proposition
7.38. -/
theorem IsClosedImmersion.isClosedEmbedding {f : X ⟶ Y} (hf : IsClosedImmersion f) :
    IsClosedEmbedding f.base := by
  choose V hV hemb using hf.exists_isClosedEmbedding_restrictPreimage
  have hcov : IsOpenCover V := IsOpenCover.of_sets _ <| Set.eq_univ_of_forall fun y ↦
    Set.mem_iUnion.mpr ⟨y, hV y⟩
  exact (hcov.isClosedEmbedding_iff_restrictPreimage f.base.hom.continuous).mpr hemb

/-- Precomposing a closed immersion with an isomorphism gives a closed immersion: over the same
neighbourhoods, `e` identifies the restrictions of the two sources. -/
private theorem IsClosedImmersion.iso_hom_comp {X' : PreAdicSpace.{u}} (e : X' ≅ X) {f : X ⟶ Y}
    (hf : IsClosedImmersion f) : IsClosedImmersion (e.hom ≫ f) := by
  intro y
  obtain ⟨V, hy, A, _, _, _, _, S, P, hP, J, hJ, hsheaf, eV, eU, hfac⟩ := hf y
  -- `e⁻¹((e.hom ≫ f)⁻¹(V)) = f⁻¹(V)`
  have key := Opens.map_inv_obj_map_hom_obj (forgetToTop.mapIso e) ((Opens.map f.base).obj V)
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, forgetToTop_map] at key
  have hr : Set.range ((Opens.map e.inv.base).obj ((Opens.map (e.hom ≫ f).base).obj V)).inclusion'
      = Set.range ((Opens.map f.base).obj V).inclusion' := by
    rw [Opens.set_range_inclusion', Opens.set_range_inclusion']
    exact congrArg SetLike.coe key
  refine ⟨V, hy, A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, J, hJ,
    hsheaf, eV, restrictIso e _ ≪≫
      restrictIsoOfRangeEq _ (Opens.isOpenEmbedding _) (Opens.isOpenEmbedding _) hr ≪≫ eU, ?_⟩
  rw [← Category.assoc, ← restrictIso_hom_ofRestrict, Category.assoc,
    ← restrictIsoOfRangeEq_hom_ofRestrict X (Opens.isOpenEmbedding _)
      (Opens.isOpenEmbedding _) hr, Category.assoc, hfac]
  simp

/-- Postcomposing a closed immersion with an isomorphism `e : Y ≅ Y'` gives a closed immersion:
`e` carries the neighbourhoods of the definition to neighbourhoods in `Y'`, identifying the
restrictions of `Y` and `Y'` to them. -/
private theorem IsClosedImmersion.comp_iso_hom {Y' : PreAdicSpace.{u}} (e : Y ≅ Y') {f : X ⟶ Y}
    (hf : IsClosedImmersion f) : IsClosedImmersion (f ≫ e.hom) := by
  intro y
  obtain ⟨V, hy, A, _, _, _, _, S, P, hP, J, hJ, hsheaf, eV, eU, hfac⟩ := hf (e.inv.base y)
  -- `(f ≫ e.hom)⁻¹(e(V)) = f⁻¹(V)`
  have key := Opens.map_hom_obj_map_inv_obj (forgetToTop.mapIso e) V
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, forgetToTop_map] at key
  have hr : Set.range ((Opens.map (f ≫ e.hom).base).obj ((Opens.map e.inv.base).obj V)).inclusion'
      = Set.range ((Opens.map f.base).obj V).inclusion' := by
    rw [Opens.set_range_inclusion', Opens.set_range_inclusion']
    exact congrArg (fun U ↦ ((Opens.map f.base).obj U : Set X)) key
  refine ⟨(Opens.map e.inv.base).obj V, hy, A, inferInstance, inferInstance, inferInstance,
    inferInstance, S, P, hP, J, hJ, hsheaf, (restrictIso e V).symm ≪≫ eV,
    restrictIsoOfRangeEq _ (Opens.isOpenEmbedding _) (Opens.isOpenEmbedding _) hr ≪≫ eU, ?_⟩
  rw [← restrictIsoOfRangeEq_hom_ofRestrict X (Opens.isOpenEmbedding _)
    (Opens.isOpenEmbedding _) hr, Category.assoc, reassoc_of% hfac]
  simp

/-- Being a closed immersion is invariant under isomorphisms of the source and of the target. -/
instance IsClosedImmersion.respectsIso :
    MorphismProperty.RespectsIso (@IsClosedImmersion.{u}) :=
  MorphismProperty.RespectsIso.mk _ (fun e _ hf ↦ hf.iso_hom_comp e)
    (fun e _ hf ↦ hf.comp_iso_hom e)

end PreAdicSpace

namespace ValuationSpectrum

open PreAdicSpace

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) (J : Ideal A)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa (S.quotient J).plus))
    (presentationLimitPresheaf (P.quotient J) (S.quotient J).plus))

/-- **The quotient morphism by a closed ideal is a closed immersion**, witnessed over the whole
of `Spa(A, A⁺)`. -/
theorem isClosedImmersion_presentationLimitPreAdicSpaceQuotientComap
    (hJ : IsClosed (J : Set A)) :
    IsClosedImmersion (presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf) := by
  refine fun _ ↦ ⟨⊤, trivial, A, inferInstance, inferInstance, inferInstance, inferInstance, S, P,
    hP, J, hJ, hsheaf, restrictTopIso _,
    restrictIsoOfRangeEq _ _ (Opens.isOpenEmbedding ⊤) ?_ ≪≫ restrictTopIso _, ?_⟩
  · rw [Opens.map_top]
  · rw [← restrictTopIso_hom, Iso.inv_hom_id, Category.comp_id, Iso.trans_hom, restrictTopIso_hom,
      Category.assoc, restrictIsoOfRangeEq_hom_ofRestrict_assoc]

end ValuationSpectrum

end TauCeti

end
