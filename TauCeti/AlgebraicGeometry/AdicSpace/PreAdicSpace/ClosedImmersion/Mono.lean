/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.ClosedImmersion.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Quotient

/-!
# Closed immersions are monomorphisms

Let `(A, A⁺)` be a Huber pair and `J ⊆ A` an ideal. Over a rational open `R(T/s)` of
`Spa(A, A⁺)`, the coordinate ring of its preimage in `Spa(A ⧸ J, (A ⧸ J)⁺)` is the quotient
`(A ⧸ J)⟨q(T)/q(s)⟩` of `A⟨T/s⟩`
(`TauCeti.Huber.PairOfDefinition.Presentation.mapHom_quotientMk_surjective`). Since the rational
opens of `Spa(A ⧸ J, (A ⧸ J)⁺)` of this form are a basis, every germ of the structure presheaf
of `Spa(A ⧸ J, (A ⧸ J)⁺)` comes from a germ of that of `Spa(A, A⁺)`: the stalk maps of the
quotient morphism are surjective. A closed immersion is locally on the target a quotient
morphism, so its stalk maps are surjective as well.

A morphism of sheafed spaces which is injective on points and has surjective stalk maps is a
monomorphism (Mathlib's `AlgebraicGeometry.SheafedSpace.mono_of_base_injective_of_stalk_epi`), as
two morphisms into its source with the same composite agree on points and on stalks, and sections
of a sheaf are determined by their germs. So closed immersions are
monomorphisms among sheafy pre-adic spaces and among adic spaces. This is the uniqueness half of
the universal property of a closed immersion: a morphism into the target factors through it in at
most one way. For affinoid sources and morphisms induced by morphisms of Huber pairs killing `J`,
the factorisation exists by
`TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComap_quotientLift_comp_quotientComap`.

## Main results

* `TauCeti.ValuationSpectrum.stalkMap_presentationLimitPreAdicSpaceQuotientComap_surjective`: the
  stalk maps of the quotient morphism `Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)` are surjective.
* `TauCeti.PreAdicSpace.IsClosedImmersion.stalkMap_surjective`: the stalk maps of a closed
  immersion are surjective.
* `TauCeti.SheafyPreAdicSpace.mono_of_isClosedImmersion` and
  `TauCeti.AdicSpace.mono_of_isClosedImmersion`: closed immersions are monomorphisms in the
  categories of sheafy pre-adic spaces and of adic spaces.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 7.38 and §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti.ValuationSpectrum

open Huber Huber.PairOfDefinition

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) (J : Ideal A)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa (S.quotient J).plus))
    (presentationLimitPresheaf (P.quotient J) (S.quotient J).plus))

/-- **The stalk maps of the quotient morphism `Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)` are
surjective**: every germ at `x` is the germ of an element of `(A ⧸ J)⟨q(T)/q(s)⟩` for a rational
neighbourhood `R(T/s)` of the image of `x`, and such elements lift to `A⟨T/s⟩`. -/
theorem stalkMap_presentationLimitPreAdicSpaceQuotientComap_surjective
    (x : presentationLimitPreAdicSpace (P.quotient J) (S.quotient J).plus
      (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem
      (P.quotient_ringOfDefinition_le_quotient_plus hP J)) :
    Function.Surjective
      ((presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf).stalkMap x) := by
  classical
  have hbase := coe_presentationLimitPreAdicSpaceQuotientComap_base S P hP J hsheaf
  have hemb := isClosedEmbedding_presentationLimitPreAdicSpaceQuotientComap_base S P hP J hsheaf
  rw [presentationLimitPreAdicSpaceQuotientComap_def] at hbase hemb ⊢
  set f := presentationLimitPreAdicSpaceComap (P := P) (Ideal.Quotient.mk J) _ _ _ _ _ hP _ hsheaf
  intro t
  obtain ⟨p', hp', hxp', b, rfl⟩ := exists_presentationLimitRationalGerm_eq
    (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem x t
  -- `R(p')` is the preimage of an open `V` of `Spa(A, A⁺)`, which contains a rational
  -- neighbourhood `R(p)` of the image of `x`
  obtain ⟨V, hV, hVp'⟩ := hemb.isInducing.isOpen_iff.mp (spaBasicOpen _ p'.num p'.den).isOpen
  have hxV : f.base x ∈ (⟨V, hV⟩ : Opens _) := (Set.ext_iff.mp hVp' x).mpr hxp'
  obtain ⟨p, hp, hxp, hpV⟩ := exists_presentation_mem_spaBasicOpen_le P hxV
  -- the preimage of `R(p)` is `R(q)` for `q = (q(T), q(s))`, and `R(q) ⊆ R(p')`
  have hq : IsOpen (Ideal.span ((p.num.image (Ideal.Quotient.mk J) : Finset (A ⧸ J)) :
      Set (A ⧸ J)) : Set (A ⧸ J)) := by
    rw [Finset.coe_image, ← Ideal.map_span,
      Ideal.map_eq_image_of_surjective _ Ideal.Quotient.mk_surjective]
    exact (QuotientRing.isOpenQuotientMap_mk J).isOpenMap _ hp
  let q : Presentation (P.quotient J) := ⟨p.num.image (Ideal.Quotient.mk J),
    Ideal.Quotient.mk J p.den, hasDenominatorPower_of_isOpen_span _ _ _ _ hq⟩
  have hmem : ∀ w, w ∈ spaBasicOpen (S.quotient J).plus q.num q.den ↔
      f.base w ∈ spaBasicOpen S.plus p.num p.den := fun w ↦ by
    have h := Set.ext_iff.mp
      ((Pair.quotientHom S J).spaComap_preimage_rationalSubset p.num p.den) w
    simp only [Set.mem_preimage, Pair.Hom.toRingHom_quotientHom] at h
    refine mem_spaBasicOpen.trans (h.symm.trans ?_)
    rw [congrFun hbase w]
    exact mem_spaBasicOpen.symm
  have hsub : spaBasicOpen (S.quotient J).plus q.num q.den ≤
      spaBasicOpen (S.quotient J).plus p'.num p'.den := fun w hw ↦ by
    rw [← SetLike.mem_coe, ← hVp']
    exact hpV ((hmem w).mp hw)
  have hx : x ∈ spaBasicOpen (S.quotient J).plus q.num q.den := (hmem x).mpr hxp
  -- the germ of `b` is the germ of its restriction to `R(q)`, which lifts to `A⟨p⟩`, and the
  -- stalk map carries the germ of the lift to the germ of its image in `(A ⧸ J)⟨q⟩`
  obtain ⟨a, ha⟩ := Presentation.mapHom_quotientMk_surjective J p q rfl rfl
    ((homOfRationalSubsetSubset _ (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem
      (spaBasicOpen_le_spaBasicOpen_iff.mp hsub)).hom b)
  refine ⟨(presentationLimitRationalGerm S.isRingOfIntegralElements.isPowerBounded_of_mem p hp _
    hxp).hom a, ?_⟩
  rw [← presentationLimitRationalGerm_res _ p' q hp' hq hsub x hx]
  exact (congrArg (fun k ↦ k.hom a)
    (presentationLimitRationalGerm_comp_stalkMap_presentationLimitPreAdicSpaceComap _ _ _ _ _ _ _
      _ hsheaf p hp q hq rfl rfl x hxp hx)).trans
    (congrArg (presentationLimitRationalGerm
      (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem q hq x hx).hom ha)

end TauCeti.ValuationSpectrum

namespace TauCeti.PreAdicSpace

open ValuationSpectrum

universe u

variable {X Y : PreAdicSpace.{u}}

/-- **The stalk maps of a closed immersion are surjective**: around each point of the target, the
closed immersion is a quotient morphism up to isomorphisms and restrictions to opens, all of which
have bijective stalk maps. -/
theorem IsClosedImmersion.stalkMap_surjective {f : X ⟶ Y} (hf : IsClosedImmersion f) (x : X) :
    Function.Surjective (f.stalkMap x) := by
  obtain ⟨V, hV, A, _, _, _, _, S, P, hP, J, -, hsheaf, eV, eU, hfac⟩ :=
    (isClosedImmersion_iff f).mp hf (f.base x)
  -- `x` as a point of the restriction of `X` to `f⁻¹(V)`
  let x' : X.restrict ((Opens.map f.base).obj V).isOpenEmbedding := ⟨x, hV⟩
  have hR : Function.Surjective
      ((eU.hom ≫ presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf ≫ eV.inv ≫
        Y.ofRestrict _).stalkMap x') := by
    rw [stalkMap_comp, stalkMap_comp, stalkMap_comp]
    exact (ConcreteCategory.bijective_of_isIso (eU.hom.stalkMap x')).2.comp
      ((stalkMap_presentationLimitPreAdicSpaceQuotientComap_surjective S P hP J hsheaf _).comp
        ((ConcreteCategory.bijective_of_isIso (eV.inv.stalkMap _)).2.comp
          (ConcreteCategory.bijective_of_isIso ((Y.ofRestrict V.isOpenEmbedding).stalkMap _)).2))
  have hL : Function.Surjective ((X.ofRestrict _ ≫ f).stalkMap x') := hfac ▸ hR
  rw [stalkMap_comp] at hL
  -- the stalk map of `X.ofRestrict` at `x'` is bijective, so `f.stalkMap x` is surjective
  exact (Function.Surjective.of_comp_iff' (ConcreteCategory.bijective_of_isIso
    ((X.ofRestrict ((Opens.map f.base).obj V).isOpenEmbedding).stalkMap x')) _).mp hL

end TauCeti.PreAdicSpace

namespace TauCeti

open PreAdicSpace

universe u

/-- **Closed immersions of sheafy pre-adic spaces are monomorphisms**: a closed immersion is
injective on points and has surjective stalk maps, so it is a monomorphism of the underlying
sheafed spaces of rings, to which morphisms of sheafy pre-adic spaces are faithfully sent. -/
theorem SheafyPreAdicSpace.mono_of_isClosedImmersion {X Y : SheafyPreAdicSpace.{u}} (f : X ⟶ Y)
    (hf : IsClosedImmersion f.hom) : Mono f :=
  have : Mono (forgetToRingSheafedSpace.map f) := by
    refine SheafedSpace.mono_of_base_injective_of_stalk_epi _ ?_ fun x ↦ ?_
    · rw [forgetToRingSheafedSpace_map_hom]
      exact hf.isClosedEmbedding.injective
    · rw [forgetToRingSheafedSpace_map_hom]
      exact ConcreteCategory.epi_of_surjective _
        (Hom.stalkMap_def f.hom x ▸ hf.stalkMap_surjective x)
  forgetToRingSheafedSpace.mono_of_mono_map this

/-- **Closed immersions of adic spaces are monomorphisms**: a morphism into an adic space factors
through a closed immersion in at most one way. -/
theorem AdicSpace.mono_of_isClosedImmersion {X Y : AdicSpace.{u}} (f : X ⟶ Y)
    (hf : IsClosedImmersion f.hom) : Mono f :=
  have : Mono (AdicSpace.toSheafyPreAdicSpace.map f) :=
    SheafyPreAdicSpace.mono_of_isClosedImmersion _ hf
  AdicSpace.toSheafyPreAdicSpace.mono_of_mono_map this

end TauCeti
