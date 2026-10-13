/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Stalk.GlobalSections
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Integral
public import Mathlib.CategoryTheory.HomCongr

/-!
# Recovering Huber-pair maps from affinoid morphisms

For complete Hausdorff Huber pairs, pullback on global sections of a pre-adic morphism
`Spa(B,B⁺) → Spa(A,A⁺)` gives a continuous ring homomorphism `A → B`. Its pullback on
valuations is the original map on points, and it preserves the plus rings. Thus it is a
morphism of Huber pairs. Recovery respects identity and composition.

This is the global-sections direction of the correspondence between affinoid morphisms and
Huber-pair morphisms. It supplies the ring map to which a quotient factorisation can be applied.
No sheaf condition is required for this direction of the correspondence.

The construction uses Mathlib's `PresheafedSpace.Γ` and `Iso.homCongr`, the topological
isomorphism `presentationLimitTopIso`, and the characterisation of rings of integral elements
by valuations in `IsRingOfIntegralElements.mem_of_forall_vle_one`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and §8.3.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe u

variable {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A]
  (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- The global sections of the pre-adic spectrum of a complete Hausdorff pair are its
coefficient ring, as a topological ring. -/
noncomputable def presentationLimitPreAdicSpaceTopIso :
    ((presentationLimitPreAdicSpace P Aplus hAplus hP).toPresheafedSpace.presheaf.obj
      (Opposite.op ⊤)).obj ≅ _root_.TopCommRingCat.of A :=
  TopCommRingCat.isCompleteSeparated.ι.mapIso
    (eqToIso (presentationLimitPresheaf_obj P Aplus (Opposite.op ⊤)) ≪≫
      presentationLimitTopIso Aplus hAplus) ≪≫
    eqToIso (CompleteSeparatedTopCommRingCat.of_obj A)

/-- The inverse global-sections isomorphism is the canonical coefficient map. -/
@[simp]
theorem presentationLimitPreAdicSpaceTopIso_inv :
    (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).inv =
      eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm ≫
        TopCommRingCat.isCompleteSeparated.ι.map (toPresentationLimit (P := P) Aplus ⊤) ≫
          eqToHom (congrArg ObjectProperty.FullSubcategory.obj
            (presentationLimitPresheaf_obj P Aplus (Opposite.op ⊤)).symm) := by
  simp only [presentationLimitPreAdicSpaceTopIso, Iso.trans_inv,
    Functor.mapIso_inv, presentationLimitTopIso_inv]
  erw [Functor.map_comp]
  erw [eqToIso.inv, eqToIso.inv]
  erw [eqToHom_map TopCommRingCat.isCompleteSeparated.ι
    (presentationLimitPresheaf_obj P Aplus (Opposite.op ⊤)).symm]
  rfl

-- This equality compares the native topological-ring isomorphism with the coefficient map
-- used by the stalk-valuation API; the presheaf-object equalities supply the transports.
private theorem topIso_inv_comp_germ
    (x : presentationLimitPreAdicSpace P Aplus hAplus hP) :
    ((forget₂ _root_.TopCommRingCat CommRingCat).map
        (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).inv ≫
      (presentationLimitPreAdicSpace P Aplus hAplus hP).toRingPresheafedSpace.presheaf.germ
        ⊤ x (Opens.mem_top x)).hom = presentationLimitGlobalGerm P Aplus x := by
  erw [presentationLimitPreAdicSpaceTopIso_inv, presentationLimitGlobalGerm_def]
  apply congrArg CommRingCat.Hom.hom
  erw [Functor.map_comp, Functor.map_comp]
  erw [eqToHom_map, eqToHom_map, Category.assoc, Category.assoc]

variable {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [CompleteSpace B] [T0Space B]
  (P' : PairOfDefinition B) (Bplus : Subring B)
  (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b) (hP' : P'.ringOfDefinition ≤ Bplus)

private noncomputable def globalSectionsPullback
    (f : presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP) :
    _root_.TopCommRingCat.of A ⟶ _root_.TopCommRingCat.of B :=
  (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).homCongr
    (presentationLimitPreAdicSpaceTopIso P' Bplus hBplus hP')
    (TopCommRingCat.isCompleteSeparated.ι.map (PresheafedSpace.Γ.map
      (PreAdicSpace.forgetToPresheafedSpace.map f).op))

/-- The continuous ring homomorphism `A → B` obtained by pullback on global sections from a
morphism `Spa(B,B⁺) → Spa(A,A⁺)` of complete affinoid pre-adic spectra. -/
noncomputable def presentationLimitHomRingHom
    (f : presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP) : A →+* B :=
  ((forget₂ _root_.TopCommRingCat CommRingCat).map
    (globalSectionsPullback P Aplus hAplus hP P' Bplus hBplus hP' f)).hom

/-- The recovered ring homomorphism is the map on global sections transported through the
canonical topological ring isomorphisms. -/
theorem presentationLimitHomRingHom_def
    (f : presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP) :
    presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f =
      ((forget₂ _root_.TopCommRingCat CommRingCat).map
        ((presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).homCongr
          (presentationLimitPreAdicSpaceTopIso P' Bplus hBplus hP')
          (TopCommRingCat.isCompleteSeparated.ι.map
            (PresheafedSpace.Γ.map (PreAdicSpace.forgetToPresheafedSpace.map f).op)))).hom :=
  (rfl)

/-- Recovery produces a continuous ring homomorphism. -/
theorem continuous_presentationLimitHomRingHom
    (f : presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP) :
    Continuous (presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f) :=
  (globalSectionsPullback P Aplus hAplus hP P' Bplus hBplus hP' f).2

private theorem globalSectionsPullback_comp_germ
    (f : presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP)
    (x : presentationLimitPreAdicSpace P' Bplus hBplus hP') :
    (presentationLimitGlobalGerm P' Bplus x).comp
        (presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f) =
      (f.stalkMap x).hom.comp (presentationLimitGlobalGerm P Aplus (f.base x)) := by
  let F := forget₂ _root_.TopCommRingCat CommRingCat
  have hc : F.map (globalSectionsPullback P Aplus hAplus hP P' Bplus hBplus hP' f) ≫
      F.map (presentationLimitPreAdicSpaceTopIso P' Bplus hBplus hP').inv =
      F.map (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).inv ≫
        F.map (TopCommRingCat.isCompleteSeparated.ι.map (PresheafedSpace.Γ.map
          (PreAdicSpace.forgetToPresheafedSpace.map f).op)) := by
    have hc' : globalSectionsPullback P Aplus hAplus hP P' Bplus hBplus hP' f ≫
        (presentationLimitPreAdicSpaceTopIso P' Bplus hBplus hP').inv =
        (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).inv ≫
          TopCommRingCat.isCompleteSeparated.ι.map (PresheafedSpace.Γ.map
            (PreAdicSpace.forgetToPresheafedSpace.map f).op) := by
      exact (Iso.comp_inv_eq (presentationLimitPreAdicSpaceTopIso P' Bplus hBplus hP')).mpr
        (Category.assoc (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).inv
          (TopCommRingCat.isCompleteSeparated.ι.map (PresheafedSpace.Γ.map
            (PreAdicSpace.forgetToPresheafedSpace.map f).op))
          (presentationLimitPreAdicSpaceTopIso P' Bplus hBplus hP').hom).symm
    exact (Functor.map_comp F _ _).symm.trans
      ((congrArg F.map hc').trans (Functor.map_comp F _ _))
  have hg := PresheafedSpace.stalkMap_germ (PreAdicSpace.toRingPresheafedSpaceHom f.toHom)
    ⊤ x (Opens.mem_top _)
  have hcat := (congrArg (fun k ↦ k ≫
    (presentationLimitPreAdicSpace P' Bplus hBplus hP').toRingPresheafedSpace.presheaf.germ
      ⊤ x (Opens.mem_top x)) hc).trans
    ((Category.assoc _ _ _).trans (congrArg
      (fun k ↦ F.map (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).inv ≫ k) hg.symm))
  erw [← topIso_inv_comp_germ P Aplus hAplus hP (f.base x),
    ← topIso_inv_comp_germ P' Bplus hBplus hP' x, PreAdicSpace.Hom.stalkMap_def]
  exact congrArg CommRingCat.Hom.hom hcat

/-- The map on points of an affinoid pre-adic morphism is pullback along its recovered ring
homomorphism. Equality is in the valuation spectrum, so no representative value group is chosen. -/
theorem base_eq_comap_presentationLimitHomRingHom
    (f : presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP)
    (x : presentationLimitPreAdicSpace P' Bplus hBplus hP') :
    (f.base x : spa Aplus).1 =
      comap (presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f)
        (x : spa Bplus).1 := by
  calc
    (f.base x : spa Aplus).1 =
        comap (presentationLimitGlobalGerm P Aplus (f.base x))
          ((presentationLimitPreAdicSpace P Aplus hAplus hP).stalkValuation (f.base x)) :=
      ((congrArg (comap (presentationLimitGlobalGerm P Aplus (f.base x)))
        (presentationLimitPreAdicSpace_stalkValuation P Aplus hAplus hP (f.base x))).trans
          (comap_presentationLimitGlobalGerm P Aplus hAplus hP (f.base x))).symm
    _ = comap ((f.stalkMap x).hom.comp (presentationLimitGlobalGerm P Aplus (f.base x)))
        ((presentationLimitPreAdicSpace P' Bplus hBplus hP').stalkValuation x) := by
      rw [f.stalkValuation_eq_comap]
      exact (congrFun (comap_comp (presentationLimitGlobalGerm P Aplus (f.base x))
        (f.stalkMap x).hom)
        ((presentationLimitPreAdicSpace P' Bplus hBplus hP').stalkValuation x)).symm
    _ = comap ((presentationLimitGlobalGerm P' Bplus x).comp
        (presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f))
        ((presentationLimitPreAdicSpace P' Bplus hBplus hP').stalkValuation x) :=
      congrArg (fun g ↦ comap g
        ((presentationLimitPreAdicSpace P' Bplus hBplus hP').stalkValuation x))
        (globalSectionsPullback_comp_germ P Aplus hAplus hP P' Bplus hBplus hP' f x).symm
    _ = comap (presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f)
        (x : spa Bplus).1 := by
      exact (congrFun (comap_comp
        (presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f)
        (presentationLimitGlobalGerm P' Bplus x))
        ((presentationLimitPreAdicSpace P' Bplus hBplus hP').stalkValuation x)).trans
        (congrArg (comap (presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f))
          ((congrArg (comap (presentationLimitGlobalGerm P' Bplus x))
            (presentationLimitPreAdicSpace_stalkValuation P' Bplus hBplus hP' x)).trans
              (comap_presentationLimitGlobalGerm P' Bplus hBplus hP' x)))

/-- The identity morphism recovers the identity ring homomorphism. -/
@[simp]
theorem presentationLimitHomRingHom_id :
    presentationLimitHomRingHom P Aplus hAplus hP P Aplus hAplus hP
      (𝟙 (presentationLimitPreAdicSpace P Aplus hAplus hP)) = RingHom.id A := by
  have htop : globalSectionsPullback P Aplus hAplus hP P Aplus hAplus hP
      (𝟙 (presentationLimitPreAdicSpace P Aplus hAplus hP)) =
      𝟙 (_root_.TopCommRingCat.of A) := by
    rw [globalSectionsPullback]
    have hi := (PreAdicSpace.forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ ⋙
      TopCommRingCat.isCompleteSeparated.ι).map_id
      (Opposite.op (presentationLimitPreAdicSpace P Aplus hAplus hP))
    exact (congrArg (fun g ↦ (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).inv ≫ g ≫
      (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).hom) hi).trans
      ((congrArg (fun g ↦ (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).inv ≫ g)
        (Category.id_comp (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).hom)).trans
          (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).inv_hom_id)
  exact congrArg (fun g ↦ ((forget₂ _root_.TopCommRingCat CommRingCat).map g).hom) htop

variable {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
  [IsTopologicalRing C] [CompleteSpace C] [T0Space C]
  (P'' : PairOfDefinition C) (Cplus : Subring C)
  (hCplus : ∀ ⦃c⦄, c ∈ Cplus → IsPowerBounded c) (hP'' : P''.ringOfDefinition ≤ Cplus)

/-- Recovery from global sections is contravariant with respect to composition. -/
@[simp]
theorem presentationLimitHomRingHom_comp
    (f : presentationLimitPreAdicSpace P'' Cplus hCplus hP'' ⟶
      presentationLimitPreAdicSpace P' Bplus hBplus hP')
    (g : presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP) :
    presentationLimitHomRingHom P Aplus hAplus hP P'' Cplus hCplus hP'' (f ≫ g) =
      (presentationLimitHomRingHom P' Bplus hBplus hP' P'' Cplus hCplus hP'' f).comp
        (presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' g) := by
  have hc := (PreAdicSpace.forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ ⋙
    TopCommRingCat.isCompleteSeparated.ι).map_comp g.op f.op
  have htop := (congrArg ((presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).homCongr
    (presentationLimitPreAdicSpaceTopIso P'' Cplus hCplus hP'')) hc).trans
    (Iso.homCongr_comp (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP)
      (presentationLimitPreAdicSpaceTopIso P' Bplus hBplus hP')
      (presentationLimitPreAdicSpaceTopIso P'' Cplus hCplus hP'') _ _)
  exact congrArg (fun k ↦ ((forget₂ _root_.TopCommRingCat CommRingCat).map k).hom) htop

variable [IsHuberRing B]
/-- The recovered ring map carries the source plus ring into the target plus ring when the
latter is a ring of integral elements. -/
theorem presentationLimitHomRingHom_mem_plus
    (hB : IsRingOfIntegralElements Bplus)
    (f : presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP) {a : A} (ha : a ∈ Aplus) :
    presentationLimitHomRingHom P Aplus hAplus hP P' Bplus hBplus hP' f a ∈ Bplus := by
  apply hB.mem_of_forall_vle_one
  intro v hv
  let x : presentationLimitPreAdicSpace P' Bplus hBplus hP' := ⟨v, hv⟩
  have hx := ((mem_spa_iff Aplus (f.base x : spa Aplus).1).mp (f.base x : spa Aplus).2).2 a ha
  rw [base_eq_comap_presentationLimitHomRingHom, comap_vle, map_one] at hx
  exact hx

variable [IsHuberRing A]
/-- A morphism between the pre-adic spectra of complete Hausdorff Huber pairs determines a
continuous morphism of the Huber pairs, by pullback on global sections. -/
noncomputable def presentationLimitHomPairHom (S : Pair A) (T : Pair B)
    (hS : P.ringOfDefinition ≤ S.plus) (hT : P'.ringOfDefinition ≤ T.plus)
    (f : presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem
      hT ⟶
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS) :
    Pair.Hom S T where
  toRingHom := presentationLimitHomRingHom P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hS
    P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hT f
  continuous_toRingHom := (globalSectionsPullback P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hS P' T.plus
    T.isRingOfIntegralElements.isPowerBounded_of_mem hT f).2
  map_mem_plus _ ha := presentationLimitHomRingHom_mem_plus P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hS P' T.plus
    T.isRingOfIntegralElements.isPowerBounded_of_mem hT T.isRingOfIntegralElements f ha

/-- The underlying ring map of the recovered Huber-pair map is the recovered section map. -/
@[simp]
theorem presentationLimitHomPairHom_toRingHom (S : Pair A) (T : Pair B)
    (hS : P.ringOfDefinition ≤ S.plus) (hT : P'.ringOfDefinition ≤ T.plus)
    (f : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hT ⟶
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS) :
    (presentationLimitHomPairHom P P' S T hS hT f).toRingHom =
      presentationLimitHomRingHom P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS
        P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hT f :=
  (rfl)

end TauCeti.ValuationSpectrum

end
