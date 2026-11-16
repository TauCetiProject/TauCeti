/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.PlusWeaklyFiniteType
public import TauCeti.AlgebraicGeometry.AdicSpace.Pullback.Affinoid
public import TauCeti.AlgebraicGeometry.AdicSpace.Pullback.Cover
public import TauCeti.AlgebraicGeometry.AdicSpace.Pullback.OpenImmersion

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Sheafy
import TauCeti.RingTheory.Huber.TensorProduct.TopologicallyFiniteType
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel

/-!
# Existence and base-change stability of fibre products of adic spaces

In the category `(Adic)` of adic spaces (`TauCeti.AdicSpace`), fibre products do not exist in full
generality because completed tensor products of sheafy Huber rings need not be sheafy. Following
Huber (1994, Proposition 3.7; 1996, Proposition 1.2.2(b) and Corollary 1.2.3) and Wedhorn
(§8.6, Theorem 8.56 and Remark 8.57(1)), this file establishes the existence of the fibre product
`X ×_S Y` and its base-change stability whenever one morphism is locally of weakly finite type
(`TauCeti.AdicSpace.LocallyOfWeaklyFiniteType`), the other morphism is adic
(`TauCeti.AdicSpace.IsAdic`), and the adic factor is locally stably sheafy
(`TauCeti.AdicSpace.IsLocallyStablySheafy` — for instance, any locally noetherian analytic adic
space).

## Existence

1. **Open subspaces and open-immersion pullbacks**: an open `U` of an adic space `X` restricts to an
   adic space `X.restrict U` with canonical open immersion `X.ofRestrict U : X.restrict U ⟶ X`, and
   open immersions admit pullbacks along arbitrary morphisms in `AdicSpace`
   (`TauCeti.AdicSpace.isPullback_restrictPreimage`,
   `TauCeti.AdicSpace.hasPullback_of_isOpenImmersion_left`, from
   `TauCeti.AlgebraicGeometry.AdicSpace.Pullback.OpenImmersion`).
2. **Global gluing**: given `f : X ⟶ S` locally of weakly finite type and `g : Y ⟶ S` adic with `Y`
   locally stably sheafy, `X` is covered by complete Hausdorff affinoid charts `(U_x, V_x)` of `f`
   (`LocallyOfWeaklyFiniteType.exists_complete_chart`). Since fibre products in `AdicSpace` are
   local on the source (`hasPullback_of_cover`), existence reduces to each chart `U_x ⟶ V_x` after
   base-changing `g` to `g⁻¹(V_x)` (`IsPullback.paste_vert`). Covering `g⁻¹(V_x)` by stably sheafy
   open affinoids `W_y` and applying `hasPullback_of_cover` in the symmetric variable reduces to
   the affinoid completed tensor product `Spa((C, C⁺) ⊗̂_A (B, B⁺))`
   (`isPullback_ofPresentation_completedTensor`,
   `isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_right`).

## Base-change stability

Given *any* pullback square `IsPullback p q f g` in `AdicSpace` with `f : X ⟶ S` chart-locally `Q`,
`g : Y ⟶ S` adic, and `Y` locally stably sheafy, around any point `z` of `Z` one chooses a complete
chart `U ⊆ X`, `V ⊆ S` of `f` at `p(z)` and a stably sheafy affinoid open `W ⊆ g⁻¹(V)` of `Y` at
`q(z)`. Both `Z|_{p⁻¹(U) ∩ q⁻¹(W)}` (`isPullback_restrict_inf_of_isPullback`) and
`Spa((C, C⁺) ⊗̂_A (B, B⁺))` are pullbacks of the restricted cospan `(X|_U ⟶ S, Y|_W ⟶ S)`, so
uniqueness of pullbacks (`IsPullback.isoIsPullback`) identifies `q` locally with `Spa(inr)` and `p`
locally with `Spa(inl)`. From the ring- and pair-level base-change theorems
(`TauCeti.Huber.CompletedTensor.isTopologicallyFiniteType_inr`,
`TauCeti.Huber.Pair.completedTensor.isPlusWeaklyFiniteType_inr`,
`TauCeti.Huber.Pair.completedTensor.isTopologicallyFiniteType_inr`,
`TauCeti.Huber.CompletedTensor.isAdicHom_inl`), this yields base-change stability of:

* `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType`,
* `TauCeti.AdicSpace.LocallyOfPlusWeaklyFiniteType`,
* `TauCeti.PreAdicSpace.LocallyOfFiniteType` (along adic base change),
* `TauCeti.AdicSpace.IsAdic` (along base change locally of weakly finite type), and
* `TauCeti.AdicSpace.IsLocallyStablySheafy`, `TauCeti.AdicSpace.IsLocallyNoetherian`, and
  `TauCeti.AdicSpace.IsLocallyHuberStandard` on the fibre product.

## Main results

* `TauCeti.AdicSpace.hasPullback_of_locallyOfWeaklyFiniteType_left`,
  `TauCeti.AdicSpace.hasPullback_of_locallyOfWeaklyFiniteType_right`: existence of `X ×_S Y` in
  `AdicSpace`, together with specializations to `+`weakly finite type, finite type, analytic bases,
  and locally noetherian analytic factors.
* `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType.of_isPullback`,
  `TauCeti.AdicSpace.LocallyOfPlusWeaklyFiniteType.of_isPullback`,
  `TauCeti.AdicSpace.locallyOfFiniteType_of_isPullback`,
  `TauCeti.AdicSpace.IsAdic.of_isPullback_of_locallyOfWeaklyFiniteType`: base-change stability on
  arbitrary pullback squares (and `pullback.fst` / `pullback.snd` corollaries).
* `TauCeti.AdicSpace.IsLocallyStablySheafy.of_isPullback_of_locallyOfWeaklyFiniteType`,
  `TauCeti.AdicSpace.IsLocallyNoetherian.of_isPullback_of_locallyOfWeaklyFiniteType`,
  `TauCeti.AdicSpace.IsLocallyHuberStandard.of_isPullback_of_locallyOfWeaklyFiniteType`: permanence
  of local sheafiness and finiteness properties on fibre products.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Proposition 3.7.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, Proposition 1.2.2 and Corollary 1.2.3.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.6, Definition 8.54,
  Theorem 8.56, and Remark 8.57(1).
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace TauCeti.AdicSpace

open Huber PreAdicSpace ValuationSpectrum

universe u

/-! ### Affinoid chart and completed-tensor pullback helpers -/

section Helpers

/-- Transfer sheafiness from an open adic subspace `S.restrict V` across a `PreAdicSpace` chart
isomorphism `S.obj.restrict V ≅ Spa(A, A⁺)`. -/
private theorem isSheaf_of_restrict_iso {S : AdicSpace.{u}} {V : Opens S.obj}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {SA : Pair A} (PA : PairOfDefinition A) (hPA : PA.ringOfDefinition ≤ SA.plus)
    (eV₀ : S.obj.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace PA SA.plus SA.isRingOfIntegralElements.isPowerBounded_of_mem
        hPA) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa SA.plus))
      (presentationLimitPresheaf PA SA.plus) :=
  (isSheafy_presentationLimitPreAdicSpace_iff PA SA.plus _ hPA).mp
    (ObjectProperty.prop_of_iso isSheafy eV₀
      (isSheafy_restrict V.isOpenEmbedding S.property.isSheafy))

/-- Lift a `PreAdicSpace` affinoid chart equation for `f : X ⟶ S` to an `AdicSpace` factorization
through `comapOfPresentation`. -/
private theorem ofRestrict_comp_eq_comapOfPresentation {X S : AdicSpace.{u}} {f : X ⟶ S}
    {U : Opens X.obj} {V : Opens S.obj}
    {A C : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    {SA : Pair A} {UC : Pair C} (PA : PairOfDefinition A) (PC : PairOfDefinition C)
    (hPA : PA.ringOfDefinition ≤ SA.plus) (hPC : PC.ringOfDefinition ≤ UC.plus)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa SA.plus))
      (presentationLimitPresheaf PA SA.plus))
    (hsheafC : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa UC.plus))
      (presentationLimitPresheaf PC UC.plus))
    (φ : Pair.Hom SA UC)
    (eU₀ : X.obj.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace PC UC.plus UC.isRingOfIntegralElements.isPowerBounded_of_mem
        hPC)
    (eV₀ : S.obj.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace PA SA.plus SA.isRingOfIntegralElements.isPowerBounded_of_mem
        hPA)
    (hfac : X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom =
      eU₀.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus SA.isRingOfIntegralElements.isPowerBounded_of_mem
        UC.isRingOfIntegralElements.isPowerBounded_of_mem hPA hPC hsheafC ≫
        eV₀.inv ≫ S.obj.ofRestrict V.isOpenEmbedding) :
    X.ofRestrict U ≫ f =
      (ObjectProperty.isoMk PreAdicSpace.isAdic eU₀).hom ≫
        comapOfPresentation SA PA hPA hsheafA UC PC hPC hsheafC φ ≫
        (ObjectProperty.isoMk PreAdicSpace.isAdic eV₀).inv ≫ S.ofRestrict V := by
  ext1
  rw [ObjectProperty.FullSubcategory.comp_hom, ofRestrict_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.isoMk_hom, ObjectProperty.isoMk_inv,
    ofRestrict_hom, comapOfPresentation_eq_homMk_presentationLimitPreAdicSpaceComap,
    ObjectProperty.homMk_hom]
  exact hfac

/-- Project an `AdicSpace` factorization through `comapOfPresentation` back to the underlying
`PreAdicSpace` chart equation consumed by `chartLocally`. -/
private theorem ofRestrict_comp_hom_of_comapOfPresentation {Z Y : AdicSpace.{u}} {q : Z ⟶ Y}
    {O : Opens Z.obj} {W : Opens Y.obj}
    {B E : Type u}
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    [CommRing E] [TopologicalSpace E] [IsTopologicalRing E] [IsHuberRing E]
    {TB : Pair B} {WE : Pair E} (PB : PairOfDefinition B) (PE : PairOfDefinition E)
    (hPB : PB.ringOfDefinition ≤ TB.plus) (hPE : PE.ringOfDefinition ≤ WE.plus)
    (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa TB.plus))
      (presentationLimitPresheaf PB TB.plus))
    (hsheafE : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa WE.plus))
      (presentationLimitPresheaf PE WE.plus))
    (ψ : Pair.Hom TB WE)
    (eO : Z.restrict O ≅ ofPresentation WE PE hPE hsheafE)
    (eW₀ : Y.obj.restrict W.isOpenEmbedding ≅
      presentationLimitPreAdicSpace PB TB.plus TB.isRingOfIntegralElements.isPowerBounded_of_mem
        hPB)
    (heO : Z.ofRestrict O ≫ q =
      eO.hom ≫ comapOfPresentation TB PB hPB hsheafB WE PE hPE hsheafE ψ ≫
        (ObjectProperty.isoMk PreAdicSpace.isAdic eW₀).inv ≫ Y.ofRestrict W) :
    Z.obj.ofRestrict O.isOpenEmbedding ≫ q.hom =
      ((ObjectProperty.ι PreAdicSpace.isAdic).mapIso eO).hom ≫
        presentationLimitPreAdicSpaceComap ψ.toRingHom ψ.continuous_toRingHom ψ.map_mem_plus
          TB.isRingOfIntegralElements.isPowerBounded_of_mem
          WE.isRingOfIntegralElements.isPowerBounded_of_mem hPB hPE hsheafE ≫
        eW₀.inv ≫ Y.obj.ofRestrict W.isOpenEmbedding := by
  have h := congrArg InducedCategory.Hom.hom heO
  rwa [ObjectProperty.FullSubcategory.comp_hom, ofRestrict_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.isoMk_inv, ofRestrict_hom,
    comapOfPresentation_eq_homMk_presentationLimitPreAdicSpaceComap,
    ObjectProperty.homMk_hom] at h

/-- Core affinoid pullback construction: given `φ : (A, A⁺) → (C, C⁺)` with `A → C` topologically of
finite type and an adic morphism `g₀ : Spa(B, B⁺) ⟶ Spa(A, A⁺)` with `B` stably sheafy (all three
rings complete and Hausdorff), `g₀` comes from an adic Huber-pair morphism `ψ : (A, A⁺) → (B, B⁺)`
and `Spa((C, C⁺) ⊗̂_A (B, B⁺))` forms a pullback square of `(Spa(φ), g₀)` in `AdicSpace`. -/
private theorem exists_completedTensor_isPullback_of_isStablySheafyRing
    {A B C : Type u}
    [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T2Space A] [IsHuberRing A]
    [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T2Space B] [IsHuberRing B]
    [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T2Space C] [IsHuberRing C]
    {SA : Pair A} {TB : Pair B} {UC : Pair C}
    (PA : PairOfDefinition A) (PB : PairOfDefinition B) (PC : PairOfDefinition C)
    (hPA : PA.ringOfDefinition ≤ SA.plus) (hPB : PB.ringOfDefinition ≤ TB.plus)
    (hPC : PC.ringOfDefinition ≤ UC.plus)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa SA.plus))
      (presentationLimitPresheaf PA SA.plus))
    (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa TB.plus))
      (presentationLimitPresheaf PB TB.plus))
    (hsheafC : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa UC.plus))
      (presentationLimitPresheaf PC UC.plus))
    (hB : IsStablySheafyRing.{u, u} B)
    (φ : Pair.Hom SA UC) (hφ : IsTopologicallyFiniteType φ.toRingHom)
    (g₀ : ofPresentation TB PB hPB hsheafB ⟶ ofPresentation SA PA hPA hsheafA)
    (hg₀ : IsAdic g₀) :
    ∃ (_ : Algebra A C) (_ : Algebra A B)
      (_ : IsAdicHom (algebraMap A C)) (_ : IsAdicHom (algebraMap A B))
      (_ : SA.plus ≤ TB.plus.comap (algebraMap A B))
      (_ : φ.toRingHom = algebraMap A C)
      (PE : PairOfDefinition (CompletedTensor A C B))
      (hPE : PE.ringOfDefinition ≤ (UC.completedTensor A TB).plus)
      (hsheafE : Presheaf.IsSheaf
        (Opens.grothendieckTopology ↥(spa (UC.completedTensor A TB).plus))
        (presentationLimitPresheaf PE (UC.completedTensor A TB).plus)),
      IsPullback
        (comapOfPresentation UC PC hPC hsheafC (UC.completedTensor A TB) PE hPE hsheafE
          (Pair.completedTensor.inl A UC TB))
        (comapOfPresentation TB PB hPB hsheafB (UC.completedTensor A TB) PE hPE hsheafE
          (Pair.completedTensor.inr A UC TB))
        (comapOfPresentation SA PA hPA hsheafA UC PC hPC hsheafC φ)
        g₀ := by
  let ψ : Pair.Hom SA TB := ofPresentationHomEquiv SA PA hPA hsheafA TB PB hPB hsheafB g₀
  have hψeq : comapOfPresentation SA PA hPA hsheafA TB PB hPB hsheafB ψ = g₀ := by
    rw [← ofPresentationHomEquiv_symm_apply]
    exact (ofPresentationHomEquiv SA PA hPA hsheafA TB PB hPB hsheafB).symm_apply_apply g₀
  have hψadic : IsAdicHom ψ.toRingHom :=
    (isAdic_comapOfPresentation_iff SA PA hPA hsheafA TB PB hPB hsheafB ψ).mp (hψeq ▸ hg₀)
  let _ : Algebra A C := φ.toRingHom.toAlgebra
  let _ : Algebra A B := ψ.toRingHom.toAlgebra
  have hAC : algebraMap A C = φ.toRingHom := RingHom.algebraMap_toAlgebra φ.toRingHom
  have hAB : algebraMap A B = ψ.toRingHom := RingHom.algebraMap_toAlgebra ψ.toRingHom
  have hACadic : IsAdicHom (algebraMap A C) := hAC ▸ hφ.isAdicHom
  have hABadic : IsAdicHom (algebraMap A B) := hAB ▸ hψadic
  have hsheafE_all : IsSheafyForEveryPresentation (UC.completedTensor A TB).plus :=
    isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_right UC TB hB (hAC ▸ hφ)
  obtain ⟨PE, hPE, hsheafE⟩ := hsheafE_all.exists_compatible_isSheaf
  have hplus : SA.plus ≤ TB.plus.comap (algebraMap A B) := fun a ha ↦ by
    rw [Subring.mem_comap, hAB]
    exact ψ.map_mem_plus a ha
  refine ⟨inferInstance, inferInstance, hACadic, hABadic, hplus, hAC.symm, PE, hPE, hsheafE, ?_⟩
  rw [← hψeq]
  exact isPullback_ofPresentation_completedTensor PA PC PB PE hPA hPC hPB hPE
    hsheafA hsheafC hsheafB hsheafE φ ψ hAC.symm hAB.symm

end Helpers

/-! ### Existence of fibre products of adic spaces -/

section Existence

/-- Local existence step: the fibre product of an explicit complete Hausdorff affinoid morphism
`Spa(C, C⁺) ⟶ Spa(A, A⁺)` (with `A → C` topologically of finite type) along any adic morphism
`g : Y ⟶ Spa(A, A⁺)` out of a locally stably sheafy adic space `Y` exists in `AdicSpace`. -/
private theorem hasPullback_comapOfPresentation_of_isLocallyStablySheafy
    {A C : Type u}
    [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T2Space A] [IsHuberRing A]
    [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T2Space C] [IsHuberRing C]
    {SA : Pair A} {UC : Pair C} (PA : PairOfDefinition A) (PC : PairOfDefinition C)
    (hPA : PA.ringOfDefinition ≤ SA.plus) (hPC : PC.ringOfDefinition ≤ UC.plus)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa SA.plus))
      (presentationLimitPresheaf PA SA.plus))
    (hsheafC : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa UC.plus))
      (presentationLimitPresheaf PC UC.plus))
    (φ : Pair.Hom SA UC) (hφ : IsTopologicallyFiniteType φ.toRingHom)
    {Y : AdicSpace.{u}} (g : Y ⟶ ofPresentation SA PA hPA hsheafA)
    (hg : IsAdic g) (hY : Y.IsLocallyStablySheafy) :
    HasPullback (comapOfPresentation SA PA hPA hsheafA UC PC hPC hsheafC φ) g := by
  let f₀ := comapOfPresentation SA PA hPA hsheafA UC PC hPC hsheafC φ
  suffices HasPullback g f₀ from hasPullback_symmetry g f₀
  choose W hW hyW using isLocallyStablySheafy_iff.mp hY
  have hpb (y : Y.obj) : HasPullback (Y.ofRestrict (W y) ≫ g) f₀ := by
    obtain ⟨B, _, _, _, _, _, _, _, hB, TB, PB, hPB, ⟨eW₀⟩⟩ :=
      (isStablySheafyAffinoid_iff _).mp ((mem_propOpens_iff _).mp (hW y))
    have hsheafB :=
      isSheaf_presentationLimitPresheaf_of_isSheafyRing PB TB.isRingOfIntegralElements hPB
        hB.isSheafyRing
    let eW : Y.restrict (W y) ≅ ofPresentation TB PB hPB hsheafB :=
      ObjectProperty.isoMk PreAdicSpace.isAdic eW₀
    let g_y : ofPresentation TB PB hPB hsheafB ⟶ ofPresentation SA PA hPA hsheafA :=
      eW.inv ≫ Y.ofRestrict (W y) ≫ g
    have hg_y : IsAdic g_y :=
      IsAdic.isMultiplicative.comp_mem eW.inv _ (MorphismProperty.of_isIso _ _)
        (IsAdic.isMultiplicative.comp_mem _ _ (IsAdic.of_isOpenImmersion _) hg)
    obtain ⟨_, _, _, _, _, _, _, _, _, hpull₀⟩ :=
      exists_completedTensor_isPullback_of_isStablySheafyRing PA PB PC hPA hPB hPC
        hsheafA hsheafB hsheafC hB φ hφ g_y hg_y
    have heq : eW.hom ≫ g_y = Y.ofRestrict (W y) ≫ g := by
      simp only [g_y, Iso.hom_inv_id_assoc]
    rw [← heq]
    exact (HasPullback.comp_left_left_iff_of_isIso eW.hom).mpr hpull₀.flip.hasPullback
  exact hasPullback_of_cover g f₀ (fun y ↦ Y.ofRestrict (W y))
    fun y ↦ ⟨y, ⟨y, hyW y⟩, ofRestrict_base_apply Y (W y) ⟨y, hyW y⟩⟩

variable {X Y S : AdicSpace.{u}}

/-- **Existence of fibre products of adic spaces in the adic case** (Huber 1994, Proposition 3.7;
Huber 1996, Proposition 1.2.2(b); Wedhorn, Theorem 8.56): if `f : X ⟶ S` is locally of weakly finite
type, `g : Y ⟶ S` is adic, and `Y` is locally stably sheafy, then the fibre product `X ×_S Y` exists
in the category `AdicSpace`. -/
theorem hasPullback_of_locallyOfWeaklyFiniteType_left {f : X ⟶ S} {g : Y ⟶ S}
    (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g) (hY : Y.IsLocallyStablySheafy) :
    HasPullback f g := by
  choose U hxU V _ rest using fun x : X.obj ↦ hf.exists_complete_chart x
  have hpb (x : X.obj) : HasPullback (X.ofRestrict (U x) ≫ f) g := by
    obtain ⟨A, _, _, _, _, _, _, _, SA, PA, hPA, C, _, _, _, _, _, _, _, UC, PC, hPC,
      φ, hφ, hsheafC, eU₀, eV₀, hfac⟩ := rest x
    have hsheafA := isSheaf_of_restrict_iso PA hPA eV₀
    let eU : X.restrict (U x) ≅ ofPresentation UC PC hPC hsheafC :=
      ObjectProperty.isoMk PreAdicSpace.isAdic eU₀
    let eV : S.restrict (V x) ≅ ofPresentation SA PA hPA hsheafA :=
      ObjectProperty.isoMk PreAdicSpace.isAdic eV₀
    let f₀ := comapOfPresentation SA PA hPA hsheafA UC PC hPC hsheafC φ
    let f_x : X.restrict (U x) ⟶ S.restrict (V x) := eU.hom ≫ f₀ ≫ eV.inv
    have hfac' : X.ofRestrict (U x) ≫ f = f_x ≫ S.ofRestrict (V x) := by
      simpa only [f_x, f₀, eU, eV, Category.assoc] using
        ofRestrict_comp_eq_comapOfPresentation PA PC hPA hPC hsheafA hsheafC φ eU₀ eV₀ hfac
    let Y' := Y.restrict ((Opens.map g.hom.base).obj (V x))
    let g_x : Y' ⟶ S.restrict (V x) := restrictPreimage g (V x)
    have hY' : Y'.IsLocallyStablySheafy := hY.of_isOpenImmersion (Y.ofRestrict _)
    have hg_x : IsAdic g_x := by
      refine IsAdic.of_comp (g := S.ofRestrict (V x)) ?_
      rw [restrictPreimage_ofRestrict]
      exact IsAdic.isMultiplicative.comp_mem _ _ (IsAdic.of_isOpenImmersion _) hg
    have hg_x_eV : IsAdic (g_x ≫ eV.hom) :=
      IsAdic.isMultiplicative.comp_mem _ _ hg_x (MorphismProperty.of_isIso _ _)
    have hpb₀ : HasPullback f₀ (g_x ≫ eV.hom) :=
      hasPullback_comapOfPresentation_of_isLocallyStablySheafy PA PC hPA hPC hsheafA hsheafC φ hφ
        (g_x ≫ eV.hom) hg_x_eV hY'
    have hpb₁ : HasPullback (f₀ ≫ eV.inv) g_x := by
      rw [HasPullback.comp_left_right_iff_of_isIso eV.inv]
      simpa using hpb₀
    have hpb₂ : HasPullback f_x g_x :=
      (HasPullback.comp_left_left_iff_of_isIso eU.hom).mpr hpb₁
    rw [hfac']
    exact ((IsPullback.of_hasPullback f_x g_x).paste_vert
      (isPullback_restrictPreimage g (V x))).hasPullback
  exact hasPullback_of_cover f g (fun x ↦ X.ofRestrict (U x))
    fun x ↦ ⟨x, ⟨x, hxU x⟩, ofRestrict_base_apply X (U x) ⟨x, hxU x⟩⟩

/-- **Symmetric form of `hasPullback_of_locallyOfWeaklyFiniteType_left`**: if `f : X ⟶ S` is adic,
`g : Y ⟶ S` is locally of weakly finite type, and `X` is locally stably sheafy, then `X ×_S Y`
exists in `AdicSpace`. -/
theorem hasPullback_of_locallyOfWeaklyFiniteType_right {f : X ⟶ S} {g : Y ⟶ S}
    (hf : IsAdic f) (hg : LocallyOfWeaklyFiniteType g) (hX : X.IsLocallyStablySheafy) :
    HasPullback f g :=
  have := hasPullback_of_locallyOfWeaklyFiniteType_left hg hf hX
  hasPullback_symmetry g f

/-- Existence of `X ×_S Y` when `f` is locally of +weakly finite type, `g` is adic, and `Y` is
locally stably sheafy. -/
theorem hasPullback_of_locallyOfPlusWeaklyFiniteType_left {f : X ⟶ S} {g : Y ⟶ S}
    (hf : LocallyOfPlusWeaklyFiniteType f) (hg : IsAdic g) (hY : Y.IsLocallyStablySheafy) :
    HasPullback f g :=
  hasPullback_of_locallyOfWeaklyFiniteType_left hf.locallyOfWeaklyFiniteType hg hY

/-- Existence of `X ×_S Y` when `f` is adic, `g` is locally of +weakly finite type, and `X` is
locally stably sheafy. -/
theorem hasPullback_of_locallyOfPlusWeaklyFiniteType_right {f : X ⟶ S} {g : Y ⟶ S}
    (hf : IsAdic f) (hg : LocallyOfPlusWeaklyFiniteType g) (hX : X.IsLocallyStablySheafy) :
    HasPullback f g :=
  hasPullback_of_locallyOfWeaklyFiniteType_right hf hg.locallyOfWeaklyFiniteType hX

/-- Existence of `X ×_S Y` when `f` is locally of finite type, `g` is adic, and `Y` is locally
stably sheafy. -/
theorem hasPullback_of_locallyOfFiniteType_left {f : X ⟶ S} {g : Y ⟶ S}
    (hf : PreAdicSpace.LocallyOfFiniteType f.hom) (hg : IsAdic g) (hY : Y.IsLocallyStablySheafy) :
    HasPullback f g :=
  hasPullback_of_locallyOfWeaklyFiniteType_left hf.locallyOfWeaklyFiniteType hg hY

/-- Existence of `X ×_S Y` when `f` is adic, `g` is locally of finite type, and `X` is locally
stably sheafy. -/
theorem hasPullback_of_locallyOfFiniteType_right {f : X ⟶ S} {g : Y ⟶ S}
    (hf : IsAdic f) (hg : PreAdicSpace.LocallyOfFiniteType g.hom) (hX : X.IsLocallyStablySheafy) :
    HasPullback f g :=
  hasPullback_of_locallyOfWeaklyFiniteType_right hf hg.locallyOfWeaklyFiniteType hX

/-- **Existence of fibre products over an analytic base**: over an analytic adic space `S`, every
morphism `g : Y ⟶ S` is automatically adic (`IsAdic.of_isAnalytic`), so `X ×_S Y` exists whenever
`f : X ⟶ S` is locally of weakly finite type and `Y` is locally stably sheafy. -/
theorem hasPullback_of_locallyOfWeaklyFiniteType_left_of_isAnalytic {f : X ⟶ S} (g : Y ⟶ S)
    (hf : LocallyOfWeaklyFiniteType f) (hS : S.IsAnalytic) (hY : Y.IsLocallyStablySheafy) :
    HasPullback f g :=
  hasPullback_of_locallyOfWeaklyFiniteType_left hf (.of_isAnalytic g hS) hY

/-- Symmetric form of `hasPullback_of_locallyOfWeaklyFiniteType_left_of_isAnalytic`. -/
theorem hasPullback_of_locallyOfWeaklyFiniteType_right_of_isAnalytic (f : X ⟶ S) {g : Y ⟶ S}
    (hg : LocallyOfWeaklyFiniteType g) (hS : S.IsAnalytic) (hX : X.IsLocallyStablySheafy) :
    HasPullback f g :=
  hasPullback_of_locallyOfWeaklyFiniteType_right (.of_isAnalytic f hS) hg hX

/-- **Huber 1996, Proposition 1.2.2(b) over locally noetherian analytic spaces**: if
`f : X ⟶ S` is locally of weakly finite type, `g : Y ⟶ S` is adic, and `Y` is locally noetherian
analytic, then `X ×_S Y` exists in `AdicSpace`. -/
theorem hasPullback_of_locallyOfWeaklyFiniteType_left_of_isLocallyNoetherianAnalytic
    {f : X ⟶ S} {g : Y ⟶ S} (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g)
    (hY : Y.IsLocallyNoetherianAnalytic) : HasPullback f g :=
  hasPullback_of_locallyOfWeaklyFiniteType_left hf hg hY.isLocallyStablySheafy

/-- Symmetric form of
`hasPullback_of_locallyOfWeaklyFiniteType_left_of_isLocallyNoetherianAnalytic`. -/
theorem hasPullback_of_locallyOfWeaklyFiniteType_right_of_isLocallyNoetherianAnalytic
    {f : X ⟶ S} {g : Y ⟶ S} (hf : IsAdic f) (hg : LocallyOfWeaklyFiniteType g)
    (hX : X.IsLocallyNoetherianAnalytic) : HasPullback f g :=
  hasPullback_of_locallyOfWeaklyFiniteType_right hf hg hX.isLocallyStablySheafy

end Existence

/-! ### Local chart identification on pullback squares and base-change stability -/

section BaseChange

variable {Z X Y S : AdicSpace.{u}}

/-- Local completed-tensor chart data around a point `z` of a pullback `Z` in `AdicSpace`. -/
private structure CompletedTensorChart
    (Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop)
    (p : Z ⟶ X) (q : Z ⟶ Y) (z : Z.obj) : Type (u + 1) where
  O : Opens Z.obj
  hzO : z ∈ O
  U : Opens X.obj
  hOU : O ≤ (Opens.map p.hom.base).obj U
  W : Opens Y.obj
  hOW : O ≤ (Opens.map q.hom.base).obj W
  A : Type u
  B : Type u
  C : Type u
  [commRingA : CommRing A]
  [uniformSpaceA : UniformSpace A]
  [isUniformAddGroupA : IsUniformAddGroup A]
  [isTopologicalRingA : IsTopologicalRing A]
  [completeSpaceA : CompleteSpace A]
  [t2SpaceA : T2Space A]
  [isHuberRingA : IsHuberRing A]
  [commRingB : CommRing B]
  [uniformSpaceB : UniformSpace B]
  [isUniformAddGroupB : IsUniformAddGroup B]
  [isTopologicalRingB : IsTopologicalRing B]
  [completeSpaceB : CompleteSpace B]
  [t2SpaceB : T2Space B]
  [isHuberRingB : IsHuberRing B]
  [commRingC : CommRing C]
  [uniformSpaceC : UniformSpace C]
  [isUniformAddGroupC : IsUniformAddGroup C]
  [isTopologicalRingC : IsTopologicalRing C]
  [completeSpaceC : CompleteSpace C]
  [t2SpaceC : T2Space C]
  [isHuberRingC : IsHuberRing C]
  [algebraAC : Algebra A C]
  [algebraAB : Algebra A B]
  [isAdicHomAC : IsAdicHom (algebraMap A C)]
  [isAdicHomAB : IsAdicHom (algebraMap A B)]
  SA : Pair A
  TB : Pair B
  PB : PairOfDefinition B
  hPB : PB.ringOfDefinition ≤ TB.plus
  UC : Pair C
  PC : PairOfDefinition C
  hPC : PC.ringOfDefinition ≤ UC.plus
  φ : Pair.Hom SA UC
  hφQ : Q φ
  hplus : SA.plus ≤ TB.plus.comap (algebraMap A B)
  hφA : φ.toRingHom = algebraMap A C
  PE : PairOfDefinition (CompletedTensor A C B)
  hPE : PE.ringOfDefinition ≤ (UC.completedTensor A TB).plus
  hsheafE : Presheaf.IsSheaf
    (Opens.grothendieckTopology ↥(spa (UC.completedTensor A TB).plus))
    (presentationLimitPresheaf PE (UC.completedTensor A TB).plus)
  eO : Z.obj.restrict O.isOpenEmbedding ≅
    presentationLimitPreAdicSpace PE (UC.completedTensor A TB).plus
      (UC.completedTensor A TB).isRingOfIntegralElements.isPowerBounded_of_mem hPE
  eU₀ : X.obj.restrict U.isOpenEmbedding ≅
    presentationLimitPreAdicSpace PC UC.plus
      UC.isRingOfIntegralElements.isPowerBounded_of_mem hPC
  eW₀ : Y.obj.restrict W.isOpenEmbedding ≅
    presentationLimitPreAdicSpace PB TB.plus
      TB.isRingOfIntegralElements.isPowerBounded_of_mem hPB
  hfac_q : Z.obj.ofRestrict O.isOpenEmbedding ≫ q.hom =
    eO.hom ≫ presentationLimitPreAdicSpaceComap
      (Pair.completedTensor.inr A UC TB).toRingHom
      (Pair.completedTensor.inr A UC TB).continuous_toRingHom
      (Pair.completedTensor.inr A UC TB).map_mem_plus
      TB.isRingOfIntegralElements.isPowerBounded_of_mem
      (UC.completedTensor A TB).isRingOfIntegralElements.isPowerBounded_of_mem hPB hPE
      hsheafE ≫ eW₀.inv ≫ Y.obj.ofRestrict W.isOpenEmbedding
  hfac_p : Z.obj.ofRestrict O.isOpenEmbedding ≫ p.hom =
    eO.hom ≫ presentationLimitPreAdicSpaceComap
      (Pair.completedTensor.inl A UC TB).toRingHom
      (Pair.completedTensor.inl A UC TB).continuous_toRingHom
      (Pair.completedTensor.inl A UC TB).map_mem_plus
      UC.isRingOfIntegralElements.isPowerBounded_of_mem
      (UC.completedTensor A TB).isRingOfIntegralElements.isPowerBounded_of_mem hPC hPE
      hsheafE ≫ eU₀.inv ≫ X.obj.ofRestrict U.isOpenEmbedding

attribute [local instance]
  CompletedTensorChart.commRingA CompletedTensorChart.uniformSpaceA
  CompletedTensorChart.isUniformAddGroupA CompletedTensorChart.isTopologicalRingA
  CompletedTensorChart.completeSpaceA CompletedTensorChart.t2SpaceA
  CompletedTensorChart.isHuberRingA
  CompletedTensorChart.commRingB CompletedTensorChart.uniformSpaceB
  CompletedTensorChart.isUniformAddGroupB CompletedTensorChart.isTopologicalRingB
  CompletedTensorChart.completeSpaceB CompletedTensorChart.t2SpaceB
  CompletedTensorChart.isHuberRingB
  CompletedTensorChart.commRingC CompletedTensorChart.uniformSpaceC
  CompletedTensorChart.isUniformAddGroupC CompletedTensorChart.isTopologicalRingC
  CompletedTensorChart.completeSpaceC CompletedTensorChart.t2SpaceC
  CompletedTensorChart.isHuberRingC
  CompletedTensorChart.algebraAC CompletedTensorChart.algebraAB
  CompletedTensorChart.isAdicHomAC CompletedTensorChart.isAdicHomAB

/-- Pointwise completed-tensor chart identification on a pullback square `IsPullback p q f g` in
`AdicSpace`: when `f` satisfies `chartLocally Q` (for a right-cancellative property `Q` implying
topological finite type on rings), `g` is adic, and `Y` is locally stably sheafy, every point `z` of
`Z` lies in an open `O = p⁻¹(U) ∩ q⁻¹(W)` isomorphic to `Spa((C, C⁺) ⊗̂_A (B, B⁺))` under which `q`
is induced by `Pair.completedTensor.inr` and `p` is induced by `Pair.completedTensor.inl`. -/
private theorem nonempty_completedTensorChart_of_isPullback
    (Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop)
    (hQtft : ∀ {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsHuberRing A] {SA : Pair A}
      {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
      [IsTopologicalRing C] [CompleteSpace C] [T2Space C] [IsHuberRing C] {UC : Pair C}
      {φ : Pair.Hom SA UC}, Q φ → IsTopologicallyFiniteType φ.toRingHom)
    (hQcomp : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {SA : Pair A}
      {A₁ : Type u} [CommRing A₁] [UniformSpace A₁] [IsUniformAddGroup A₁]
      [IsTopologicalRing A₁] [CompleteSpace A₁] [T2Space A₁] [IsHuberRing A₁] {SA₁ : Pair A₁}
      {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
      [IsTopologicalRing C] [CompleteSpace C] [T2Space C] [IsHuberRing C] {UC : Pair C}
      {ιA : Pair.Hom SA SA₁} {φ₁ : Pair.Hom SA₁ UC},
      Q (φ₁.comp ιA) → Q φ₁)
    {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hs : IsPullback p q f g) (hf : chartLocally Q f.hom)
    (hg : IsAdic g) (hY : Y.IsLocallyStablySheafy) (z : Z.obj) :
    Nonempty (CompletedTensorChart Q p q z) := by
  -- 1. Choose a complete Hausdorff chart `(U, V)` of `f` around `p(z)`.
  obtain ⟨U, hzpU, V, hUV, A, _, _, _, _, _, _, _, SA, PA, hPA,
    C, _, _, _, _, _, _, _, UC, PC, hPC, φ, hφQ, hsheafC, eU₀, eV₀, hfac_f⟩ :=
    exists_complete_chart_of_chartLocally Q hQcomp hf (p.hom.base z)
  have hφtft : IsTopologicallyFiniteType φ.toRingHom := hQtft hφQ
  have hsheafA := isSheaf_of_restrict_iso PA hPA eV₀
  -- 2. Since `g(q(z)) = f(p(z)) ∈ V`, pick a stably sheafy affinoid `W ⊆ g⁻¹(V)` at `q(z)`.
  have hzqV : q.hom.base z ∈ (Opens.map g.hom.base).obj V := by
    have hzw := congrArg (fun k : Z ⟶ S ↦ k.hom.base z) hs.w
    simp only [ObjectProperty.FullSubcategory.comp_hom, PreAdicSpace.comp_base, TopCat.coe_comp,
      Function.comp_apply] at hzw
    exact Opens.mem_map.mpr (hzw ▸ hUV hzpU)
  obtain ⟨W, hWss, hzqW, hWV⟩ :=
    Opens.isBasis_iff_nbhd.mp hY.isBasis_stablySheafyAffinoidOpens hzqV
  obtain ⟨B, _, _, _, _, _, _, _, hB, TB, PB, hPB, ⟨eW₀⟩⟩ :=
    (isStablySheafyAffinoid_iff _).mp ((mem_propOpens_iff _).mp hWss)
  have hsheafB :=
    isSheaf_presentationLimitPresheaf_of_isSheafyRing PB TB.isRingOfIntegralElements hPB
      hB.isSheafyRing
  let eU : X.restrict U ≅ ofPresentation UC PC hPC hsheafC :=
    ObjectProperty.isoMk PreAdicSpace.isAdic eU₀
  let eV : S.restrict V ≅ ofPresentation SA PA hPA hsheafA :=
    ObjectProperty.isoMk PreAdicSpace.isAdic eV₀
  let eW : Y.restrict W ≅ ofPresentation TB PB hPB hsheafB :=
    ObjectProperty.isoMk PreAdicSpace.isAdic eW₀
  -- 3. Form the completed tensor product `(C, C⁺) ⊗̂_A (B, B⁺)` over `(U, W, V)`.
  let g_W : Y.restrict W ⟶ S.restrict V := liftRestrict g hWV
  have hg_W : IsAdic g_W := by
    refine IsAdic.of_comp (g := S.ofRestrict V) ?_
    rw [liftRestrict_ofRestrict]
    exact IsAdic.isMultiplicative.comp_mem _ _ (IsAdic.of_isOpenImmersion _) hg
  let g₀ : ofPresentation TB PB hPB hsheafB ⟶ ofPresentation SA PA hPA hsheafA :=
    eW.inv ≫ g_W ≫ eV.hom
  have hg₀ : IsAdic g₀ :=
    IsAdic.isMultiplicative.comp_mem _ _ (MorphismProperty.of_isIso _ _)
      (IsAdic.isMultiplicative.comp_mem _ _ hg_W (MorphismProperty.of_isIso _ _))
  obtain ⟨_, _, _, _, hplus, hφA, PE, hPE, hsheafE, hpull₀⟩ :=
    exists_completedTensor_isPullback_of_isStablySheafyRing PA PB PC hPA hPB hPC
      hsheafA hsheafB hsheafC hB φ hφtft g₀ hg₀
  let WE := UC.completedTensor A TB
  let πC :=
    comapOfPresentation UC PC hPC hsheafC WE PE hPE hsheafE (Pair.completedTensor.inl A UC TB)
  let πB :=
    comapOfPresentation TB PB hPB hsheafB WE PE hPE hsheafE (Pair.completedTensor.inr A UC TB)
  let f₀ := comapOfPresentation SA PA hPA hsheafA UC PC hPC hsheafC φ
  have hpull₁ : IsPullback (πC ≫ eU.inv) (πB ≫ eW.inv)
      (eU.hom ≫ f₀ ≫ eV.inv) (eW.hom ≫ g₀ ≫ eV.inv) :=
    hpull₀.of_iso' (Iso.refl _) eU eW eV
      (by simp [πC, WE]) (by simp [πB, WE]) (by simp [f₀]) (by simp)
  have hfac_f' : eU.hom ≫ f₀ ≫ eV.inv ≫ S.ofRestrict V = X.ofRestrict U ≫ f :=
    (ofRestrict_comp_eq_comapOfPresentation PA PC hPA hPC hsheafA hsheafC φ eU₀ eV₀ hfac_f).symm
  have hg_W_fac : g_W ≫ S.ofRestrict V = Y.ofRestrict W ≫ g :=
    liftRestrict_ofRestrict g hWV
  have hfac_g' : eW.hom ≫ g₀ ≫ eV.inv ≫ S.ofRestrict V = Y.ofRestrict W ≫ g := by
    dsimp only [g₀]
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, hg_W_fac]
  have hpull_aff : IsPullback (πC ≫ eU.inv) (πB ≫ eW.inv)
      (X.ofRestrict U ≫ f) (Y.ofRestrict W ≫ g) := by
    have hbot : IsPullback (eW.hom ≫ g₀ ≫ eV.inv) (𝟙 _) (S.ofRestrict V) (Y.ofRestrict W ≫ g) :=
      IsPullback.of_vert_isIso_mono
        ⟨by simpa only [Category.id_comp, Category.assoc] using hfac_g'⟩
    simpa only [Category.comp_id, Category.assoc, hfac_f'] using hpull₁.paste_vert hbot
  -- 4. Identify `Z.restrict O` (`O = p⁻¹(U) ∩ q⁻¹(W)`) with `Spa(WE)` via `isoIsPullback`.
  let O : Opens Z.obj := (Opens.map p.hom.base).obj U ⊓ (Opens.map q.hom.base).obj W
  have hzO : z ∈ O := ⟨hzpU, hzqW⟩
  have hpull_Z := isPullback_restrict_inf_of_isPullback hs U W
  let eO : Z.restrict O ≅ ofPresentation WE PE hPE hsheafE :=
    hpull_Z.isoIsPullback _ _ hpull_aff
  have heO_p : Z.ofRestrict O ≫ p = eO.hom ≫ πC ≫ eU.inv ≫ X.ofRestrict U := by
    have hcomp := congrArg (· ≫ X.ofRestrict U) (hpull_Z.isoIsPullback_hom_fst _ _ hpull_aff)
    simpa only [Category.assoc, liftRestrict_ofRestrict] using hcomp.symm
  have heO_q : Z.ofRestrict O ≫ q = eO.hom ≫ πB ≫ eW.inv ≫ Y.ofRestrict W := by
    have hcomp := congrArg (· ≫ Y.ofRestrict W) (hpull_Z.isoIsPullback_hom_snd _ _ hpull_aff)
    simpa only [Category.assoc, liftRestrict_ofRestrict] using hcomp.symm
  exact ⟨{
    O := O
    hzO := hzO
    U := U
    hOU := inf_le_left
    W := W
    hOW := inf_le_right
    A := A
    B := B
    C := C
    SA := SA
    TB := TB
    PB := PB
    hPB := hPB
    UC := UC
    PC := PC
    hPC := hPC
    φ := φ
    hφQ := hφQ
    hplus := hplus
    hφA := hφA
    PE := PE
    hPE := hPE
    hsheafE := hsheafE
    eO := (ObjectProperty.ι PreAdicSpace.isAdic).mapIso eO
    eU₀ := eU₀
    eW₀ := eW₀
    hfac_q := ofRestrict_comp_hom_of_comapOfPresentation PB PE hPB hPE hsheafB hsheafE _ eO eW₀
      heO_q
    hfac_p := ofRestrict_comp_hom_of_comapOfPresentation PC PE hPC hPE hsheafC hsheafE _ eO eU₀
      heO_p }⟩

/-- Parametric base-change stability of `chartLocally Q` along adic morphisms out of locally stably
sheafy adic spaces whenever `Q` implies topological finite type on rings, cancels on the right, and
passes to `Pair.completedTensor.inr`. -/
private theorem chartLocally_of_isPullback
    (Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop)
    (hQtft : ∀ {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsHuberRing A] {SA : Pair A}
      {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
      [IsTopologicalRing C] [CompleteSpace C] [T2Space C] [IsHuberRing C] {UC : Pair C}
      {φ : Pair.Hom SA UC}, Q φ → IsTopologicallyFiniteType φ.toRingHom)
    (hQcomp : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {SA : Pair A}
      {A₁ : Type u} [CommRing A₁] [UniformSpace A₁] [IsUniformAddGroup A₁]
      [IsTopologicalRing A₁] [CompleteSpace A₁] [T2Space A₁] [IsHuberRing A₁] {SA₁ : Pair A₁}
      {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
      [IsTopologicalRing C] [CompleteSpace C] [T2Space C] [IsHuberRing C] {UC : Pair C}
      {ιA : Pair.Hom SA SA₁} {φ₁ : Pair.Hom SA₁ UC},
      Q (φ₁.comp ιA) → Q φ₁)
    (hQbc : ∀ {A B C : Type u}
      [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
      [CompleteSpace A] [T2Space A] [IsHuberRing A]
      [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
      [CompleteSpace B] [T2Space B] [IsHuberRing B]
      [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
      [CompleteSpace C] [T2Space C] [IsHuberRing C]
      [Algebra A C] [Algebra A B] [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap A B)]
      {SA : Pair A} {UC : Pair C} {TB : Pair B} {φ : Pair.Hom SA UC},
      SA.plus ≤ TB.plus.comap (algebraMap A B) →
      Q φ → φ.toRingHom = algebraMap A C →
      Q (Pair.completedTensor.inr A UC TB))
    {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hs : IsPullback p q f g) (hf : chartLocally Q f.hom)
    (hg : IsAdic g) (hY : Y.IsLocallyStablySheafy) :
    chartLocally Q q.hom := by
  refine (chartLocally_iff q.hom).mpr fun z ↦ ?_
  obtain ⟨c⟩ := nonempty_completedTensorChart_of_isPullback Q hQtft hQcomp hs hf hg hY z
  exact ⟨c.O, c.hzO, c.W, c.hOW, c.B, inferInstance, inferInstance, inferInstance, inferInstance,
    c.TB, c.PB, c.hPB, CompletedTensor c.A c.C c.B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, c.UC.completedTensor c.A c.TB,
    c.PE, c.hPE, Pair.completedTensor.inr c.A c.UC c.TB, hQbc c.hplus c.hφQ c.hφA, c.hsheafE,
    c.eO, c.eW₀, c.hfac_q⟩

/-- **Base-change stability of `LocallyOfWeaklyFiniteType`** (Huber 1996, Corollary 1.2.3(iii)(a);
Wedhorn, Remark 8.57(1)): in any pullback square `IsPullback p q f g` in `AdicSpace`, if `f : X ⟶ S`
is locally of weakly finite type, `g : Y ⟶ S` is adic, and `Y` is locally stably sheafy, then
`q : Z ⟶ Y` is locally of weakly finite type. -/
theorem LocallyOfWeaklyFiniteType.of_isPullback {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hs : IsPullback p q f g) (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g)
    (hY : Y.IsLocallyStablySheafy) : LocallyOfWeaklyFiniteType q :=
  (locallyOfWeaklyFiniteType_iff_chartLocally q).mpr <|
    chartLocally_of_isPullback
      (fun φ ↦ IsTopologicallyFiniteType φ.toRingHom)
      (fun hφ ↦ hφ)
      (fun h ↦ Pair.Hom.isTopologicallyFiniteType_toRingHom_of_comp h)
      (fun _ hφ hφA ↦ by
        rw [Pair.completedTensor.toRingHom_inr]
        exact CompletedTensor.isTopologicallyFiniteType_inr (hφA ▸ hφ))
      hs ((locallyOfWeaklyFiniteType_iff_chartLocally f).mp hf) hg hY

/-- Symmetric form of `LocallyOfWeaklyFiniteType.of_isPullback`: if `g : Y ⟶ S` is locally of
weakly finite type, `f : X ⟶ S` is adic, and `X` is locally stably sheafy, then `p : Z ⟶ X` is
locally of weakly finite type. -/
theorem LocallyOfWeaklyFiniteType.of_isPullback_flip {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S}
    {g : Y ⟶ S} (hs : IsPullback p q f g) (hf : IsAdic f) (hg : LocallyOfWeaklyFiniteType g)
    (hX : X.IsLocallyStablySheafy) : LocallyOfWeaklyFiniteType p :=
  hg.of_isPullback hs.flip hf hX

/-- The second projection `pullback.snd f g : X ×_S Y ⟶ Y` is locally of weakly finite type when
`f` is locally of weakly finite type, `g` is adic, and `Y` is locally stably sheafy. -/
theorem LocallyOfWeaklyFiniteType.pullback_snd {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g) (hY : Y.IsLocallyStablySheafy) :
    LocallyOfWeaklyFiniteType (pullback.snd f g) :=
  hf.of_isPullback (.of_hasPullback f g) hg hY

/-- The first projection `pullback.fst f g : X ×_S Y ⟶ X` is locally of weakly finite type when
`f` is adic, `g` is locally of weakly finite type, and `X` is locally stably sheafy. -/
theorem LocallyOfWeaklyFiniteType.pullback_fst {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : IsAdic f) (hg : LocallyOfWeaklyFiniteType g) (hX : X.IsLocallyStablySheafy) :
    LocallyOfWeaklyFiniteType (pullback.fst f g) :=
  hg.of_isPullback_flip (.of_hasPullback f g) hf hX

/-- **Base-change stability of `LocallyOfPlusWeaklyFiniteType`** (Huber 1996,
Corollary 1.2.3(ii)): in any pullback square `IsPullback p q f g` in `AdicSpace`, if `f : X ⟶ S` is
locally of +weakly finite type, `g : Y ⟶ S` is adic, and `Y` is locally stably sheafy, then
`q : Z ⟶ Y` is locally of +weakly finite type. -/
theorem LocallyOfPlusWeaklyFiniteType.of_isPullback {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S}
    {g : Y ⟶ S} (hs : IsPullback p q f g) (hf : LocallyOfPlusWeaklyFiniteType f) (hg : IsAdic g)
    (hY : Y.IsLocallyStablySheafy) : LocallyOfPlusWeaklyFiniteType q :=
  (locallyOfPlusWeaklyFiniteType_iff_chartLocally q).mpr <|
    chartLocally_of_isPullback
      (fun φ ↦ φ.IsPlusWeaklyFiniteType)
      (fun hφ ↦ hφ.isTopologicallyFiniteType_toRingHom)
      (fun h ↦ h.of_comp)
      (fun hplus hφ hφA ↦ Pair.completedTensor.isPlusWeaklyFiniteType_inr _ hplus hφ hφA)
      hs ((locallyOfPlusWeaklyFiniteType_iff_chartLocally f).mp hf) hg hY

/-- Symmetric form of `LocallyOfPlusWeaklyFiniteType.of_isPullback`. -/
theorem LocallyOfPlusWeaklyFiniteType.of_isPullback_flip {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S}
    {g : Y ⟶ S} (hs : IsPullback p q f g) (hf : IsAdic f) (hg : LocallyOfPlusWeaklyFiniteType g)
    (hX : X.IsLocallyStablySheafy) : LocallyOfPlusWeaklyFiniteType p :=
  hg.of_isPullback hs.flip hf hX

/-- The second projection `pullback.snd f g : X ×_S Y ⟶ Y` is locally of +weakly finite type when
`f` is locally of +weakly finite type, `g` is adic, and `Y` is locally stably sheafy. -/
theorem LocallyOfPlusWeaklyFiniteType.pullback_snd {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : LocallyOfPlusWeaklyFiniteType f) (hg : IsAdic g) (hY : Y.IsLocallyStablySheafy) :
    LocallyOfPlusWeaklyFiniteType (pullback.snd f g) :=
  hf.of_isPullback (.of_hasPullback f g) hg hY

/-- The first projection `pullback.fst f g : X ×_S Y ⟶ X` is locally of +weakly finite type when
`f` is adic, `g` is locally of +weakly finite type, and `X` is locally stably sheafy. -/
theorem LocallyOfPlusWeaklyFiniteType.pullback_fst {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : IsAdic f) (hg : LocallyOfPlusWeaklyFiniteType g) (hX : X.IsLocallyStablySheafy) :
    LocallyOfPlusWeaklyFiniteType (pullback.fst f g) :=
  hg.of_isPullback_flip (.of_hasPullback f g) hf hX

/-- **Adic base-change stability of `LocallyOfFiniteType`** (Huber 1996, Corollary 1.2.3(i);
Wedhorn, Remark 8.57(1)): in any pullback square `IsPullback p q f g` in `AdicSpace`, if `f : X ⟶ S`
is locally of finite type, `g : Y ⟶ S` is adic, and `Y` is locally stably sheafy, then
`q : Z ⟶ Y` is locally of finite type. -/
theorem locallyOfFiniteType_of_isPullback {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hs : IsPullback p q f g) (hf : PreAdicSpace.LocallyOfFiniteType f.hom) (hg : IsAdic g)
    (hY : Y.IsLocallyStablySheafy) : PreAdicSpace.LocallyOfFiniteType q.hom :=
  (locallyOfFiniteType_iff q.hom).mpr <|
    chartLocally_of_isPullback
      (fun φ ↦ φ.IsTopologicallyFiniteType)
      (fun hφ ↦ hφ.isTopologicallyFiniteType_toRingHom)
      (fun h ↦ h.of_comp)
      (fun hplus hφ hφA ↦ Pair.completedTensor.isTopologicallyFiniteType_inr _ hplus hφ hφA)
      hs ((locallyOfFiniteType_iff f.hom).mp hf) hg hY

/-- Symmetric form of `locallyOfFiniteType_of_isPullback`. -/
theorem locallyOfFiniteType_of_isPullback_flip {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hs : IsPullback p q f g) (hf : IsAdic f) (hg : PreAdicSpace.LocallyOfFiniteType g.hom)
    (hX : X.IsLocallyStablySheafy) : PreAdicSpace.LocallyOfFiniteType p.hom :=
  locallyOfFiniteType_of_isPullback hs.flip hg hf hX

/-- The second projection `pullback.snd f g : X ×_S Y ⟶ Y` is locally of finite type when `f` is
locally of finite type, `g` is adic, and `Y` is locally stably sheafy. -/
theorem locallyOfFiniteType_pullback_snd {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : PreAdicSpace.LocallyOfFiniteType f.hom) (hg : IsAdic g) (hY : Y.IsLocallyStablySheafy) :
    PreAdicSpace.LocallyOfFiniteType (pullback.snd f g).hom :=
  locallyOfFiniteType_of_isPullback (.of_hasPullback f g) hf hg hY

/-- The first projection `pullback.fst f g : X ×_S Y ⟶ X` is locally of finite type when `f` is
adic, `g` is locally of finite type, and `X` is locally stably sheafy. -/
theorem locallyOfFiniteType_pullback_fst {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : IsAdic f) (hg : PreAdicSpace.LocallyOfFiniteType g.hom) (hX : X.IsLocallyStablySheafy) :
    PreAdicSpace.LocallyOfFiniteType (pullback.fst f g).hom :=
  locallyOfFiniteType_of_isPullback_flip (.of_hasPullback f g) hf hg hX

/-- **Base-change stability of `IsAdic` along morphisms locally of weakly finite type** (Huber 1994,
Proposition 3.7; Huber 1996, Corollary 1.2.3(iii)(a); Wedhorn, Remark 8.57(1)): in any pullback
square `IsPullback p q f g` in `AdicSpace`, if `f : X ⟶ S` is locally of weakly finite type,
`g : Y ⟶ S` is adic, and `Y` is locally stably sheafy, then `p : Z ⟶ X` is adic. -/
theorem IsAdic.of_isPullback_of_locallyOfWeaklyFiniteType {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S}
    {g : Y ⟶ S} (hs : IsPullback p q f g) (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g)
    (hY : Y.IsLocallyStablySheafy) : IsAdic p := by
  refine (isAdic_iff_chartLocally p).mpr <| (chartLocally_iff p.hom).mpr fun z ↦ ?_
  obtain ⟨c⟩ :=
    nonempty_completedTensorChart_of_isPullback
      (fun φ ↦ IsTopologicallyFiniteType φ.toRingHom)
      (fun hφ ↦ hφ)
      (fun h ↦ Pair.Hom.isTopologicallyFiniteType_toRingHom_of_comp h)
      hs ((locallyOfWeaklyFiniteType_iff_chartLocally f).mp hf) hg hY z
  have hinl : IsAdicHom (Pair.completedTensor.inl c.A c.UC c.TB).toRingHom := by
    rw [Pair.completedTensor.toRingHom_inl]
    exact CompletedTensor.isAdicHom_inl c.A c.C c.B
  exact ⟨c.O, c.hzO, c.U, c.hOU, c.C, inferInstance, inferInstance, inferInstance, inferInstance,
    c.UC, c.PC, c.hPC, CompletedTensor c.A c.C c.B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, c.UC.completedTensor c.A c.TB,
    c.PE, c.hPE, Pair.completedTensor.inl c.A c.UC c.TB, hinl, c.hsheafE, c.eO, c.eU₀, c.hfac_p⟩

/-- Symmetric form of `IsAdic.of_isPullback_of_locallyOfWeaklyFiniteType`: if `f : X ⟶ S` is adic,
`g : Y ⟶ S` is locally of weakly finite type, and `X` is locally stably sheafy, then `q : Z ⟶ Y` is
adic. -/
theorem IsAdic.of_isPullback_of_locallyOfWeaklyFiniteType_flip {p : Z ⟶ X} {q : Z ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (hs : IsPullback p q f g) (hf : IsAdic f)
    (hg : LocallyOfWeaklyFiniteType g) (hX : X.IsLocallyStablySheafy) : IsAdic q :=
  of_isPullback_of_locallyOfWeaklyFiniteType hs.flip hg hf hX

/-- The first projection `pullback.fst f g : X ×_S Y ⟶ X` is adic when `f` is locally of weakly
finite type, `g` is adic, and `Y` is locally stably sheafy. -/
theorem IsAdic.pullback_fst_of_locallyOfWeaklyFiniteType {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g) (hY : Y.IsLocallyStablySheafy) :
    IsAdic (pullback.fst f g) :=
  of_isPullback_of_locallyOfWeaklyFiniteType (.of_hasPullback f g) hf hg hY

/-- The second projection `pullback.snd f g : X ×_S Y ⟶ Y` is adic when `f` is adic, `g` is locally
of weakly finite type, and `X` is locally stably sheafy. -/
theorem IsAdic.pullback_snd_of_locallyOfWeaklyFiniteType {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : IsAdic f) (hg : LocallyOfWeaklyFiniteType g) (hX : X.IsLocallyStablySheafy) :
    IsAdic (pullback.snd f g) :=
  of_isPullback_of_locallyOfWeaklyFiniteType_flip (.of_hasPullback f g) hf hg hX

/-! ### Permanence of local sheafiness and finiteness properties on fibre products -/

/-- **Fibre products inherit local stable sheafiness**: in any pullback square `IsPullback p q f g`
in `AdicSpace` with `f` locally of weakly finite type, `g` adic, and `Y` locally stably sheafy, the
fibre product `Z` is locally stably sheafy. -/
theorem IsLocallyStablySheafy.of_isPullback_of_locallyOfWeaklyFiniteType
    {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (hs : IsPullback p q f g)
    (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g) (hY : Y.IsLocallyStablySheafy) :
    Z.IsLocallyStablySheafy :=
  hY.of_locallyOfWeaklyFiniteType (hf.of_isPullback hs hg hY)

/-- Symmetric form of `IsLocallyStablySheafy.of_isPullback_of_locallyOfWeaklyFiniteType`. -/
theorem IsLocallyStablySheafy.of_isPullback_of_locallyOfWeaklyFiniteType_flip
    {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (hs : IsPullback p q f g)
    (hf : IsAdic f) (hg : LocallyOfWeaklyFiniteType g) (hX : X.IsLocallyStablySheafy) :
    Z.IsLocallyStablySheafy :=
  hX.of_isPullback_of_locallyOfWeaklyFiniteType hs.flip hg hf

/-- `pullback f g` is locally stably sheafy when `f` is locally of weakly finite type, `g` is adic,
and `Y` is locally stably sheafy. -/
theorem isLocallyStablySheafy_pullback_of_locallyOfWeaklyFiniteType_left
    {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g] (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g)
    (hY : Y.IsLocallyStablySheafy) : (pullback f g).IsLocallyStablySheafy :=
  hY.of_isPullback_of_locallyOfWeaklyFiniteType (.of_hasPullback f g) hf hg

/-- `pullback f g` is locally stably sheafy when `f` is adic, `g` is locally of weakly finite type,
and `X` is locally stably sheafy. -/
theorem isLocallyStablySheafy_pullback_of_locallyOfWeaklyFiniteType_right
    {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g] (hf : IsAdic f) (hg : LocallyOfWeaklyFiniteType g)
    (hX : X.IsLocallyStablySheafy) : (pullback f g).IsLocallyStablySheafy :=
  hX.of_isPullback_of_locallyOfWeaklyFiniteType_flip (.of_hasPullback f g) hf hg

/-- **Fibre products over a locally noetherian factor inherit `IsLocallyNoetherian`** (Huber 1994,
Proposition 3.7): if `f` is locally of weakly finite type, `g` is adic, and `Y` is both locally
stably sheafy and locally noetherian, then `Z` is locally noetherian. -/
theorem IsLocallyNoetherian.of_isPullback_of_locallyOfWeaklyFiniteType
    {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (hs : IsPullback p q f g)
    (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g) (hYss : Y.IsLocallyStablySheafy)
    (hY : Y.IsLocallyNoetherian) : Z.IsLocallyNoetherian :=
  hY.of_locallyOfWeaklyFiniteType (hf.of_isPullback hs hg hYss)

/-- Symmetric form of `IsLocallyNoetherian.of_isPullback_of_locallyOfWeaklyFiniteType`. -/
theorem IsLocallyNoetherian.of_isPullback_of_locallyOfWeaklyFiniteType_flip
    {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (hs : IsPullback p q f g)
    (hf : IsAdic f) (hg : LocallyOfWeaklyFiniteType g) (hXss : X.IsLocallyStablySheafy)
    (hX : X.IsLocallyNoetherian) : Z.IsLocallyNoetherian :=
  hX.of_isPullback_of_locallyOfWeaklyFiniteType hs.flip hg hf hXss

/-- `pullback f g` is locally noetherian when `f` is locally of weakly finite type, `g` is adic, and
`Y` is locally stably sheafy and locally noetherian. -/
theorem isLocallyNoetherian_pullback_of_locallyOfWeaklyFiniteType_left
    {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g] (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g)
    (hYss : Y.IsLocallyStablySheafy) (hY : Y.IsLocallyNoetherian) :
    (pullback f g).IsLocallyNoetherian :=
  hY.of_isPullback_of_locallyOfWeaklyFiniteType (.of_hasPullback f g) hf hg hYss

/-- `pullback f g` is locally noetherian when `f` is adic, `g` is locally of weakly finite type, and
`X` is locally stably sheafy and locally noetherian. -/
theorem isLocallyNoetherian_pullback_of_locallyOfWeaklyFiniteType_right
    {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g] (hf : IsAdic f) (hg : LocallyOfWeaklyFiniteType g)
    (hXss : X.IsLocallyStablySheafy) (hX : X.IsLocallyNoetherian) :
    (pullback f g).IsLocallyNoetherian :=
  hX.of_isPullback_of_locallyOfWeaklyFiniteType_flip (.of_hasPullback f g) hf hg hXss

/-- **Fibre products over a factor locally of Huber's standing class inherit
`IsLocallyHuberStandard`**: if `f` is locally of weakly finite type, `g` is adic, and `Y` is locally
stably sheafy and locally of Huber's standing class, then `Z` is locally of Huber's standing class.
-/
theorem IsLocallyHuberStandard.of_isPullback_of_locallyOfWeaklyFiniteType
    {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (hs : IsPullback p q f g)
    (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g) (hYss : Y.IsLocallyStablySheafy)
    (hY : Y.IsLocallyHuberStandard) : Z.IsLocallyHuberStandard :=
  hY.of_locallyOfWeaklyFiniteType (hf.of_isPullback hs hg hYss)

/-- Symmetric form of `IsLocallyHuberStandard.of_isPullback_of_locallyOfWeaklyFiniteType`. -/
theorem IsLocallyHuberStandard.of_isPullback_of_locallyOfWeaklyFiniteType_flip
    {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (hs : IsPullback p q f g)
    (hf : IsAdic f) (hg : LocallyOfWeaklyFiniteType g) (hXss : X.IsLocallyStablySheafy)
    (hX : X.IsLocallyHuberStandard) : Z.IsLocallyHuberStandard :=
  hX.of_isPullback_of_locallyOfWeaklyFiniteType hs.flip hg hf hXss

/-- `pullback f g` is locally of Huber's standing class when `f` is locally of weakly finite type,
`g` is adic, and `Y` is locally stably sheafy and locally of Huber's standing class. -/
theorem isLocallyHuberStandard_pullback_of_locallyOfWeaklyFiniteType_left
    {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g] (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g)
    (hYss : Y.IsLocallyStablySheafy) (hY : Y.IsLocallyHuberStandard) :
    (pullback f g).IsLocallyHuberStandard :=
  hY.of_isPullback_of_locallyOfWeaklyFiniteType (.of_hasPullback f g) hf hg hYss

/-- `pullback f g` is locally of Huber's standing class when `f` is adic, `g` is locally of weakly
finite type, and `X` is locally stably sheafy and locally of Huber's standing class. -/
theorem isLocallyHuberStandard_pullback_of_locallyOfWeaklyFiniteType_right
    {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g] (hf : IsAdic f) (hg : LocallyOfWeaklyFiniteType g)
    (hXss : X.IsLocallyStablySheafy) (hX : X.IsLocallyHuberStandard) :
    (pullback f g).IsLocallyHuberStandard :=
  hX.of_isPullback_of_locallyOfWeaklyFiniteType_flip (.of_hasPullback f g) hf hg hXss

end BaseChange

end TauCeti.AdicSpace
