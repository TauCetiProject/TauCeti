/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.PlusWeaklyFiniteType
public import TauCeti.AlgebraicGeometry.AdicSpace.Pullback.Affinoid
public import TauCeti.AlgebraicGeometry.AdicSpace.Pullback.Cover

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Sheafy
import TauCeti.RingTheory.Huber.TensorProduct.TopologicallyFiniteType
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel

/-!
# Existence and base-change stability of fibre products of adic spaces

In the category `(Adic)` of adic spaces (`TauCeti.AdicSpace`), fibre products do not exist in full
generality because completed tensor products of sheafy Huber rings need not be sheafy. Following
Huber (1994, Proposition 3.7; 1996, Proposition 1.2.2 part 1) and Corollary 1.2.3) and Wedhorn
(§8.6, Theorem 8.56, Remark 8.57(1), and Proposition 8.58), this file establishes the existence of
the fibre product `X ×_S Y` and its base-change stability whenever one morphism is locally of
weakly finite type (`TauCeti.AdicSpace.LocallyOfWeaklyFiniteType`), the other morphism is adic
(`TauCeti.AdicSpace.IsAdic`), and the adic factor is locally stably sheafy
(`TauCeti.AdicSpace.IsLocallyStablySheafy` — for instance, any locally noetherian analytic adic
space).

## Existence

1. **Open subspaces in `AdicSpace`**: an open `U` of an adic space `X` restricts to an adic space
   `X.restrict U` with canonical open immersion `X.ofRestrict U : X.restrict U ⟶ X`, and open
   immersions admit pullbacks along arbitrary morphisms in `AdicSpace`
   (`isPullback_restrictPreimage`, `hasPullback_of_isOpenImmersion_left`).
2. **Global gluing**: given `f : X ⟶ S` locally of weakly finite type and `g : Y ⟶ S` adic with `Y`
   locally stably sheafy, `X` is covered by complete Hausdorff affinoid charts `(U_x, V_x)` of `f`
   (`LocallyOfWeaklyFiniteType.exists_complete_chart`). Since fibre products in `AdicSpace` are
   local on the source (`hasPullback_of_cover`), existence reduces to each chart `U_x ⟶ V_x` after
   base-changing `g` to `g⁻¹(V_x)` (`IsPullback.paste_horiz`). Covering `g⁻¹(V_x)` by stably sheafy
   open affinoids `W_y` and applying `hasPullback_of_cover` in the symmetric variable reduces to
   the affinoid completed tensor product `Spa((C, C⁺) ⊗̂_A (B, B⁺))`
   (`isPullback_ofPresentation_completedTensor`,
   `isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_right`).

## Base-change stability

Given *any* pullback square `IsPullback p q f g` in `AdicSpace` with `f : X ⟶ S` chart-locally `Q`,
`g : Y ⟶ S` adic, and `Y` locally stably sheafy, around any point `z` of `Z` one chooses a complete
chart `U ⊆ X`, `V ⊆ S` of `f` at `p(z)` and a stably sheafy affinoid open `W ⊆ g⁻¹(V)` of `Y` at
`q(z)`. Both `Z|_{p⁻¹(U) ∩ q⁻¹(W)}` and `Spa((C, C⁺) ⊗̂_A (B, B⁺))` are pullbacks of the restricted
cospan `(X|_U ⟶ S, Y|_W ⟶ S)`, so uniqueness of pullbacks (`IsPullback.isoIsPullback`) identifies
`q` locally with `Spa(inr)` and `p` locally with `Spa(inl)`. From the ring- and pair-level base
change theorems (`TauCeti.Huber.CompletedTensor.isTopologicallyFiniteType_inr`,
`TauCeti.Huber.Pair.completedTensor.isPlusWeaklyFiniteType_inr`,
`TauCeti.Huber.Pair.completedTensor.isTopologicallyFiniteType_inr`,
`TauCeti.Huber.CompletedTensor.isAdicHom_inl`), this yields base-change stability of:

* `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType`,
* `TauCeti.AdicSpace.LocallyOfPlusWeaklyFiniteType`,
* `TauCeti.PreAdicSpace.LocallyOfFiniteType` (along adic base change),
* `TauCeti.AdicSpace.IsAdic` (along base change locally of weakly finite type), and
* `TauCeti.AdicSpace.IsLocallyStablySheafy`, `TauCeti.AdicSpace.IsLocallyNoetherian`, and
  `TauCeti.AdicSpace.IsLocallyHuberStandard` on the fibre product.

## Main definitions and results

* `TauCeti.AdicSpace.restrict`, `TauCeti.AdicSpace.ofRestrict`,
  `TauCeti.AdicSpace.restrictPreimage`, `TauCeti.AdicSpace.isPullback_restrictPreimage`: open
  subspaces and open-immersion pullbacks in `AdicSpace`.
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
  Theorem 8.56, Remark 8.57(1), and Proposition 8.58.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace TauCeti.AdicSpace

open Huber PreAdicSpace ValuationSpectrum

universe u

/-! ### Open subspaces and open-immersion pullbacks in `AdicSpace` -/

section OpenSubspace

variable {X Y Z S : AdicSpace.{u}}

/-- The open subspace `X|_U` of an adic space `X` associated to an open `U : Opens X.obj`, packaged
as an object of `AdicSpace`. Marked `abbrev` so `(X.restrict U).obj` reduces definitionally to
`X.obj.restrict U.isOpenEmbedding`. -/
noncomputable abbrev restrict (X : AdicSpace.{u}) (U : Opens X.obj) : AdicSpace.{u} :=
  ⟨X.obj.restrict U.isOpenEmbedding, PreAdicSpace.isAdic_restrict U.isOpenEmbedding X.property⟩

/-- The underlying pre-adic space of `X.restrict U` is `X.obj.restrict U.isOpenEmbedding`. -/
theorem restrict_obj (X : AdicSpace.{u}) (U : Opens X.obj) :
    (X.restrict U).obj = X.obj.restrict U.isOpenEmbedding :=
  (rfl)

/-- The canonical open immersion `X.restrict U ⟶ X` in `AdicSpace`. -/
noncomputable def ofRestrict (X : AdicSpace.{u}) (U : Opens X.obj) : X.restrict U ⟶ X :=
  ObjectProperty.homMk (X.obj.ofRestrict U.isOpenEmbedding)

@[simp]
theorem ofRestrict_hom (X : AdicSpace.{u}) (U : Opens X.obj) :
    (X.ofRestrict U).hom = X.obj.ofRestrict U.isOpenEmbedding :=
  (rfl)

theorem ofRestrict_base (X : AdicSpace.{u}) (U : Opens X.obj) :
    (X.ofRestrict U).hom.base = U.inclusion' :=
  (rfl)

instance (X : AdicSpace.{u}) (U : Opens X.obj) :
    PreAdicSpace.IsOpenImmersion (X.ofRestrict U).hom :=
  PreAdicSpace.IsOpenImmersion.ofRestrict X.obj U.isOpenEmbedding

/-- Any morphism in `AdicSpace` whose underlying morphism of pre-adic spaces is an open immersion is
a monomorphism in `AdicSpace`. -/
instance mono_of_isOpenImmersion (i : X ⟶ Y) [PreAdicSpace.IsOpenImmersion i.hom] : Mono i :=
  (ObjectProperty.ι PreAdicSpace.isAdic).mono_of_mono_map (inferInstanceAs (Mono i.hom))

/-- The restriction `X|_{f⁻¹(V)} ⟶ Y|_V` of a morphism `f : X ⟶ Y` of adic spaces over an open
`V : Opens Y.obj`. -/
noncomputable def restrictPreimage (f : X ⟶ Y) (V : Opens Y.obj) :
    X.restrict ((Opens.map f.hom.base).obj V) ⟶ Y.restrict V :=
  ObjectProperty.homMk (f.hom.restrictPreimage V)

@[simp]
theorem restrictPreimage_hom (f : X ⟶ Y) (V : Opens Y.obj) :
    (restrictPreimage f V).hom = f.hom.restrictPreimage V :=
  (rfl)

@[reassoc (attr := simp)]
theorem restrictPreimage_ofRestrict (f : X ⟶ Y) (V : Opens Y.obj) :
    restrictPreimage f V ≫ Y.ofRestrict V =
      X.ofRestrict ((Opens.map f.hom.base).obj V) ≫ f := by
  ext1
  exact f.hom.restrictPreimage_ofRestrict V

/-- Lifting a morphism `f : X ⟶ Y` restricted to `O ≤ f⁻¹(U)` across `Y.ofRestrict U` in
`AdicSpace`. -/
noncomputable def liftRestrict (f : X ⟶ Y) {O : Opens X.obj} {U : Opens Y.obj}
    (hOU : O ≤ (Opens.map f.hom.base).obj U) :
    X.restrict O ⟶ Y.restrict U :=
  ObjectProperty.homMk <|
    PreAdicSpace.IsOpenImmersion.lift (Y.obj.ofRestrict U.isOpenEmbedding)
      (X.obj.ofRestrict O.isOpenEmbedding ≫ f.hom)
      (by
        rintro _ ⟨x, rfl⟩
        exact ⟨⟨f.hom.base x.1, hOU x.2⟩, rfl⟩)

@[reassoc (attr := simp)]
theorem liftRestrict_ofRestrict (f : X ⟶ Y) {O : Opens X.obj} {U : Opens Y.obj}
    (hOU : O ≤ (Opens.map f.hom.base).obj U) :
    liftRestrict f hOU ≫ Y.ofRestrict U = X.ofRestrict O ≫ f := by
  ext1
  exact PreAdicSpace.IsOpenImmersion.lift_fac _ _ _

/-- **Canonical pullback square of an open subspace inclusion `S.ofRestrict V` along `g : Y ⟶ S`**
in `AdicSpace`: the fibre product is `Y.restrict (g⁻¹(V))` with projections `restrictPreimage g V`
and `Y.ofRestrict (g⁻¹(V))`. -/
theorem isPullback_restrictPreimage (g : Y ⟶ S) (V : Opens S.obj) :
    IsPullback (restrictPreimage g V) (Y.ofRestrict ((Opens.map g.hom.base).obj V))
      (S.ofRestrict V) g := by
  refine { w := restrictPreimage_ofRestrict g V
           isLimit' := ⟨PullbackCone.isLimitAux' _ fun s ↦ ?_⟩ }
  have hrange : Set.range s.snd.hom.base ⊆
      Set.range (Y.obj.ofRestrict ((Opens.map g.hom.base).obj V).isOpenEmbedding).base := by
    rintro _ ⟨w, rfl⟩
    have hw : (s.fst ≫ S.ofRestrict V).hom.base w = (s.snd ≫ g).hom.base w :=
      congrArg (fun k : s.pt ⟶ S ↦ k.hom.base w) s.condition
    simp only [ObjectProperty.FullSubcategory.comp_hom, PreAdicSpace.comp_base, ofRestrict_base,
      TopCat.coe_comp, Function.comp_apply] at hw
    exact ⟨⟨s.snd.hom.base w, Opens.mem_map.mpr (hw ▸ (s.fst.hom.base w).2)⟩, rfl⟩
  let m : s.pt ⟶ Y.restrict ((Opens.map g.hom.base).obj V) :=
    ObjectProperty.homMk (PreAdicSpace.IsOpenImmersion.lift _ s.snd.hom hrange)
  have hm₂ : m ≫ Y.ofRestrict ((Opens.map g.hom.base).obj V) = s.snd := by
    ext1
    exact PreAdicSpace.IsOpenImmersion.lift_fac _ _ _
  have hm₁ : m ≫ restrictPreimage g V = s.fst := by
    rw [← cancel_mono (S.ofRestrict V), Category.assoc, restrictPreimage_ofRestrict,
      ← Category.assoc, hm₂, s.condition]
  exact ⟨m, hm₁, hm₂, fun {m'} _ h₂ ↦ (cancel_mono (Y.ofRestrict _)).mp (h₂.trans hm₂.symm)⟩

/-- **Adic spaces have pullbacks along open immersions on the left**: the pullback cone
`PreAdicSpace.IsOpenImmersion.pullbackConeOfLeft` in `PreAdicSpace` has adic cone point and hence is
a pullback in the full subcategory `AdicSpace`. -/
instance hasPullback_of_isOpenImmersion_left (i : X ⟶ S) [PreAdicSpace.IsOpenImmersion i.hom]
    (g : Y ⟶ S) : HasPullback i g := by
  let c := PreAdicSpace.IsOpenImmersion.pullbackConeOfLeft i.hom g.hom
  have hc : PreAdicSpace.isAdic c.pt :=
    PreAdicSpace.isAdic_of_isOpenImmersion Y.property c.snd
  have hlim : IsLimit (PullbackCone.mk (W := (⟨c.pt, hc⟩ : AdicSpace.{u}))
      (ObjectProperty.homMk c.fst) (ObjectProperty.homMk c.snd)
      (by ext1; exact c.condition) : PullbackCone i g) := by
    refine PullbackCone.isLimitAux' _ fun s ↦ ?_
    let s' : PullbackCone i.hom g.hom :=
      PullbackCone.mk s.fst.hom s.snd.hom (congrArg InducedCategory.Hom.hom s.condition)
    let H := PreAdicSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit i.hom g.hom
    refine ⟨ObjectProperty.homMk (H.lift s'),
      by ext1; exact H.fac s' WalkingCospan.left,
      by ext1; exact H.fac s' WalkingCospan.right,
      fun {m} hm₁ hm₂ ↦ ?_⟩
    ext1
    exact PullbackCone.IsLimit.hom_ext H
      ((congrArg InducedCategory.Hom.hom hm₁).trans (H.fac s' WalkingCospan.left).symm)
      ((congrArg InducedCategory.Hom.hom hm₂).trans (H.fac s' WalkingCospan.right).symm)
  exact ⟨⟨⟨_, hlim⟩⟩⟩

/-- **Adic spaces have pullbacks along open immersions on the right.** -/
instance hasPullback_of_isOpenImmersion_right (f : X ⟶ S) (i : Y ⟶ S)
    [PreAdicSpace.IsOpenImmersion i.hom] : HasPullback f i :=
  hasPullback_symmetry i f

end OpenSubspace

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
    have hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa TB.plus))
        (presentationLimitPresheaf PB TB.plus) :=
      isSheaf_presentationLimitPresheaf_of_isSheafyRing PB TB.isRingOfIntegralElements hPB
        hB.isSheafyRing
    let eW : Y.restrict (W y) ≅ ofPresentation TB PB hPB hsheafB :=
      ObjectProperty.isoMk PreAdicSpace.isAdic eW₀
    let g_y : ofPresentation TB PB hPB hsheafB ⟶ ofPresentation SA PA hPA hsheafA :=
      eW.inv ≫ Y.ofRestrict (W y) ≫ g
    have hg_y : IsAdic g_y :=
      IsAdic.isMultiplicative.comp_mem eW.inv _ (MorphismProperty.of_isIso _ _)
        (IsAdic.isMultiplicative.comp_mem _ _ (IsAdic.of_isOpenImmersion _) hg)
    let ψ : Pair.Hom SA TB := ofPresentationHomEquiv SA PA hPA hsheafA TB PB hPB hsheafB g_y
    have hψeq : comapOfPresentation SA PA hPA hsheafA TB PB hPB hsheafB ψ = g_y := by
      rw [← ofPresentationHomEquiv_symm_apply]
      exact (ofPresentationHomEquiv SA PA hPA hsheafA TB PB hPB hsheafB).symm_apply_apply g_y
    have hψadic : IsAdicHom ψ.toRingHom :=
      (isAdic_comapOfPresentation_iff SA PA hPA hsheafA TB PB hPB hsheafB ψ).mp (hψeq ▸ hg_y)
    let : Algebra A B := ψ.toRingHom.toAlgebra
    let : Algebra A C := φ.toRingHom.toAlgebra
    have hAB : algebraMap A B = ψ.toRingHom := rfl
    have hAC : algebraMap A C = φ.toRingHom := rfl
    have : IsAdicHom (algebraMap A B) := hAB ▸ hψadic
    have : IsAdicHom (algebraMap A C) := hAC ▸ hφ.isAdicHom
    have hsheafE_all : IsSheafyForEveryPresentation (TB.completedTensor A UC).plus :=
      isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_left TB UC hB (hAC ▸ hφ)
    obtain ⟨PE, hPE, hsheafE⟩ := hsheafE_all.exists_compatible_isSheaf
    have hpull : HasPullback g_y f₀ := by
      rw [← hψeq]
      exact (isPullback_ofPresentation_completedTensor PA PB PC PE hPA hPB hPC hPE
        hsheafA hsheafB hsheafC hsheafE ψ φ hAB.symm hAC.symm).hasPullback
    have heq : eW.hom ≫ g_y = Y.ofRestrict (W y) ≫ g := by
      simp [g_y]
    rw [← heq]
    exact (HasPullback.comp_left_left_iff_of_isIso eW.hom).mpr hpull
  exact hasPullback_of_cover g f₀ (fun y ↦ Y.ofRestrict (W y)) fun y ↦ ⟨y, ⟨y, hyW y⟩, rfl⟩

variable {X Y S : AdicSpace.{u}}

/-- **Existence of fibre products of adic spaces in the adic case** (Huber 1994, Proposition 3.7;
Huber 1996, Proposition 1.2.2 part 1); Wedhorn, Theorem 8.56 and Remark 8.57(1)): if `f : X ⟶ S`
is locally of weakly finite type, `g : Y ⟶ S` is adic, and `Y` is locally stably sheafy, then the
fibre product `X ×_S Y` exists in the category `AdicSpace`. -/
theorem hasPullback_of_locallyOfWeaklyFiniteType_left {f : X ⟶ S} {g : Y ⟶ S}
    (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g) (hY : Y.IsLocallyStablySheafy) :
    HasPullback f g := by
  choose U hxU V _ rest using fun x : X.obj ↦ hf.exists_complete_chart x
  have hpb (x : X.obj) : HasPullback (X.ofRestrict (U x) ≫ f) g := by
    obtain ⟨A, _, _, _, _, _, _, _, SA, PA, hPA, C, _, _, _, _, _, _, _, UC, PC, hPC,
      φ, hφ, hsheafC, eU₀, eV₀, hfac⟩ := rest x
    have hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa SA.plus))
        (presentationLimitPresheaf PA SA.plus) :=
      (isSheafy_presentationLimitPreAdicSpace_iff PA SA.plus _ hPA).mp
        (ObjectProperty.prop_of_iso isSheafy eV₀
          (isSheafy_restrict (V x).isOpenEmbedding S.property.isSheafy))
    let eU : X.restrict (U x) ≅ ofPresentation UC PC hPC hsheafC :=
      ObjectProperty.isoMk PreAdicSpace.isAdic eU₀
    let eV : S.restrict (V x) ≅ ofPresentation SA PA hPA hsheafA :=
      ObjectProperty.isoMk PreAdicSpace.isAdic eV₀
    let f₀ := comapOfPresentation SA PA hPA hsheafA UC PC hPC hsheafC φ
    let f_x : X.restrict (U x) ⟶ S.restrict (V x) := eU.hom ≫ f₀ ≫ eV.inv
    have hfac' : X.ofRestrict (U x) ≫ f = f_x ≫ S.ofRestrict (V x) := by
      ext1
      simpa only [f_x, f₀, eU, eV, ObjectProperty.FullSubcategory.comp_hom, ofRestrict_hom,
        ObjectProperty.isoMk_hom, ObjectProperty.isoMk_inv,
        comapOfPresentation_eq_homMk_presentationLimitPreAdicSpaceComap,
        ObjectProperty.homMk_hom, Category.assoc] using hfac
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
    have hpb₂ : HasPullback f_x g_x := by
      dsimp only [f_x]
      exact (HasPullback.comp_left_left_iff_of_isIso eU.hom).mpr hpb₁
    rw [hfac']
    exact ((IsPullback.of_hasPullback f_x g_x).paste_vert
      (isPullback_restrictPreimage g (V x))).hasPullback
  exact hasPullback_of_cover f g (fun x ↦ X.ofRestrict (U x)) fun x ↦ ⟨x, ⟨x, hxU x⟩, rfl⟩

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

/-- **Huber 1996, Proposition 1.2.2 part 1) over locally noetherian analytic spaces**: if
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

/-- The open subspace `Z|_{p⁻¹(U) ∩ q⁻¹(W)}` of the vertex `Z` of a pullback square
`IsPullback p q f g` is a pullback of the restricted cospan `(X|_U ⟶ S, Y|_W ⟶ S)`. -/
private theorem isPullback_restrict_inf_of_isPullback
    {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (hs : IsPullback p q f g)
    (U : Opens X.obj) (W : Opens Y.obj) :
    let O : Opens Z.obj := (Opens.map p.hom.base).obj U ⊓ (Opens.map q.hom.base).obj W
    IsPullback
      (liftRestrict p (inf_le_left : O ≤ (Opens.map p.hom.base).obj U))
      (liftRestrict q (inf_le_right : O ≤ (Opens.map q.hom.base).obj W))
      (X.ofRestrict U ≫ f) (Y.ofRestrict W ≫ g) := by
  intro O
  have hOU : O ≤ (Opens.map p.hom.base).obj U := inf_le_left
  have hOW : O ≤ (Opens.map q.hom.base).obj W := inf_le_right
  let p_O := liftRestrict p hOU
  let q_O := liftRestrict q hOW
  have hw : p_O ≫ X.ofRestrict U ≫ f = q_O ≫ Y.ofRestrict W ≫ g := by
    rw [← Category.assoc, liftRestrict_ofRestrict, ← Category.assoc, liftRestrict_ofRestrict,
      Category.assoc, Category.assoc, hs.w]
  refine { w := hw, isLimit' := ⟨PullbackCone.isLimitAux' _ fun s ↦ ?_⟩ }
  have hcond : (s.fst ≫ X.ofRestrict U) ≫ f = (s.snd ≫ Y.ofRestrict W) ≫ g := by
    simpa only [Category.assoc] using s.condition
  let l : s.pt ⟶ Z := hs.lift (s.fst ≫ X.ofRestrict U) (s.snd ≫ Y.ofRestrict W) hcond
  have hl₁ : l ≫ p = s.fst ≫ X.ofRestrict U := hs.lift_fst _ _ hcond
  have hl₂ : l ≫ q = s.snd ≫ Y.ofRestrict W := hs.lift_snd _ _ hcond
  have hrange : Set.range l.hom.base ⊆ Set.range (Z.obj.ofRestrict O.isOpenEmbedding).base := by
    rintro _ ⟨w, rfl⟩
    have hw₁ := congrArg (fun k : s.pt ⟶ X ↦ k.hom.base w) hl₁
    have hw₂ := congrArg (fun k : s.pt ⟶ Y ↦ k.hom.base w) hl₂
    simp only [ObjectProperty.FullSubcategory.comp_hom, PreAdicSpace.comp_base, ofRestrict_base,
      TopCat.coe_comp, Function.comp_apply] at hw₁ hw₂
    have hmem : l.hom.base w ∈ O :=
      ⟨Opens.mem_map.mpr (hw₁.symm ▸ (s.fst.hom.base w).2),
        Opens.mem_map.mpr (hw₂.symm ▸ (s.snd.hom.base w).2)⟩
    exact ⟨⟨l.hom.base w, hmem⟩, rfl⟩
  let m : s.pt ⟶ Z.restrict O :=
    ObjectProperty.homMk (PreAdicSpace.IsOpenImmersion.lift _ l.hom hrange)
  have hmZ : m ≫ Z.ofRestrict O = l := by
    ext1
    exact PreAdicSpace.IsOpenImmersion.lift_fac _ _ _
  have hm₁ : m ≫ p_O = s.fst := by
    rw [← cancel_mono (X.ofRestrict U), Category.assoc, liftRestrict_ofRestrict,
      ← Category.assoc, hmZ, hl₁]
  have hm₂ : m ≫ q_O = s.snd := by
    rw [← cancel_mono (Y.ofRestrict W), Category.assoc, liftRestrict_ofRestrict,
      ← Category.assoc, hmZ, hl₂]
  refine ⟨m, hm₁, hm₂, fun {m'} hm'₁ hm'₂ ↦ ?_⟩
  simp only [PullbackCone.mk_fst] at hm'₁
  simp only [PullbackCone.mk_snd] at hm'₂
  apply (cancel_mono (Z.ofRestrict O)).mp
  refine hs.hom_ext ?_ ?_
  · rw [Category.assoc, ← liftRestrict_ofRestrict p hOU, ← Category.assoc, hm'₁, ← hl₁, hmZ]
  · rw [Category.assoc, ← liftRestrict_ofRestrict q hOW, ← Category.assoc, hm'₂, ← hl₂, hmZ]

/-- Parametric local-chart theorem on a pullback square `IsPullback p q f g` in `AdicSpace`: when
`f` satisfies `chartLocally Q`, `g` is adic, and `Y` is locally stably sheafy, every point `z` of
`Z` admits a completed-tensor affinoid chart identifying `q : Z ⟶ Y` locally with `Spa(inr)` (so `q`
satisfies `chartLocally Q'`) and `p : Z ⟶ X` locally with `Spa(inl)` (so `p` is adic). -/
private theorem chartLocally_snd_and_isAdic_fst_of_isPullback
    (Q Q' : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
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
      {C₁ : Type u} [CommRing C₁] [UniformSpace C₁] [IsUniformAddGroup C₁]
      [IsTopologicalRing C₁] [CompleteSpace C₁] [T2Space C₁] [IsHuberRing C₁] {UC₁ : Pair C₁}
      {φ : Pair.Hom SA UC} {ιA : Pair.Hom SA SA₁} {ιC : Pair.Hom UC UC₁} {φ₁ : Pair.Hom SA₁ UC₁},
      Q φ → ιC.IsTopologicallyFiniteType →
      (φ.IsTopologicallyFiniteType → (ιC.comp φ).IsTopologicallyFiniteType) →
      φ₁.comp ιA = ιC.comp φ → Q φ₁)
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
      Q' (Pair.completedTensor.inr A UC TB))
    {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hs : IsPullback p q f g) (hf : chartLocally Q f.hom)
    (hg : IsAdic g) (hY : Y.IsLocallyStablySheafy) :
    chartLocally Q' q.hom ∧ IsAdic p := by
  have hpoint (z : Z.obj) :
      (∃ (O : Opens Z.obj) (_ : z ∈ O) (W : Opens Y.obj) (_ : O ≤ (Opens.map q.hom.base).obj W)
        (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsTopologicalRing B)
        (_ : IsHuberRing B) (TB : Pair B) (PB : PairOfDefinition B)
        (hPB : PB.ringOfDefinition ≤ TB.plus)
        (E : Type u) (_ : CommRing E) (_ : UniformSpace E) (_ : IsUniformAddGroup E)
        (_ : IsTopologicalRing E) (_ : CompleteSpace E) (_ : T2Space E) (_ : IsHuberRing E)
        (WE : Pair E) (PE : PairOfDefinition E) (hPE : PE.ringOfDefinition ≤ WE.plus)
        (inrHom : Pair.Hom TB WE) (_ : Q' inrHom)
        (hsheafE : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa WE.plus))
          (presentationLimitPresheaf PE WE.plus))
        (eO : Z.obj.restrict O.isOpenEmbedding ≅
          presentationLimitPreAdicSpace PE WE.plus WE.isRingOfIntegralElements.isPowerBounded_of_mem
            hPE)
        (eW : Y.obj.restrict W.isOpenEmbedding ≅
          presentationLimitPreAdicSpace PB TB.plus TB.isRingOfIntegralElements.isPowerBounded_of_mem
            hPB),
        Z.obj.ofRestrict _ ≫ q.hom =
          eO.hom ≫ presentationLimitPreAdicSpaceComap inrHom.toRingHom inrHom.continuous_toRingHom
            inrHom.map_mem_plus TB.isRingOfIntegralElements.isPowerBounded_of_mem
            WE.isRingOfIntegralElements.isPowerBounded_of_mem hPB hPE hsheafE ≫
            eW.inv ≫ Y.obj.ofRestrict _) ∧
      (∃ (O : Opens Z.obj) (_ : z ∈ O) (U : Opens X.obj) (_ : O ≤ (Opens.map p.hom.base).obj U)
        (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
        (_ : IsHuberRing C) (UC : Pair C) (PC : PairOfDefinition C)
        (hPC : PC.ringOfDefinition ≤ UC.plus)
        (E : Type u) (_ : CommRing E) (_ : UniformSpace E) (_ : IsUniformAddGroup E)
        (_ : IsTopologicalRing E) (_ : CompleteSpace E) (_ : T2Space E) (_ : IsHuberRing E)
        (WE : Pair E) (PE : PairOfDefinition E) (hPE : PE.ringOfDefinition ≤ WE.plus)
        (inlHom : Pair.Hom UC WE) (_ : IsAdicHom inlHom.toRingHom)
        (hsheafE : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa WE.plus))
          (presentationLimitPresheaf PE WE.plus))
        (eO : Z.obj.restrict O.isOpenEmbedding ≅
          presentationLimitPreAdicSpace PE WE.plus WE.isRingOfIntegralElements.isPowerBounded_of_mem
            hPE)
        (eU : X.obj.restrict U.isOpenEmbedding ≅
          presentationLimitPreAdicSpace PC UC.plus UC.isRingOfIntegralElements.isPowerBounded_of_mem
            hPC),
        Z.obj.ofRestrict _ ≫ p.hom =
          eO.hom ≫ presentationLimitPreAdicSpaceComap inlHom.toRingHom inlHom.continuous_toRingHom
            inlHom.map_mem_plus UC.isRingOfIntegralElements.isPowerBounded_of_mem
            WE.isRingOfIntegralElements.isPowerBounded_of_mem hPC hPE hsheafE ≫
            eU.inv ≫ X.obj.ofRestrict _) := by
    -- 1. Choose a complete Hausdorff chart `(U, V)` of `f` around `p(z)`.
    obtain ⟨U, hzpU, V, hUV, A, _, _, _, _, _, _, _, SA, PA, hPA,
      C, _, _, _, _, _, _, _, UC, PC, hPC, φ, hφQ, hsheafC, eU₀, eV₀, hfac_f⟩ :=
      exists_complete_chart_of_chartLocally Q hQcomp hf (p.hom.base z)
    have hφtft : IsTopologicallyFiniteType φ.toRingHom := hQtft hφQ
    have hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa SA.plus))
        (presentationLimitPresheaf PA SA.plus) :=
      (isSheafy_presentationLimitPreAdicSpace_iff PA SA.plus _ hPA).mp
        (ObjectProperty.prop_of_iso isSheafy eV₀
          (isSheafy_restrict V.isOpenEmbedding S.property.isSheafy))
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
    have hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa TB.plus))
        (presentationLimitPresheaf PB TB.plus) :=
      isSheaf_presentationLimitPresheaf_of_isSheafyRing PB TB.isRingOfIntegralElements hPB
        hB.isSheafyRing
    let eU : X.restrict U ≅ ofPresentation UC PC hPC hsheafC :=
      ObjectProperty.isoMk PreAdicSpace.isAdic eU₀
    let eV : S.restrict V ≅ ofPresentation SA PA hPA hsheafA :=
      ObjectProperty.isoMk PreAdicSpace.isAdic eV₀
    let eW : Y.restrict W ≅ ofPresentation TB PB hPB hsheafB :=
      ObjectProperty.isoMk PreAdicSpace.isAdic eW₀
    -- 3. Express `Y.ofRestrict W ≫ g` via an adic pair morphism `ψ : (A, A⁺) → (B, B⁺)`.
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
    let ψ : Pair.Hom SA TB := ofPresentationHomEquiv SA PA hPA hsheafA TB PB hPB hsheafB g₀
    have hψeq : comapOfPresentation SA PA hPA hsheafA TB PB hPB hsheafB ψ = g₀ := by
      rw [← ofPresentationHomEquiv_symm_apply]
      exact (ofPresentationHomEquiv SA PA hPA hsheafA TB PB hPB hsheafB).symm_apply_apply g₀
    have hψadic : IsAdicHom ψ.toRingHom :=
      (isAdic_comapOfPresentation_iff SA PA hPA hsheafA TB PB hPB hsheafB ψ).mp (hψeq ▸ hg₀)
    -- 4. Form the completed tensor product `(C, C⁺) ⊗̂_A (B, B⁺)` and its pullback square.
    let : Algebra A C := φ.toRingHom.toAlgebra
    let : Algebra A B := ψ.toRingHom.toAlgebra
    have hAC : algebraMap A C = φ.toRingHom := rfl
    have hAB : algebraMap A B = ψ.toRingHom := rfl
    have : IsAdicHom (algebraMap A C) := hAC ▸ hφtft.isAdicHom
    have : IsAdicHom (algebraMap A B) := hAB ▸ hψadic
    have hsheafE_all : IsSheafyForEveryPresentation (UC.completedTensor A TB).plus :=
      isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_right UC TB hB
        (hAC ▸ hφtft)
    obtain ⟨PE, hPE, hsheafE⟩ := hsheafE_all.exists_compatible_isSheaf
    let WE := UC.completedTensor A TB
    let inlHom := Pair.completedTensor.inl A UC TB
    let inrHom := Pair.completedTensor.inr A UC TB
    have hpull₀ := isPullback_ofPresentation_completedTensor PA PC PB PE hPA hPC hPB hPE
      hsheafA hsheafC hsheafB hsheafE φ ψ hAC.symm hAB.symm
    -- Conjugate `hpull₀` by `eU`, `eW`, `eV` and compose with the monomorphism `S.ofRestrict V`.
    let πC := comapOfPresentation UC PC hPC hsheafC WE PE hPE hsheafE inlHom
    let πB := comapOfPresentation TB PB hPB hsheafB WE PE hPE hsheafE inrHom
    let f₀ := comapOfPresentation SA PA hPA hsheafA UC PC hPC hsheafC φ
    let g₀' := comapOfPresentation SA PA hPA hsheafA TB PB hPB hsheafB ψ
    have hpull₁ : IsPullback (πC ≫ eU.inv) (πB ≫ eW.inv)
        (eU.hom ≫ f₀ ≫ eV.inv) (eW.hom ≫ g₀' ≫ eV.inv) :=
      hpull₀.of_iso' (Iso.refl _) eU eW eV
        (by simp [πC, WE, inlHom]) (by simp [πB, WE, inrHom]) (by simp [f₀]) (by simp [g₀'])
    have hfac_f' : eU.hom ≫ f₀ ≫ eV.inv ≫ S.ofRestrict V = X.ofRestrict U ≫ f := by
      ext1
      simpa only [f₀, eU, eV, ObjectProperty.FullSubcategory.comp_hom, ofRestrict_hom,
        ObjectProperty.isoMk_hom, ObjectProperty.isoMk_inv,
        comapOfPresentation_eq_homMk_presentationLimitPreAdicSpaceComap,
        ObjectProperty.homMk_hom, Category.assoc] using hfac_f.symm
    have hfac_g' : eW.hom ≫ g₀' ≫ eV.inv ≫ S.ofRestrict V = Y.ofRestrict W ≫ g := by
      simp [g₀', hψeq, g₀, g_W]
    have hpull_aff : IsPullback (πC ≫ eU.inv) (πB ≫ eW.inv)
        (X.ofRestrict U ≫ f) (Y.ofRestrict W ≫ g) := by
      have hbot : IsPullback (eW.hom ≫ g₀' ≫ eV.inv) (𝟙 _) (S.ofRestrict V) (Y.ofRestrict W ≫ g) :=
        IsPullback.of_vert_isIso_mono
          ⟨by simpa only [Category.id_comp, Category.assoc] using hfac_g'⟩
      simpa only [Category.comp_id, Category.assoc, hfac_f'] using hpull₁.paste_vert hbot
    -- 5. Compare with `Z.restrict O` (`O = p⁻¹(U) ∩ q⁻¹(W)`) via `IsPullback.isoIsPullback`.
    let O : Opens Z.obj := (Opens.map p.hom.base).obj U ⊓ (Opens.map q.hom.base).obj W
    have hzO : z ∈ O := ⟨hzpU, hzqW⟩
    have hpull_Z : IsPullback
        (liftRestrict p (inf_le_left : O ≤ (Opens.map p.hom.base).obj U))
        (liftRestrict q (inf_le_right : O ≤ (Opens.map q.hom.base).obj W))
        (X.ofRestrict U ≫ f) (Y.ofRestrict W ≫ g) :=
      isPullback_restrict_inf_of_isPullback hs U W
    let eO : Z.restrict O ≅ ofPresentation WE PE hPE hsheafE :=
      hpull_Z.isoIsPullback _ _ hpull_aff
    have heO_p : Z.ofRestrict O ≫ p = eO.hom ≫ πC ≫ eU.inv ≫ X.ofRestrict U := by
      have hfst := hpull_Z.isoIsPullback_hom_fst _ _ hpull_aff
      have hcomp := congrArg (· ≫ X.ofRestrict U) hfst
      simpa only [Category.assoc, liftRestrict_ofRestrict] using hcomp.symm
    have heO_q : Z.ofRestrict O ≫ q = eO.hom ≫ πB ≫ eW.inv ≫ Y.ofRestrict W := by
      have hsnd := hpull_Z.isoIsPullback_hom_snd _ _ hpull_aff
      have hcomp := congrArg (· ≫ Y.ofRestrict W) hsnd
      simpa only [Category.assoc, liftRestrict_ofRestrict] using hcomp.symm
    have hplus : SA.plus ≤ TB.plus.comap (algebraMap A B) := fun a ha ↦ by
      rw [Subring.mem_comap, hAB]
      exact ψ.map_mem_plus a ha
    have hinr : Q' inrHom := hQbc hplus hφQ hAC.symm
    have hinl : IsAdicHom inlHom.toRingHom := by
      rw [Pair.completedTensor.toRingHom_inl]
      exact CompletedTensor.isAdicHom_inl A C B
    refine ⟨⟨O, hzO, W, inf_le_right, B, inferInstance, inferInstance, inferInstance,
      inferInstance, TB, PB, hPB, CompletedTensor A C B, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      WE, PE, hPE, inrHom, hinr, hsheafE, (ObjectProperty.ι _).mapIso eO, eW₀, ?_⟩,
      ⟨O, hzO, U, inf_le_left, C, inferInstance, inferInstance, inferInstance,
      inferInstance, UC, PC, hPC, CompletedTensor A C B, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      WE, PE, hPE, inlHom, hinl, hsheafE, (ObjectProperty.ι _).mapIso eO, eU₀, ?_⟩⟩
    · simpa only [πB, eW, ObjectProperty.FullSubcategory.comp_hom, ofRestrict_hom,
        Functor.mapIso_hom, ObjectProperty.ι_map, ObjectProperty.isoMk_inv,
        comapOfPresentation_eq_homMk_presentationLimitPreAdicSpaceComap,
        ObjectProperty.homMk_hom, Category.assoc] using congrArg InducedCategory.Hom.hom heO_q
    · simpa only [πC, eU, ObjectProperty.FullSubcategory.comp_hom, ofRestrict_hom,
        Functor.mapIso_hom, ObjectProperty.ι_map, ObjectProperty.isoMk_inv,
        comapOfPresentation_eq_homMk_presentationLimitPreAdicSpaceComap,
        ObjectProperty.homMk_hom, Category.assoc] using congrArg InducedCategory.Hom.hom heO_p
  exact ⟨(chartLocally_iff q.hom).mpr fun z ↦ (hpoint z).1,
    (isAdic_iff_chartLocally p).mpr <| (chartLocally_iff p.hom).mpr fun z ↦ (hpoint z).2⟩

/-- **Base-change stability of `LocallyOfWeaklyFiniteType`** (Huber 1996, Corollary 1.2.3(iii)(a);
Wedhorn, Proposition 8.58): in any pullback square `IsPullback p q f g` in `AdicSpace`, if
`f : X ⟶ S` is locally of weakly finite type, `g : Y ⟶ S` is adic, and `Y` is locally stably sheafy,
then `q : Z ⟶ Y` is locally of weakly finite type. -/
theorem LocallyOfWeaklyFiniteType.of_isPullback {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hs : IsPullback p q f g) (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g)
    (hY : Y.IsLocallyStablySheafy) : LocallyOfWeaklyFiniteType q :=
  (locallyOfWeaklyFiniteType_iff_chartLocally q).mpr
    (chartLocally_snd_and_isAdic_fst_of_isPullback
      (fun φ ↦ IsTopologicallyFiniteType φ.toRingHom)
      (fun φ ↦ IsTopologicallyFiniteType φ.toRingHom)
      (fun hφ ↦ hφ)
      (fun {A} _ _ _ _ {SA} {A₁} _ _ _ _ _ _ _ {SA₁} {C} _ _ _ _ _ _ _ {UC}
          {C₁} _ _ _ _ _ _ _ {UC₁} {φ ιA ιC φ₁} hφ hιC _ hcomm ↦ by
        have h := hιC.isTopologicallyFiniteType_toRingHom.comp hφ
        rw [← Pair.Hom.toRingHom_comp, ← hcomm, Pair.Hom.toRingHom_comp] at h
        exact h.of_comp ιA.continuous_toRingHom φ₁.continuous_toRingHom)
      (fun _ hφ hφA ↦ by
        rw [Pair.completedTensor.toRingHom_inr]
        exact CompletedTensor.isTopologicallyFiniteType_inr (hφA ▸ hφ))
      hs ((locallyOfWeaklyFiniteType_iff_chartLocally f).mp hf) hg hY).1

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
  (locallyOfPlusWeaklyFiniteType_iff_chartLocally q).mpr
    (chartLocally_snd_and_isAdic_fst_of_isPullback
      (fun φ ↦ φ.IsPlusWeaklyFiniteType)
      (fun φ ↦ φ.IsPlusWeaklyFiniteType)
      (fun hφ ↦ hφ.isTopologicallyFiniteType_toRingHom)
      (fun hφ hιC _ hcomm ↦ (hcomm ▸ hιC.isPlusWeaklyFiniteType.comp hφ).of_comp)
      (fun hplus hφ hφA ↦ Pair.completedTensor.isPlusWeaklyFiniteType_inr _ hplus hφ hφA)
      hs ((locallyOfPlusWeaklyFiniteType_iff_chartLocally f).mp hf) hg hY).1

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
Wedhorn, Proposition 8.58): in any pullback square `IsPullback p q f g` in `AdicSpace`, if
`f : X ⟶ S` is locally of finite type, `g : Y ⟶ S` is adic, and `Y` is locally stably sheafy, then
`q : Z ⟶ Y` is locally of finite type. -/
theorem locallyOfFiniteType_of_isPullback {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hs : IsPullback p q f g) (hf : PreAdicSpace.LocallyOfFiniteType f.hom) (hg : IsAdic g)
    (hY : Y.IsLocallyStablySheafy) : PreAdicSpace.LocallyOfFiniteType q.hom :=
  (locallyOfFiniteType_iff q.hom).mpr
    (chartLocally_snd_and_isAdic_fst_of_isPullback
      (fun φ ↦ φ.IsTopologicallyFiniteType)
      (fun φ ↦ φ.IsTopologicallyFiniteType)
      (fun hφ ↦ hφ.isTopologicallyFiniteType_toRingHom)
      (fun hφ _ hcomp hcomm ↦ (hcomm ▸ hcomp hφ).of_comp)
      (fun hplus hφ hφA ↦ Pair.completedTensor.isTopologicallyFiniteType_inr _ hplus hφ hφA)
      hs ((locallyOfFiniteType_iff f.hom).mp hf) hg hY).1

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

/-- **Base-change stability of `IsAdic` along morphisms locally of weakly finite type** (Wedhorn,
Proposition 8.58): in any pullback square `IsPullback p q f g` in `AdicSpace`, if `f : X ⟶ S` is
locally of weakly finite type, `g : Y ⟶ S` is adic, and `Y` is locally stably sheafy, then
`p : Z ⟶ X` is adic. -/
theorem IsAdic.of_isPullback_of_locallyOfWeaklyFiniteType {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S}
    {g : Y ⟶ S} (hs : IsPullback p q f g) (hf : LocallyOfWeaklyFiniteType f) (hg : IsAdic g)
    (hY : Y.IsLocallyStablySheafy) : IsAdic p :=
  (chartLocally_snd_and_isAdic_fst_of_isPullback
    (fun φ ↦ IsTopologicallyFiniteType φ.toRingHom)
    (fun φ ↦ IsTopologicallyFiniteType φ.toRingHom)
    (fun hφ ↦ hφ)
    (fun {A} _ _ _ _ {SA} {A₁} _ _ _ _ _ _ _ {SA₁} {C} _ _ _ _ _ _ _ {UC}
        {C₁} _ _ _ _ _ _ _ {UC₁} {φ ιA ιC φ₁} hφ hιC _ hcomm ↦ by
      have h := hιC.isTopologicallyFiniteType_toRingHom.comp hφ
      rw [← Pair.Hom.toRingHom_comp, ← hcomm, Pair.Hom.toRingHom_comp] at h
      exact h.of_comp ιA.continuous_toRingHom φ₁.continuous_toRingHom)
    (fun _ hφ hφA ↦ by
      rw [Pair.completedTensor.toRingHom_inr]
      exact CompletedTensor.isTopologicallyFiniteType_inr (hφA ▸ hφ))
    hs ((locallyOfWeaklyFiniteType_iff_chartLocally f).mp hf) hg hY).2

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
