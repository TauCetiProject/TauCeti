/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic

/-!
# Pullbacks along open immersions in `AdicSpace`

In Wedhorn's category `TauCeti.AdicSpace` of adic spaces, pullbacks along open immersions exist
unconditionally and agree with the underlying pullbacks in `PreAdicSpace`: for an open immersion
`i : X ⟶ S` and an arbitrary morphism `g : Y ⟶ S` in `AdicSpace`, the cone point of
`TauCeti.PreAdicSpace.IsOpenImmersion.pullbackConeOfLeft` maps to `Y` by an open immersion and is
therefore an adic space (`TauCeti.PreAdicSpace.isAdic_of_isOpenImmersion`), so the fully faithful
inclusion `AdicSpace ⥤ PreAdicSpace` reflects and preserves the limit cone. Consequently, open
immersions in `AdicSpace` are stable under base change.

This file also records the explicit restriction pullback squares (`isPullback_restrictPreimage` and
`isPullback_restrict_inf_of_isPullback`) used to localize global fibre-product constructions and
base-change arguments to open affinoid charts.

## Main results

* `TauCeti.AdicSpace.isPullback_restrictPreimage`: the preimage restriction `Y|_{g⁻¹(V)}` is a
  pullback of `S.ofRestrict V` along `g : Y ⟶ S`.
* `TauCeti.AdicSpace.isPullback_restrict_inf_of_isPullback`: restricting a pullback square
  `IsPullback p q f g` to `p⁻¹(U) ∩ q⁻¹(W)` gives a pullback of `(X.ofRestrict U ≫ f,
  Y.ofRestrict W ≫ g)`.
* `TauCeti.AdicSpace.isPullback_pullbackConeOfLeft`,
  `TauCeti.AdicSpace.hasPullback_of_isOpenImmersion_left`,
  `TauCeti.AdicSpace.hasPullback_of_isOpenImmersion_right`: pullbacks along open immersions exist in
  `AdicSpace`, and the inclusion into `PreAdicSpace` preserves them
  (`ι_preservesPullback_of_isOpenImmersion_left`, `ι_preservesPullback_of_isOpenImmersion_right`).
* `TauCeti.AdicSpace.isOpenImmersion_snd_of_isPullback`,
  `TauCeti.AdicSpace.isOpenImmersion_fst_of_isPullback`,
  `TauCeti.AdicSpace.isOpenImmersion_pullback_snd_of_left`,
  `TauCeti.AdicSpace.isOpenImmersion_pullback_fst_of_right`: open immersions are stable under base
  change in `AdicSpace`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.2 and §8.6.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace TauCeti.AdicSpace

universe u

variable {Z X Y S : AdicSpace.{u}}

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
    exact ⟨⟨s.snd.hom.base w, Opens.mem_map.mpr (hw ▸ (s.fst.hom.base w).property)⟩, rfl⟩
  let m : s.pt ⟶ Y.restrict ((Opens.map g.hom.base).obj V) :=
    ObjectProperty.homMk (PreAdicSpace.IsOpenImmersion.lift _ s.snd.hom hrange)
  have hm₂ : m ≫ Y.ofRestrict ((Opens.map g.hom.base).obj V) = s.snd := by
    ext1
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, ofRestrict_hom]
    exact PreAdicSpace.IsOpenImmersion.lift_fac _ _ _
  have hm₁ : m ≫ restrictPreimage g V = s.fst := by
    rw [← cancel_mono (S.ofRestrict V), Category.assoc, restrictPreimage_ofRestrict,
      ← Category.assoc, hm₂, s.condition]
  exact ⟨m, hm₁, hm₂, fun {m'} _ h₂ ↦ (cancel_mono (Y.ofRestrict _)).mp (h₂.trans hm₂.symm)⟩

/-- **Restricting a pullback square in `AdicSpace` to a product of open subspaces**: the open
subspace `Z|_{p⁻¹(U) ∩ q⁻¹(W)}` of the vertex `Z` of a pullback square `IsPullback p q f g` is a
pullback of the restricted cospan `(X|_U ⟶ S, Y|_W ⟶ S)`. -/
theorem isPullback_restrict_inf_of_isPullback
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
      ⟨Opens.mem_map.mpr (hw₁.symm ▸ (s.fst.hom.base w).property),
        Opens.mem_map.mpr (hw₂.symm ▸ (s.snd.hom.base w).property)⟩
    exact ⟨⟨l.hom.base w, hmem⟩, rfl⟩
  let m : s.pt ⟶ Z.restrict O :=
    ObjectProperty.homMk (PreAdicSpace.IsOpenImmersion.lift _ l.hom hrange)
  have hmZ : m ≫ Z.ofRestrict O = l := by
    ext1
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, ofRestrict_hom]
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

/-- **Pullback square in `AdicSpace` along an open immersion on the left**: the pre-adic pullback
cone `PreAdicSpace.IsOpenImmersion.pullbackConeOfLeft i.hom g.hom` has adic cone point and therefore
forms a pullback square in the full subcategory `AdicSpace`. -/
theorem isPullback_pullbackConeOfLeft (i : X ⟶ S) [PreAdicSpace.IsOpenImmersion i.hom]
    (g : Y ⟶ S) :
    IsPullback
      (ObjectProperty.homMk
        (X := ⟨(PreAdicSpace.IsOpenImmersion.pullbackConeOfLeft i.hom g.hom).pt,
          PreAdicSpace.isAdic_of_isOpenImmersion Y.property
            (PreAdicSpace.IsOpenImmersion.pullbackConeOfLeft i.hom g.hom).snd⟩)
        (PreAdicSpace.IsOpenImmersion.pullbackConeOfLeft i.hom g.hom).fst)
      (ObjectProperty.homMk
        (X := ⟨(PreAdicSpace.IsOpenImmersion.pullbackConeOfLeft i.hom g.hom).pt,
          PreAdicSpace.isAdic_of_isOpenImmersion Y.property
            (PreAdicSpace.IsOpenImmersion.pullbackConeOfLeft i.hom g.hom).snd⟩)
        (PreAdicSpace.IsOpenImmersion.pullbackConeOfLeft i.hom g.hom).snd)
      i g :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι PreAdicSpace.isAdic)
    (IsPullback.of_isLimit (PreAdicSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit i.hom g.hom))

/-- **Adic spaces have pullbacks along open immersions on the left.** -/
instance hasPullback_of_isOpenImmersion_left (i : X ⟶ S) [PreAdicSpace.IsOpenImmersion i.hom]
    (g : Y ⟶ S) : HasPullback i g :=
  (isPullback_pullbackConeOfLeft i g).hasPullback

/-- **Adic spaces have pullbacks along open immersions on the right.** -/
instance hasPullback_of_isOpenImmersion_right (f : X ⟶ S) (i : Y ⟶ S)
    [PreAdicSpace.IsOpenImmersion i.hom] : HasPullback f i :=
  hasPullback_symmetry i f

/-- The full subcategory inclusion `AdicSpace ⥤ PreAdicSpace` preserves pullbacks along open
immersions on the left. -/
instance ι_preservesPullback_of_isOpenImmersion_left (i : X ⟶ S)
    [PreAdicSpace.IsOpenImmersion i.hom] (g : Y ⟶ S) :
    PreservesLimit (cospan i g) (ObjectProperty.ι PreAdicSpace.isAdic) :=
  preservesLimit_of_preserves_limit_cone (isPullback_pullbackConeOfLeft i g).isLimit <|
    (isLimitMapConePullbackConeEquiv (ObjectProperty.ι PreAdicSpace.isAdic)
      (isPullback_pullbackConeOfLeft i g).w).symm
      ((PreAdicSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit i.hom g.hom).ofIsoLimit
        (PullbackCone.ext (s := PreAdicSpace.IsOpenImmersion.pullbackConeOfLeft i.hom g.hom)
          (Iso.refl _) (Category.id_comp _).symm (Category.id_comp _).symm))

/-- The full subcategory inclusion `AdicSpace ⥤ PreAdicSpace` preserves pullbacks along open
immersions on the right. -/
instance ι_preservesPullback_of_isOpenImmersion_right (f : X ⟶ S) (i : Y ⟶ S)
    [PreAdicSpace.IsOpenImmersion i.hom] :
    PreservesLimit (cospan f i) (ObjectProperty.ι PreAdicSpace.isAdic) :=
  preservesPullback_symmetry _ _ _

/-- **Base-change stability of open immersions in `AdicSpace` (left leg)**: in any pullback square
`IsPullback p q i g` in `AdicSpace` with `i.hom` an open immersion, `q.hom` is an open immersion. -/
theorem isOpenImmersion_snd_of_isPullback {p : Z ⟶ X} {q : Z ⟶ Y} {i : X ⟶ S} {g : Y ⟶ S}
    [PreAdicSpace.IsOpenImmersion i.hom] (hs : IsPullback p q i g) :
    PreAdicSpace.IsOpenImmersion q.hom := by
  let hpb := isPullback_pullbackConeOfLeft i g
  let e := hs.isoIsPullback _ _ hpb
  have he : (((ObjectProperty.ι PreAdicSpace.isAdic).mapIso e).hom ≫
      (PreAdicSpace.IsOpenImmersion.pullbackConeOfLeft i.hom g.hom).snd) = q.hom :=
    congrArg InducedCategory.Hom.hom (hs.isoIsPullback_hom_snd _ _ hpb)
  rw [← he]
  infer_instance

/-- **Base-change stability of open immersions in `AdicSpace` (right leg)**: in any pullback square
`IsPullback p q f i` in `AdicSpace` with `i.hom` an open immersion, `p.hom` is an open immersion. -/
theorem isOpenImmersion_fst_of_isPullback {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {i : Y ⟶ S}
    [PreAdicSpace.IsOpenImmersion i.hom] (hs : IsPullback p q f i) :
    PreAdicSpace.IsOpenImmersion p.hom :=
  isOpenImmersion_snd_of_isPullback hs.flip

/-- Open immersions in `AdicSpace` are stable under pullback on the left. -/
instance isOpenImmersion_pullback_snd_of_left (i : X ⟶ S) [PreAdicSpace.IsOpenImmersion i.hom]
    (g : Y ⟶ S) : PreAdicSpace.IsOpenImmersion (pullback.snd i g).hom :=
  isOpenImmersion_snd_of_isPullback (.of_hasPullback i g)

/-- Open immersions in `AdicSpace` are stable under pullback on the right. -/
instance isOpenImmersion_pullback_fst_of_right (f : X ⟶ S) (i : Y ⟶ S)
    [PreAdicSpace.IsOpenImmersion i.hom] : PreAdicSpace.IsOpenImmersion (pullback.fst f i).hom :=
  isOpenImmersion_fst_of_isPullback (.of_hasPullback f i)

end TauCeti.AdicSpace
