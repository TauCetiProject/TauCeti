/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.CoarseSpace.Restrict
public import TauCeti.Topology.CategoryTheory.ThinClassifyingSpace
import TauCeti.Topology.Constructions.Basic

/-!
# Coarse projections and saturated restrictions of thin classifying spaces

For a topological groupoid `C` with continuous source `Quiver.Total.left : Quiver.Total C → C`,
`TauCeti.thinClassifyingSpace.coarseMap` descends `TauCeti.fatClassifyingSpace.coarseMap` along
`TauCeti.fatToThinClassifyingSpace C` to the coarse quotient `Quotient (isIsomorphicSetoid C)`,
where it is surjective and (when units are continuous) a topological quotient map
(`TauCeti.thinClassifyingSpace.isQuotientMap_coarseMap`).

For an isomorphism-invariant `P : CategoryTheory.ObjectProperty C`, inclusion of a saturated open
full subgroupoid induces an open embedding on thin classifying spaces
(`CategoryTheory.ObjectProperty.isOpenEmbedding_thinClassifyingSpaceMap_ι`), and the preimage of
the coarse image of `P` is the image of the thin classifying space of `P.FullSubcategory`
(`CategoryTheory.ObjectProperty.preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι`). Combining
this with openness (`isOpenEmbedding_thinClassifyingSpaceMap_ι`) or closedness
(`isClosedEmbedding_thinClassifyingSpaceMap_ι` in
`TauCeti.Topology.CategoryTheory.ThinClassifyingSpace`)
yields the subspace homeomorphisms
`CategoryTheory.ObjectProperty.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding`,
`CategoryTheory.ObjectProperty.thinClassifyingSpaceRestrictionHomeomorph`, and
`CategoryTheory.ObjectProperty.thinClassifyingSpaceClosedRestrictionHomeomorph`, together with
the comparison `TauCeti.thinClassifyingSpace.fatToThinClassifyingSpacePreimage` on coarse-map
preimages (which is surjective for every subset `V` and a quotient map when `V` is open or closed:
`fatToThinClassifyingSpacePreimage_surjective`,
`isQuotientMap_fatToThinClassifyingSpacePreimage_of_isOpen`,
`isQuotientMap_fatToThinClassifyingSpacePreimage_of_isClosed`) and its compatibility with the fat
and thin restriction homeomorphisms
(`thinClassifyingSpaceRestrictionHomeomorph_fatToThinClassifyingSpace`,
`thinClassifyingSpaceClosedRestrictionHomeomorph_fatToThinClassifyingSpace`).

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* I. Moerdijk, *Classifying spaces and classifying topoi*, LNM **1616**, Springer, 1995.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Contemp. Math. **310** (2002), 205–222.
-/

public noncomputable section

open CategoryTheory Opposite Set Simplicial SimplicialObject Topology
open SimplexCategory (toTop)

universe v u

namespace TauCeti

namespace thinClassifyingSpace

section CoarseSpace

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The coarse projection from `thinClassifyingSpace C` to `Quotient (isIsomorphicSetoid C)`. -/
def coarseMap : thinClassifyingSpace C ⟶ TopCat.of (Quotient (isIsomorphicSetoid C)) :=
  geometricRealization.augment (topologicalNerve.coarseAugmentation hs)

theorem coarseMap_eq_augment :
    coarseMap hs = geometricRealization.augment (topologicalNerve.coarseAugmentation hs) := (rfl)

@[simp↓] theorem coarseMap_ι (n : ℕ) (F : ComposableArrows C n) (t : toTop.{u}.obj ⦋n⦌) :
    coarseMap hs (geometricRealization.ι (topologicalNerve C) n (F, t)) =
      Quotient.mk (isIsomorphicSetoid C) (F.obj 0) :=
  (geometricRealization.augment_ι (topologicalNerve.coarseAugmentation hs) n F t).trans
    (topologicalNerve.coarseAugmentation_app_apply hs (op ⦋n⦌) F)

/-- The coarse projection of `fatClassifyingSpace C` descends along `fatToThinClassifyingSpace`. -/
@[reassoc (attr := simp)] theorem fatToThinClassifyingSpace_comp_coarseMap :
    fatToThinClassifyingSpace C ≫ coarseMap hs = fatClassifyingSpace.coarseMap hs := by
  rw [fatToThinClassifyingSpace_eq, coarseMap_eq_augment, fatClassifyingSpace.coarseMap_eq_augment]
  exact geometricRealization.fatToGeometricRealization_comp_augment _

/-- The coarse projection from `thinClassifyingSpace C` is surjective. -/
theorem coarseMap_surjective : Function.Surjective (coarseMap hs) :=
  .of_comp (g := fatToThinClassifyingSpace C) <| by
    rw [← TopCat.coe_comp, fatToThinClassifyingSpace_comp_coarseMap]
    exact fatClassifyingSpace.coarseMap_surjective hs

/-- With continuous units, `coarseMap` on `thinClassifyingSpace C` is a topological quotient map. -/
theorem isQuotientMap_coarseMap (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :
    IsQuotientMap (coarseMap hs) :=
  IsQuotientMap.of_comp (fatToThinClassifyingSpace C).hom.continuous (coarseMap hs).hom.continuous
    (by rw [← TopCat.coe_comp, fatToThinClassifyingSpace_comp_coarseMap]
        exact fatClassifyingSpace.isQuotientMap_coarseMap hs hu)

/-- The continuous map induced by `fatToThinClassifyingSpace C` on the preimages of a subset `V`
of the coarse quotient. -/
def fatToThinClassifyingSpacePreimage (V : Set (Quotient (isIsomorphicSetoid C))) :
    C(fatClassifyingSpace.coarseMap hs ⁻¹' V, coarseMap hs ⁻¹' V) :=
  ⟨Set.MapsTo.restrict (fatToThinClassifyingSpace C) _ _ fun z hz ↦ by
    change coarseMap hs (fatToThinClassifyingSpace C z) ∈ V
    rw [← TopCat.comp_app, fatToThinClassifyingSpace_comp_coarseMap]
    exact hz,
    (fatToThinClassifyingSpace C).hom.continuous.restrict _⟩

/-- Evaluating `fatToThinClassifyingSpacePreimage` on a subtype element applies
`fatToThinClassifyingSpace C` to its underlying point. -/
@[simp]
theorem fatToThinClassifyingSpacePreimage_apply_val
    (V : Set (Quotient (isIsomorphicSetoid C)))
    (z : fatClassifyingSpace.coarseMap hs ⁻¹' V) :
    (fatToThinClassifyingSpacePreimage hs V z).val = fatToThinClassifyingSpace C z.val := (rfl)

/-- For every subset `V` of the coarse quotient, `fatToThinClassifyingSpacePreimage hs V` is
surjective. -/
theorem fatToThinClassifyingSpacePreimage_surjective
    (V : Set (Quotient (isIsomorphicSetoid C))) :
    Function.Surjective (fatToThinClassifyingSpacePreimage hs V) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := fatToThinClassifyingSpace_surjective C y
  refine ⟨⟨x, ?_⟩, Subtype.ext rfl⟩
  change fatClassifyingSpace.coarseMap hs x ∈ V
  rw [← fatToThinClassifyingSpace_comp_coarseMap hs, TopCat.comp_app]
  exact hy

/-- For an open subset `V` of the coarse quotient, `fatToThinClassifyingSpacePreimage hs V` is a
topological quotient map. -/
theorem isQuotientMap_fatToThinClassifyingSpacePreimage_of_isOpen
    {V : Set (Quotient (isIsomorphicSetoid C))} (hV : IsOpen V) :
    IsQuotientMap (fatToThinClassifyingSpacePreimage hs V) := by
  have hpre : fatClassifyingSpace.coarseMap hs ⁻¹' V =
      fatToThinClassifyingSpace C ⁻¹' (coarseMap hs ⁻¹' V) := by
    rw [← Set.preimage_comp, ← TopCat.coe_comp, fatToThinClassifyingSpace_comp_coarseMap]
  have hq :
      IsQuotientMap ((coarseMap hs ⁻¹' V).restrictPreimage (fatToThinClassifyingSpace C)) :=
    (isQuotientMap_fatToThinClassifyingSpace C).restrictPreimage_isOpen
      (hV.preimage (coarseMap hs).hom.continuous)
  exact hq.comp (Homeomorph.setCongr hpre).isQuotientMap

/-- For a closed subset `V` of the coarse quotient, `fatToThinClassifyingSpacePreimage hs V` is a
topological quotient map. -/
theorem isQuotientMap_fatToThinClassifyingSpacePreimage_of_isClosed
    {V : Set (Quotient (isIsomorphicSetoid C))} (hV : IsClosed V) :
    IsQuotientMap (fatToThinClassifyingSpacePreimage hs V) := by
  refine Topology.IsQuotientMap.of_comp_eq_comp (isQuotientMap_fatToThinClassifyingSpace C)
    (fatToThinClassifyingSpacePreimage hs V).continuous
    (fatToThinClassifyingSpacePreimage_surjective hs V)
    ((hV.preimage (fatClassifyingSpace.coarseMap hs).hom.continuous)
      |>.isClosedEmbedding_subtypeVal.isClosedMap)
    continuous_subtypeVal Subtype.val_injective (funext fun _ ↦ rfl) fun z hz ↦ ?_
  obtain ⟨⟨y, hy⟩, hyz⟩ := hz
  refine ⟨⟨z, ?_⟩, rfl⟩
  change fatClassifyingSpace.coarseMap hs z ∈ V
  rw [← fatToThinClassifyingSpace_comp_coarseMap hs, TopCat.comp_app]
  exact hyz ▸ hy

end CoarseSpace

end thinClassifyingSpace

end TauCeti

namespace CategoryTheory.ObjectProperty

open TauCeti

/-- For a groupoid with continuous source `Quiver.Total.left : Quiver.Total C → C`, the inclusion
of a saturated open full subgroupoid induces an open embedding on thin classifying spaces. -/
theorem isOpenEmbedding_thinClassifyingSpaceMap_ι {C : Type u} [Category.{v} C]
    [TopologicalSpace (Quiver.Total C)] (P : ObjectProperty C) [IsGroupoid C] [TopologicalSpace C]
    [P.IsClosedUnderIsomorphisms]
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C)) (hP : IsOpen {x | P x}) :
    IsOpenEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) := by
  rw [thinClassifyingSpaceMap_eq]
  exact geometricRealization.isOpenEmbedding_map
    (fun n ↦ by
      rw [coe_topologicalNerveMap_app]; exact P.isOpenEmbedding_mapComposableArrows_ι hs hP n)
    fun m n f (F : ComposableArrows C n) hF ↦ by
      rw [topologicalNerve_map_apply, coe_topologicalNerveMap_app] at hF
      have h0 : P (F.obj (f.toOrderHom 0)) := by
        rw [← nerve.map_obj f F 0]
        exact (P.range_mapComposableArrows_ι_of_isClosedUnderIsomorphisms m).subset hF
      rw [coe_topologicalNerveMap_app]
      exact (P.range_mapComposableArrows_ι_of_isClosedUnderIsomorphisms n).superset
        (P.prop_of_iso (asIso (F.map (homOfLE (Fin.zero_le _)))).symm h0)

section SaturatedGroupoid

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The preimage of a saturated coarse subset in `thinClassifyingSpace C` is the image of the thin
classifying space of the corresponding full restriction. -/
theorem preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι :
    thinClassifyingSpace.coarseMap hs ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x}) =
      range (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) := by
  rw [thinClassifyingSpace.coarseMap_eq_augment, thinClassifyingSpaceMap_eq]
  exact geometricRealization.preimage_augment_eq_range_map
    (ε := topologicalNerve.coarseAugmentation hs)
    (fun n ↦ P.range_topologicalNerveMap_ι hs (op ⦋n⦌))

/-- Whenever the inclusion of a saturated full subgroupoid induces a topological embedding on thin
classifying spaces (for instance via `isOpenEmbedding_thinClassifyingSpaceMap_ι` or
`isClosedEmbedding_thinClassifyingSpaceMap_ι`), its thin classifying space is homeomorphic to the
corresponding coarse-map preimage with its subspace topology. -/
def thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding
    (h : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι)) :
    thinClassifyingSpace P.FullSubcategory ≃ₜ
      (thinClassifyingSpace.coarseMap hs ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  h.toHomeomorph.trans
    (Homeomorph.setCongr (P.preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι hs).symm)

@[simp↓] theorem thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_apply_val
    (h : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (z : thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs h z).val =
      thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z := (rfl)

@[simp↓]
theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_symm_apply
    (h : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (z : thinClassifyingSpace.coarseMap hs ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs h).symm z) = z.val :=
  congrArg Subtype.val
    ((P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs h).apply_symm_apply z)

/-- The embedding restriction homeomorphisms identify the induced map on coarse preimages with the
fat-to-thin comparison for `P.FullSubcategory`. -/
theorem thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_fatToThinClassifyingSpace
    (hfat : IsEmbedding (fatClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (hthin : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (z : fatClassifyingSpace P.FullSubcategory) :
    P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs hthin
        (fatToThinClassifyingSpace P.FullSubcategory z) =
      thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
        (P.fatClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs hfat z) := by
  ext
  rw [thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_apply_val,
    thinClassifyingSpace.fatToThinClassifyingSpacePreimage_apply_val,
    fatClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_apply_val]
  simpa only [TopCat.comp_app] using (ConcreteCategory.congr_hom
    (fatClassifyingSpaceMap_comp_fatToThinClassifyingSpace P.ι P.continuous_mapTotal_ι) z).symm

/-- Conjugating the induced map on coarse preimages by the embedding restriction homeomorphisms
recovers `fatToThinClassifyingSpace P.FullSubcategory`. -/
@[simp]
theorem
    thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_symm_fatToThinClassifyingSpacePreimage
    (hfat : IsEmbedding (fatClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (hthin : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (z : fatClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs hthin).symm
        (thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
          (P.fatClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs hfat z)) =
      fatToThinClassifyingSpace P.FullSubcategory z :=
  ((P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs hthin).symm_apply_eq).2
    (P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_fatToThinClassifyingSpace
      hs hfat hthin z).symm

/-- The thin classifying space of a saturated open full subgroupoid is homeomorphic to the
corresponding coarse-map preimage in `thinClassifyingSpace C`. -/
def thinClassifyingSpaceRestrictionHomeomorph (hP : IsOpen {x | P x}) :
    thinClassifyingSpace P.FullSubcategory ≃ₜ
      (thinClassifyingSpace.coarseMap hs ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs
    (P.isOpenEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding

@[simp↓] theorem thinClassifyingSpaceRestrictionHomeomorph_apply_val (hP : IsOpen {x | P x})
    (z : thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorph hs hP z).val =
      thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z := (rfl)

@[simp↓] theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorph_symm_apply
    (hP : IsOpen {x | P x})
    (z : thinClassifyingSpace.coarseMap hs ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceRestrictionHomeomorph hs hP).symm z) = z.val :=
  P.thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_symm_apply
    hs (P.isOpenEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding z

/-- The open restriction homeomorphisms identify the induced map on coarse preimages with the
fat-to-thin comparison for `P.FullSubcategory`. -/
theorem thinClassifyingSpaceRestrictionHomeomorph_fatToThinClassifyingSpace
    (hP : IsOpen {x | P x}) (z : fatClassifyingSpace P.FullSubcategory) :
    P.thinClassifyingSpaceRestrictionHomeomorph hs hP
        (fatToThinClassifyingSpace P.FullSubcategory z) =
      thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
        (P.fatClassifyingSpaceRestrictionHomeomorph hs hP z) := by
  ext
  rw [thinClassifyingSpaceRestrictionHomeomorph_apply_val,
    thinClassifyingSpace.fatToThinClassifyingSpacePreimage_apply_val,
    fatClassifyingSpaceRestrictionHomeomorph_apply_val]
  simpa only [TopCat.comp_app] using (ConcreteCategory.congr_hom
    (fatClassifyingSpaceMap_comp_fatToThinClassifyingSpace P.ι P.continuous_mapTotal_ι) z).symm

/-- Conjugating the induced map on coarse preimages by the open restriction homeomorphisms recovers
`fatToThinClassifyingSpace P.FullSubcategory`. -/
@[simp]
theorem thinClassifyingSpaceRestrictionHomeomorph_symm_fatToThinClassifyingSpacePreimage
    (hP : IsOpen {x | P x}) (z : fatClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorph hs hP).symm
        (thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
          (P.fatClassifyingSpaceRestrictionHomeomorph hs hP z)) =
      fatToThinClassifyingSpace P.FullSubcategory z :=
  ((P.thinClassifyingSpaceRestrictionHomeomorph hs hP).symm_apply_eq).2
    (P.thinClassifyingSpaceRestrictionHomeomorph_fatToThinClassifyingSpace hs hP z).symm

/-- The thin classifying space of a saturated closed full subgroupoid is homeomorphic to the
corresponding coarse-map preimage in `thinClassifyingSpace C`. -/
def thinClassifyingSpaceClosedRestrictionHomeomorph (hP : IsClosed {x | P x}) :
    thinClassifyingSpace P.FullSubcategory ≃ₜ
      (thinClassifyingSpace.coarseMap hs ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs
    (P.isClosedEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding

@[simp↓] theorem thinClassifyingSpaceClosedRestrictionHomeomorph_apply_val (hP : IsClosed {x | P x})
    (z : thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP z).val =
      thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z := (rfl)

@[simp↓]
theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceClosedRestrictionHomeomorph_symm_apply
    (hP : IsClosed {x | P x})
    (z : thinClassifyingSpace.coarseMap hs ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP).symm z) = z.val :=
  P.thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_symm_apply
    hs (P.isClosedEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding z

/-- The closed restriction homeomorphisms identify the induced map on coarse preimages with the
fat-to-thin comparison for `P.FullSubcategory`. -/
theorem thinClassifyingSpaceClosedRestrictionHomeomorph_fatToThinClassifyingSpace
    (hP : IsClosed {x | P x}) (z : fatClassifyingSpace P.FullSubcategory) :
    P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP
        (fatToThinClassifyingSpace P.FullSubcategory z) =
      thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
        (P.fatClassifyingSpaceClosedRestrictionHomeomorph hs hP z) := by
  ext
  rw [thinClassifyingSpaceClosedRestrictionHomeomorph_apply_val,
    thinClassifyingSpace.fatToThinClassifyingSpacePreimage_apply_val,
    fatClassifyingSpaceClosedRestrictionHomeomorph_apply_val]
  simpa only [TopCat.comp_app] using (ConcreteCategory.congr_hom
    (fatClassifyingSpaceMap_comp_fatToThinClassifyingSpace P.ι P.continuous_mapTotal_ι) z).symm

/-- Conjugating the induced map on coarse preimages by the closed restriction homeomorphisms
recovers `fatToThinClassifyingSpace P.FullSubcategory`. -/
@[simp]
theorem thinClassifyingSpaceClosedRestrictionHomeomorph_symm_fatToThinClassifyingSpacePreimage
    (hP : IsClosed {x | P x}) (z : fatClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP).symm
        (thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
          (P.fatClassifyingSpaceClosedRestrictionHomeomorph hs hP z)) =
      fatToThinClassifyingSpace P.FullSubcategory z :=
  ((P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP).symm_apply_eq).2
    (P.thinClassifyingSpaceClosedRestrictionHomeomorph_fatToThinClassifyingSpace hs hP z).symm

end SaturatedGroupoid

end CategoryTheory.ObjectProperty
