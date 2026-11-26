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
# Coarse-preimage comparisons and closed restrictions of thin classifying spaces

For a topological groupoid `C` with continuous source `Quiver.Total.left : Quiver.Total C → C`,
`TauCeti.thinClassifyingSpace.fatToThinClassifyingSpacePreimage` restricts
`TauCeti.fatToThinClassifyingSpace C` to the preimages of any subset `V` of the coarse quotient
`Quotient (isIsomorphicSetoid C)`. It is surjective for every subset `V` and a topological quotient
map whenever `V` is open or closed (`fatToThinClassifyingSpacePreimage_surjective`,
`isQuotientMap_fatToThinClassifyingSpacePreimage_of_isOpen`,
`isQuotientMap_fatToThinClassifyingSpacePreimage_of_isClosed`).

For an isomorphism-invariant `P : CategoryTheory.ObjectProperty C`,
`CategoryTheory.ObjectProperty.thinClassifyingSpaceClosedRestrictionHomeomorph` specializes
`CategoryTheory.ObjectProperty.thinClassifyingSpaceRestrictionHomeomorph` (in
`TauCeti.Topology.CategoryTheory.ThinClassifyingSpace`) to closed saturated full subgroupoids, and
the compatibility theorems
`thinClassifyingSpaceRestrictionHomeomorph_fatToThinClassifyingSpace`,
`thinClassifyingSpaceRestrictionHomeomorph_fatToThinClassifyingSpace_of_isOpen`, and
`thinClassifyingSpaceClosedRestrictionHomeomorph_fatToThinClassifyingSpace` identify
`fatToThinClassifyingSpacePreimage` on saturated coarse preimages with
`fatToThinClassifyingSpace P.FullSubcategory` under the fat and thin restriction homeomorphisms.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* I. Moerdijk, *Classifying spaces and classifying topoi*, LNM **1616**, Springer, 1995.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Contemp. Math. **310** (2002), 205–222.
-/

public noncomputable section

open CategoryTheory Opposite Set Simplicial SimplicialObject Topology

universe v u

namespace TauCeti

namespace thinClassifyingSpace

section CoarseSpace

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

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

section SaturatedGroupoid

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The embedding restriction homeomorphisms identify the induced map on coarse preimages with the
fat-to-thin comparison for `P.FullSubcategory`. -/
theorem thinClassifyingSpaceRestrictionHomeomorph_fatToThinClassifyingSpace
    (hfat : IsEmbedding (fatClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (hthin : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (z : fatClassifyingSpace P.FullSubcategory) :
    P.thinClassifyingSpaceRestrictionHomeomorph hs hthin
        (fatToThinClassifyingSpace P.FullSubcategory z) =
      thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
        (P.fatClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs hfat z) := by
  ext
  rw [thinClassifyingSpaceRestrictionHomeomorph_apply_val,
    thinClassifyingSpace.fatToThinClassifyingSpacePreimage_apply_val,
    fatClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_apply_val]
  simpa only [TopCat.comp_app] using (ConcreteCategory.congr_hom
    (fatClassifyingSpaceMap_comp_fatToThinClassifyingSpace P.ι P.continuous_mapTotal_ι) z).symm

/-- Conjugating the induced map on coarse preimages by the embedding restriction homeomorphisms
recovers `fatToThinClassifyingSpace P.FullSubcategory`. -/
@[simp]
theorem thinClassifyingSpaceRestrictionHomeomorph_symm_fatToThinClassifyingSpacePreimage
    (hfat : IsEmbedding (fatClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (hthin : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (z : fatClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorph hs hthin).symm
        (thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
          (P.fatClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs hfat z)) =
      fatToThinClassifyingSpace P.FullSubcategory z :=
  ((P.thinClassifyingSpaceRestrictionHomeomorph hs hthin).symm_apply_eq).2
    (P.thinClassifyingSpaceRestrictionHomeomorph_fatToThinClassifyingSpace
      hs hfat hthin z).symm

/-- The open restriction homeomorphisms identify the induced map on coarse preimages with the
fat-to-thin comparison for `P.FullSubcategory`. -/
theorem thinClassifyingSpaceRestrictionHomeomorph_fatToThinClassifyingSpace_of_isOpen
    (hP : IsOpen {x | P x}) (z : fatClassifyingSpace P.FullSubcategory) :
    P.thinClassifyingSpaceRestrictionHomeomorph hs
        (P.isOpenEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding
        (fatToThinClassifyingSpace P.FullSubcategory z) =
      thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
        (P.fatClassifyingSpaceRestrictionHomeomorph hs hP z) :=
  P.fatClassifyingSpaceRestrictionHomeomorph_eq hs hP ▸
    P.thinClassifyingSpaceRestrictionHomeomorph_fatToThinClassifyingSpace hs
      (P.isOpenEmbedding_fatClassifyingSpaceMap_ι hs hP).isEmbedding
      (P.isOpenEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding z

/-- Conjugating the induced map on coarse preimages by the open restriction homeomorphisms recovers
`fatToThinClassifyingSpace P.FullSubcategory`. -/
@[simp]
theorem thinClassifyingSpaceRestrictionHomeomorph_symm_fatToThinClassifyingSpacePreimage_of_isOpen
    (hP : IsOpen {x | P x}) (z : fatClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorph hs
        (P.isOpenEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding).symm
        (thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
          (P.fatClassifyingSpaceRestrictionHomeomorph hs hP z)) =
      fatToThinClassifyingSpace P.FullSubcategory z :=
  P.fatClassifyingSpaceRestrictionHomeomorph_eq hs hP ▸
    P.thinClassifyingSpaceRestrictionHomeomorph_symm_fatToThinClassifyingSpacePreimage hs
      (P.isOpenEmbedding_fatClassifyingSpaceMap_ι hs hP).isEmbedding
      (P.isOpenEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding z

/-- The thin classifying space of a saturated closed full subgroupoid is homeomorphic to the
corresponding coarse-map preimage in `thinClassifyingSpace C`. -/
def thinClassifyingSpaceClosedRestrictionHomeomorph (hP : IsClosed {x | P x}) :
    thinClassifyingSpace P.FullSubcategory ≃ₜ
      (thinClassifyingSpace.coarseMap hs ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  P.thinClassifyingSpaceRestrictionHomeomorph hs
    (P.isClosedEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding

@[simp↓] theorem thinClassifyingSpaceClosedRestrictionHomeomorph_apply_val (hP : IsClosed {x | P x})
    (z : thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP z).val =
      thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z :=
  P.thinClassifyingSpaceRestrictionHomeomorph_apply_val hs
    (P.isClosedEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding z

@[simp↓]
theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceClosedRestrictionHomeomorph_symm_apply
    (hP : IsClosed {x | P x})
    (z : thinClassifyingSpace.coarseMap hs ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP).symm z) = z.val :=
  P.thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorph_symm_apply hs
    (P.isClosedEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding z

/-- The closed restriction homeomorphisms identify the induced map on coarse preimages with the
fat-to-thin comparison for `P.FullSubcategory`. -/
theorem thinClassifyingSpaceClosedRestrictionHomeomorph_fatToThinClassifyingSpace
    (hP : IsClosed {x | P x}) (z : fatClassifyingSpace P.FullSubcategory) :
    P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP
        (fatToThinClassifyingSpace P.FullSubcategory z) =
      thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
        (P.fatClassifyingSpaceClosedRestrictionHomeomorph hs hP z) :=
  P.fatClassifyingSpaceClosedRestrictionHomeomorph_eq hs hP ▸
    P.thinClassifyingSpaceRestrictionHomeomorph_fatToThinClassifyingSpace hs
      (P.isClosedEmbedding_fatClassifyingSpaceMap_ι hs hP).isEmbedding
      (P.isClosedEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding z

/-- Conjugating the induced map on coarse preimages by the closed restriction homeomorphisms
recovers `fatToThinClassifyingSpace P.FullSubcategory`. -/
@[simp]
theorem thinClassifyingSpaceClosedRestrictionHomeomorph_symm_fatToThinClassifyingSpacePreimage
    (hP : IsClosed {x | P x}) (z : fatClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP).symm
        (thinClassifyingSpace.fatToThinClassifyingSpacePreimage hs _
          (P.fatClassifyingSpaceClosedRestrictionHomeomorph hs hP z)) =
      fatToThinClassifyingSpace P.FullSubcategory z :=
  P.fatClassifyingSpaceClosedRestrictionHomeomorph_eq hs hP ▸
    P.thinClassifyingSpaceRestrictionHomeomorph_symm_fatToThinClassifyingSpacePreimage hs
      (P.isClosedEmbedding_fatClassifyingSpaceMap_ι hs hP).isEmbedding
      (P.isClosedEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding z

end SaturatedGroupoid

end CategoryTheory.ObjectProperty
